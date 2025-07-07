import os
import asyncio
import json
import re
import base64
import logging
import random
import string
import math
import socket
from pathlib import Path
from typing import List, Dict, Set, Optional, Any, Tuple, Coroutine
from urllib.parse import urlparse, parse_qs, unquote
import ipaddress
from collections import Counter

import httpx
import aiofiles
import jdatetime
try:
    import geoip2.database
except ImportError:
    print("Error: 'geoip2' library not found. Please run: pip install geoip2")
    exit(1)

try:
    from rich.console import Console
    from rich.progress import Progress, BarColumn, TextColumn, TimeRemainingColumn, SpinnerColumn
    from rich.table import Table
except ImportError:
    print("Error: 'rich' library not found. Please run: pip install rich")
    exit(1)

from bs4 import BeautifulSoup
from datetime import datetime, timezone, timedelta
from pydantic import BaseModel, Field, model_validator, ValidationError

class AppConfig:
    BASE_DIR = Path(__file__).parent
    DATA_DIR = BASE_DIR / "data"
    OUTPUT_DIR = BASE_DIR / "sub"

    # ИЗМЕНЕНО: Добавлена новая директория для "избранных" провайдеров
    DIRS = {
        "protocols": OUTPUT_DIR / "protocols",
        "datacenters": OUTPUT_DIR / "datacenters",
        "custom_datacenters": OUTPUT_DIR / "custom_datacenters",
    }

    LAST_UPDATE_FILE = DATA_DIR / "last_update.log"
    GEOIP_DB_FILE = DATA_DIR / "GeoLite2-Country.mmdb"
    GEOIP_ASN_DB_FILE = DATA_DIR / "GeoLite2-ASN.mmdb"

    REMOTE_TELEGRAM_CHANNELS_URL = "https://raw.githubusercontent.com/LexterS999/configs-collector-v2ray/refs/heads/main/data/telegram-channel.json"
    REMOTE_SUBSCRIPTION_LINKS_URL = "https://raw.githubusercontent.com/LexterS999/configs-collector-v2ray/refs/heads/main/data/subscription_links.json"
    GEOIP_DB_URL = "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-Country.mmdb"
    GEOIP_ASN_DB_URL = "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-ASN.mmdb"

    # Этот список теперь используется для КЛАССИФИКАЦИИ, а не для фильтрации
    DESIRED_ASN_KEYWORDS: Set[str] = {
        "aeza", "hetzner", "digitalocean", "g-core", "pq hosting", "global connectivity"
    }

    HTTP_TIMEOUT = 25.0
    HTTP_MAX_REDIRECTS = 5
    HTTP_HEADERS = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:109.0) Gecko/20100101 Firefox/115.0"}
    MAX_CONCURRENT_REQUESTS = 20

    TELEGRAM_BASE_URL = "https://t.me/s/{}"
    TELEGRAM_MESSAGE_LIMIT = 50
    TELEGRAM_IGNORE_LAST_UPDATE = True
    MAX_CONFIGS_PER_CHANNEL = 30 

    ENABLE_SUBSCRIPTION_FETCHING = True
    ENABLE_IP_DEDUPLICATION = True
    
    ENABLE_CONNECTIVITY_TEST = True 
    CONNECTIVITY_TEST_TIMEOUT = 2.0
    CONNECTIVITY_TEST_CONCURRENCY = 40
    
CONFIG = AppConfig()
console = Console()

def setup_logger():
    logging.basicConfig(level=logging.INFO, format='%(message)s', datefmt="[%X]", handlers=[])
    logging.getLogger("httpx").setLevel(logging.WARNING)
    logging.getLogger("geoip2").setLevel(logging.WARNING)
    return logging.getLogger("V2RayCollector")

logger = setup_logger()

class V2RayCollectorException(Exception): pass
class ParsingError(V2RayCollectorException): pass
class NetworkError(V2RayCollectorException): pass

# ... (остальные классы и функции до ConfigProcessor без изменений) ...
COUNTRY_CODE_TO_FLAG = {
    'AD': '🇦🇩', 'AE': '🇦🇪', 'AF': '🇦🇫', 'AG': '🇦🇬', 'AI': '🇦🇮', 'AL': '🇦🇱', 'AM': '🇦🇲', 'AO': '🇦🇴', 'AQ': '🇦🇶', 'AR': '🇦🇷', 'AS': '🇦🇸', 'AT': '🇦🇹', 'AU': '🇦🇺', 'AW': '🇦🇼', 'AX': '🇦🇽', 'AZ': '🇦🇿', 'BA': '🇧🇦', 'BB': '🇧🇧',
    'BD': '🇧🇩', 'BE': '🇧🇪', 'BF': '🇧🇫', 'BG': '🇧🇬', 'BH': '🇧🇭', 'BI': '🇧🇮', 'BJ': '🇧🇯', 'BL': '🇧🇱', 'BM': '🇧🇲', 'BN': '🇧🇳', 'BO': '🇧🇴', 'BR': '🇧🇷', 'BS': '🇧🇸', 'BT': '🇧🇹', 'BW': '🇧🇼', 'BY': '🇧🇾', 'BZ': '🇧🇿', 'CA': '🇨🇦',
    'CC': '🇨🇨', 'CD': '🇨🇩', 'CF': '🇨🇫', 'CG': '🇨🇬', 'CH': '🇨🇭', 'CI': '🇨🇮', 'CK': '🇨🇰', 'CL': '🇨🇱', 'CM': '🇨🇲', 'CN': '🇨🇳', 'CO': '🇨🇴', 'CR': '🇨🇷', 'CU': '🇨🇺', 'CV': '🇨🇻', 'CW': '🇨🇼', 'CX': '🇨🇽', 'CY': '🇨🇾', 'CZ': '🇨🇿',
    'DE': '🇩🇪', 'DJ': '🇩🇯', 'DK': '🇩🇰', 'DM': '🇩🇲', 'DO': '🇩🇴', 'DZ': '🇩🇿', 'EC': '🇪🇨', 'EE': '🇪🇪', 'EG': '🇪🇬', 'ER': '🇪🇷', 'ES': '🇪🇸', 'ET': '🇪🇹', 'FI': '🇫🇮', 'FJ': '🇫🇯', 'FK': '🇫🇰', 'FM': '🇫🇲', 'FO': '🇫🇴', 'FR': '🇫🇷',
    'GA': '🇬🇦', 'GB': '🇬🇧', 'GD': '🇬🇩', 'GE': '🇬🇪', 'GF': '🇬🇫', 'GG': '🇬🇬', 'GH': '🇬🇭', 'GI': '🇬🇮', 'GL': '🇬🇱', 'GM': '🇬🇲', 'GN': '🇬🇳', 'GP': '🇬🇵', 'GQ': '🇬🇶', 'GR': '🇬🇷', 'GS': '🇬🇸', 'GT': '🇬🇹', 'GU': '🇬🇺', 'GW': '🇬🇼',
    'GY': '🇬🇾', 'HK': '🇭🇰', 'HN': '🇭🇳', 'HR': '🇭🇷', 'HT': '🇭🇹', 'HU': '🇭🇺', 'ID': '🇮🇩', 'IE': '🇮🇪', 'IL': '🇮🇱', 'IM': '🇮🇲', 'IN': '🇮🇳', 'IO': '🇮🇴', 'IQ': '🇮🇶', 'IR': '🇮🇷', 'IS': '🇮🇸', 'IT': '🇮🇹', 'JE': '🇯🇪', 'JM': '🇯🇲',
    'JO': '🇯🇴', 'JP': '🇯🇵', 'KE': '🇰🇪', 'KG': '🇰🇬', 'KH': '🇰🇭', 'KI': '🇰🇮', 'KM': '🇰🇲', 'KN': '🇰🇳', 'KP': '🇰🇵', 'KR': '🇰🇷', 'KW': '🇰🇼', 'KY': '🇰🇾', 'KZ': '🇰🇿', 'LA': '🇱🇦', 'LB': '🇱🇧', 'LC': '🇱🇨', 'LI': '🇱🇮', 'LK': '🇱🇰',
    'LR': '🇱🇷', 'LS': '🇱🇸', 'LT': '🇱🇹', 'LU': '🇱🇺', 'LV': '🇱🇻', 'LY': '🇱🇾', 'MA': '🇲🇦', 'MC': '🇲🇨', 'MD': '🇲🇩', 'ME': '🇲🇪', 'MF': '🇲🇫', 'MG': '🇲🇬', 'MH': '🇲🇭', 'MK': '🇲🇰', 'ML': '🇲🇱', 'MM': '🇲🇲', 'MN': '🇲🇳', 'MO': '🇲🇴',
    'MP': '🇲🇵', 'MQ': '🇲🇶', 'MR': '🇲🇷', 'MS': '🇲🇸', 'MT': '🇲🇹', 'MU': '🇲🇺', 'MV': '🇲🇻', 'MW': '🇲🇼', 'MX': '🇲🇽', 'MY': '🇲🇾', 'MZ': '🇲🇿', 'NA': '🇳🇦', 'NC': '🇳🇨', 'NE': '🇳🇪', 'NF': '🇳🇫', 'NG': '🇳🇬', 'NI': '🇳🇮', 'NL': '🇳🇱',
    'NO': '🇳🇴', 'NP': '🇳🇵', 'NR': '🇳🇷', 'NU': '🇳🇺', 'NZ': '🇳🇿', 'OM': '🇴🇲', 'PA': '🇵🇦', 'PE': '🇵🇪', 'PF': '🇵🇫', 'PG': '🇵🇬', 'PH': '🇵🇭', 'PK': '🇵🇰', 'PL': '🇵🇱', 'PM': '🇵🇲', 'PN': '🇵🇳', 'PR': '🇵🇷', 'PS': '🇵🇸', 'PT': '🇵🇹',
    'PW': '🇵🇼', 'PY': '🇵🇾', 'QA': '🇶🇦', 'RE': '🇷🇪', 'RO': '🇷🇴', 'RS': '🇷🇸', 'RU': '🇷🇺', 'RW': '🇷🇼', 'SA': '🇸🇦', 'SB': '🇸🇧', 'SC': '🇸🇨', 'SD': '🇸🇩', 'SE': '🇸🇪', 'SG': '🇸🇬', 'SH': '🇸🇭', 'SI': '🇸🇮', 'SJ': '🇸🇯', 'SK': '🇸🇰',
    'SL': '🇸🇱', 'SM': '🇸🇲', 'SN': '🇸🇳', 'SO': '🇸🇴', 'SR': '🇸🇷', 'SS': '🇸🇸', 'ST': '🇸🇹', 'SV': '🇸🇻', 'SX': '🇸🇽', 'SY': '🇸🇾', 'SZ': '🇸🇿', 'TC': '🇹🇨', 'TD': '🇹🇩', 'TF': '🇹🇫', 'TG': '🇹🇬', 'TH': '🇹🇭', 'TJ': '🇹🇯', 'TK': '🇹🇰',
    'TL': '🇹🇱', 'TM': '🇹🇲', 'TN': '🇹🇳', 'TO': '🇹🇴', 'TR': '🇹🇷', 'TT': '🇹🇹', 'TV': '🇹🇻', 'TW': '🇹🇼', 'TZ': '🇹🇿', 'UA': '🇺🇦', 'UG': '🇺🇬', 'US': '🇺🇸', 'UY': '🇺🇾', 'UZ': '🇺🇿', 'VA': '🇻🇦', 'VC': '🇻🇨', 'VE': '🇻🇪', 'VG': '🇻🇬',
    'VI': '🇻🇮', 'VN': '🇻🇳', 'VU': '🇻🇺', 'WF': '🇼🇫', 'WS': '🇼🇸', 'YE': '🇾🇪', 'YT': '🇾🇹', 'ZA': '🇿🇦', 'ZM': '🇿🇲', 'ZW': '🇿🇼', 'XX': '🏳️'
}

def is_valid_base64(s: str) -> bool:
    try:
        s_padded = s + '=' * (-len(s) % 4)
        return base64.b64encode(base64.b64decode(s_padded)).decode('utf-8') == s_padded
    except (ValueError, TypeError):
        return False

def get_iran_timezone():
    return timezone(timedelta(hours=3, minutes=30))

def is_ip_address(address: str) -> bool:
    try:
        ipaddress.ip_address(address)
        return True
    except ValueError:
        return False

class BaseConfig(BaseModel):
    model_config = {'str_strip_whitespace': True}
    protocol: str
    host: str
    port: int
    uuid: str
    remarks: str = "N/A"
    network: str = 'tcp'
    security: str = 'none'
    path: Optional[str] = None
    sni: Optional[str] = None
    fingerprint: Optional[str] = None
    country: Optional[str] = Field("XX", exclude=True)
    source_type: str = Field("unknown", exclude=True)
    ping: Optional[int] = Field(None, exclude=True)
    asn_org: Optional[str] = Field(None, exclude=True)

    def get_deduplication_key(self) -> str:
        return f"{self.protocol}:{self.host}:{self.port}:{self.uuid}"

    def to_uri(self) -> str:
        raise NotImplementedError

class VmessConfig(BaseConfig):
    protocol: str = 'vmess'
    source_type: str = 'vmess'
    ps: str
    add: str
    v: Any = "2"
    aid: int = 0
    scy: str = 'auto'
    net: str
    type: str = 'none'
    tls: str = ''

    @model_validator(mode='before')
    def map_fields(cls, values):
        values['remarks'] = values.get('ps', 'N/A')
        values['host'] = values.get('add', '')
        values['uuid'] = values.get('id', '')
        values['network'] = values.get('net', 'tcp')
        values['security'] = values.get('tls') or 'none'
        values['v'] = str(values.get('v', '2'))
        return values

    def to_uri(self) -> str:
        vmess_data = {"v": self.v, "ps": self.remarks, "add": self.host, "port": self.port, "id": self.uuid, "aid": self.aid, "scy": self.scy, "net": self.network, "type": self.type, "host": self.sni, "path": self.path, "tls": self.security if self.security != 'none' else '', "sni": self.sni}
        vmess_data_clean = {k: v for k, v in vmess_data.items() if v is not None and v != ""}
        json_str = json.dumps(vmess_data_clean, separators=(',', ':'))
        encoded = base64.b64encode(json_str.encode('utf-8')).decode('utf-8').rstrip("=")
        return f"vmess://{encoded}"

class VlessConfig(BaseConfig):
    protocol: str = 'vless'
    flow: Optional[str] = None
    pbk: Optional[str] = None
    sid: Optional[str] = None

    def to_uri(self) -> str:
        params = {'type': self.network, 'security': self.security, 'path': self.path, 'sni': self.sni, 'fp': self.fingerprint, 'flow': self.flow, 'pbk': self.pbk, 'sid': self.sid}
        query_string = '&'.join([f"{k}={v}" for k, v in params.items() if v is not None and v != ""])
        remarks_encoded = f"#{unquote(self.remarks)}"
        return f"vless://{self.uuid}@{self.host}:{self.port}?{query_string}{remarks_encoded}"

class TrojanConfig(BaseConfig):
    protocol: str = 'trojan'
    source_type: str = 'trojan'

    def to_uri(self) -> str:
        params = {'sni': self.sni, 'peer': self.sni, 'security': self.security}
        query_string = '&'.join([f"{k}={v}" for k, v in params.items() if v is not None])
        remarks_encoded = f"#{unquote(self.remarks)}"
        return f"trojan://{self.uuid}@{self.host}:{self.port}?{query_string}{remarks_encoded}"

class ShadowsocksConfig(BaseConfig):
    protocol: str = 'shadowsocks'
    source_type: str = 'shadowsocks'
    method: str

    @model_validator(mode='before')
    def map_fields(cls, values):
        values['uuid'] = values.get('password', '')
        return values

    def to_uri(self) -> str:
        user_info = f"{self.method}:{self.uuid}"
        encoded_user_info = base64.b64encode(user_info.encode('utf-8')).decode('utf-8').rstrip('=')
        remarks_encoded = f"#{unquote(self.remarks)}"
        return f"ss://{encoded_user_info}@{self.host}:{self.port}{remarks_encoded}"

class AsyncHttpClient:
    _client: Optional[httpx.AsyncClient] = None

    @classmethod
    async def get_client(cls) -> httpx.AsyncClient:
        if cls._client is None or cls._client.is_closed:
            limits = httpx.Limits(max_connections=CONFIG.MAX_CONCURRENT_REQUESTS, max_keepalive_connections=20)
            cls._client = httpx.AsyncClient(headers=CONFIG.HTTP_HEADERS, timeout=CONFIG.HTTP_TIMEOUT, max_redirects=CONFIG.HTTP_MAX_REDIRECTS, http2=True, follow_redirects=True, limits=limits)
        return cls._client

    @classmethod
    async def close(cls):
        if cls._client and not cls._client.is_closed:
            await cls._client.aclose()
            cls._client = None

    @classmethod
    async def get(cls, url: str) -> Tuple[int, str]:
        client = await cls.get_client()
        try:
            response = await client.get(url)
            response.raise_for_status()
            return response.status_code, response.text
        except httpx.RequestError as e:
            raise NetworkError(f"Failed to fetch {url}") from e
        except httpx.HTTPStatusError as e:
            return e.response.status_code, e.response.text

class V2RayParser:
    @staticmethod
    def parse(uri: str, source_type: str = "unknown") -> Optional[BaseConfig]:
        uri = uri.strip()
        if not uri:
            return None
            
        parsed_config: Optional[BaseConfig] = None
        try:
            if uri.startswith("vmess://"): parsed_config = V2RayParser._parse_vmess(uri)
            elif uri.startswith("vless://"): parsed_config = V2RayParser._parse_vless(uri)
            elif uri.startswith("trojan://"): parsed_config = V2RayParser._parse_trojan(uri)
            elif uri.startswith("ss://"): parsed_config = V2RayParser._parse_shadowsocks(uri)

            if parsed_config:
                parsed_config.source_type = source_type
            return parsed_config
        except (ValidationError, ParsingError):
            return None
        except Exception:
            return None

    @staticmethod
    def _parse_vmess(uri: str) -> Optional[VmessConfig]:
        b64_data = uri[len("vmess://"):]
        if not is_valid_base64(b64_data): return None
        data = json.loads(base64.b64decode(b64_data + '==').decode('utf-8'))
        return VmessConfig(**data)

    @staticmethod
    def _parse_vless(uri: str) -> Optional[VlessConfig]:
        try:
            parsed_url = urlparse(uri)
            if not parsed_url.hostname or not parsed_url.port:
                raise ParsingError(f"Missing hostname or port in VLESS URI.")

            params = parse_qs(parsed_url.query)
            
            net_type = params.get('type', ['tcp'])[0]

            return VlessConfig(
                uuid=parsed_url.username, 
                host=parsed_url.hostname, 
                port=parsed_url.port, 
                remarks=unquote(parsed_url.fragment) if parsed_url.fragment else f"{parsed_url.hostname}:{parsed_url.port}",
                network=net_type, 
                security=params.get('security', ['none'])[0], 
                path=unquote(params.get('path', [None])[0]) if params.get('path') else None, 
                sni=params.get('sni', [None])[0], 
                fingerprint=params.get('fp', [None])[0], 
                flow=params.get('flow', [None])[0], 
                pbk=params.get('pbk', [None])[0], 
                sid=params.get('sid', [None])[0]
            )
        except (ValueError, TypeError, AttributeError) as e:
            raise ParsingError(f"Could not parse VLESS link correctly: {uri[:60]}") from e

    @staticmethod
    def _parse_trojan(uri: str) -> Optional[TrojanConfig]:
        parsed_url = urlparse(uri)
        if not parsed_url.hostname or not parsed_url.port:
            raise ParsingError(f"Missing hostname or port in Trojan URI.")
        params = parse_qs(parsed_url.query)
        return TrojanConfig(uuid=parsed_url.username, host=parsed_url.hostname, port=parsed_url.port, remarks=unquote(parsed_url.fragment) if parsed_url.fragment else f"{parsed_url.hostname}:{parsed_url.port}", security=params.get('security', ['tls'])[0], sni=params.get('sni', [None])[0], network='tcp')

    @staticmethod
    def _parse_shadowsocks(uri: str) -> Optional[ShadowsocksConfig]:
        try:
            main_part, remarks_part = (uri[len("ss://"):].split('#', 1) + [''])[:2]
            remarks = unquote(remarks_part) if remarks_part else ''
            
            if '@' not in main_part:
                raise ParsingError("Invalid SS URI format: missing '@'.")
                
            user_info_part, host_port_part = main_part.split('@', 1)
            decoded_user_info = base64.b64decode(user_info_part + '==').decode('utf-8')
            
            if ':' not in decoded_user_info or ':' not in host_port_part:
                raise ParsingError("Invalid SS URI format: missing method/password or host/port separator.")
                
            method, password = decoded_user_info.split(':', 1)
            host, port_str = host_port_part.rsplit(':', 1)
            
            if host.startswith('[') and host.endswith(']'): host = host[1:-1]
            if not remarks: remarks = f"{host}:{port_str}"
            
            return ShadowsocksConfig(host=host, port=int(port_str), remarks=remarks, method=method, password=password)
        except Exception as e:
            raise ParsingError(f"Could not parse Shadowsocks link: {uri[:60]}") from e

class RawConfigCollector:
    PATTERNS = {"ss": r"(?<![\w-])(ss://[^\s<>#]+)", "trojan": r"(?<![\w-])(trojan://[^\s<>#]+)", "vmess": r"(?<![\w-])(vmess://[^\s<>#]+)", "vless": r"(?<![\w-])(vless://(?:(?!=reality)[^\s<>#])+(?=[\s<>#]))", "reality": r"(?<![\w-])(vless://[^\s<>#]+?security=reality[^\s<>#]*)"}

    @classmethod
    def find_all(cls, text_content: str) -> Dict[str, List[str]]:
        all_matches = {}
        for name, pattern in cls.PATTERNS.items():
            matches = re.findall(pattern, text_content, re.IGNORECASE)
            cleaned_matches = [re.sub(r"#[^#]*$", "", m) for m in matches if "…" not in m]
            if cleaned_matches:
                all_matches[name] = cleaned_matches
        return all_matches

class TelegramScraper:
    def __init__(self, channels: List[str], since_datetime: datetime):
        self.channels, self.since_datetime, self.iran_tz = channels, since_datetime, get_iran_timezone()
        self.total_configs_by_type: Dict[str, List[str]] = {key: [] for key in RawConfigCollector.PATTERNS.keys()}

    async def scrape_all(self):
        with Progress(
            TextColumn("[bold blue]Scraping Telegram..."),
            BarColumn(bar_width=None),
            "[progress.percentage]{task.percentage:>3.0f}%",
            "•",
            TextColumn("[green]{task.completed}/{task.total} Channels"),
            "•",
            TimeRemainingColumn(),
            console=console
        ) as progress:
            task = progress.add_task("channels", total=len(self.channels))
            
            tasks = [self._scrape_channel_with_retry(ch) for ch in self.channels]
            for future in asyncio.as_completed(tasks):
                channel_results = await future
                if isinstance(channel_results, dict):
                    for config_type, configs in channel_results.items():
                        self.total_configs_by_type[config_type].extend(configs)
                progress.update(task, advance=1)

    async def _scrape_channel_with_retry(self, channel: str, max_retries: int = 2) -> Optional[Dict[str, List[str]]]:
        for attempt in range(max_retries):
            try:
                await asyncio.sleep(random.uniform(1.5, 3.0))
                url = CONFIG.TELEGRAM_BASE_URL.format(channel)

                status, html = await AsyncHttpClient.get(url)
                if status == 200 and html:
                    soup = BeautifulSoup(html, "html.parser")
                    messages = soup.find_all("div", class_="tgme_widget_message", limit=CONFIG.TELEGRAM_MESSAGE_LIMIT)
                    if not messages: return {}

                    channel_configs: Dict[str, List[str]] = {key: [] for key in RawConfigCollector.PATTERNS.keys()}
                    configs_count_in_channel = 0
                    
                    for msg in messages:
                        if configs_count_in_channel >= CONFIG.MAX_CONFIGS_PER_CHANNEL:
                            break

                        time_tag = msg.find("time", class_="time")
                        if time_tag and 'datetime' in time_tag.attrs:
                            try:
                                message_dt = datetime.fromisoformat(time_tag['datetime']).astimezone(self.iran_tz)
                                if CONFIG.TELEGRAM_IGNORE_LAST_UPDATE or message_dt > self.since_datetime:
                                    text_div = msg.find("div", class_="tgme_widget_message_text")
                                    if text_div:
                                        found_configs = RawConfigCollector.find_all(text_div.get_text('\n', strip=True))
                                        for config_type, configs in found_configs.items():
                                            remaining_slots = CONFIG.MAX_CONFIGS_PER_CHANNEL - configs_count_in_channel
                                            if remaining_slots <= 0: break
                                            
                                            configs_to_add = configs[:remaining_slots]
                                            channel_configs[config_type].extend(configs_to_add)
                                            configs_count_in_channel += len(configs_to_add)
                                        
                                        if configs_count_in_channel >= CONFIG.MAX_CONFIGS_PER_CHANNEL:
                                            break
                            except (ValueError, TypeError): continue
                    return channel_configs
            except (NetworkError, Exception):
                pass
            if attempt < max_retries - 1:
                await asyncio.sleep((attempt + 1) * 5)
        return None

class SubscriptionFetcher:
    def __init__(self, sub_links: List[str]):
        self.sub_links = sub_links
        self.total_configs_by_type: Dict[str, List[str]] = {key: [] for key in RawConfigCollector.PATTERNS.keys()}

    async def fetch_all(self):
        with Progress(
            TextColumn("[bold blue]Fetching Subscriptions..."),
            BarColumn(bar_width=None),
            "[progress.percentage]{task.percentage:>3.0f}%",
            "•",
            TextColumn("[green]{task.completed}/{task.total} Links"),
            console=console
        ) as progress:
            tasks = [self._fetch_and_decode(link) for link in self.sub_links]
            for f in progress.track(asyncio.as_completed(tasks), total=len(self.sub_links), description="links"):
                content = await f
                if isinstance(content, str):
                    found_configs = RawConfigCollector.find_all(content)
                    for config_type, configs in found_configs.items():
                        self.total_configs_by_type[config_type].extend(configs)

    async def _fetch_and_decode(self, link: str) -> str:
        try:
            _, content = await AsyncHttpClient.get(link)
            try:
                return base64.b64decode(content + '==').decode('utf-8')
            except Exception:
                return content
        except Exception:
            return ""

class FileManager:
    def __init__(self, config: AppConfig):
        self.config = config
        self._setup_directories()

    def _setup_directories(self):
        CONFIG.DATA_DIR.mkdir(exist_ok=True)
        CONFIG.OUTPUT_DIR.mkdir(exist_ok=True)
        for path in self.config.DIRS.values():
            path.mkdir(parents=True, exist_ok=True)

    async def write_configs_to_file(self, file_path: Path, configs: List[BaseConfig]):
        if not configs: return
        final_list = [c.to_uri() for c in configs]
        content = "\n".join(final_list)
        
        try:
            file_path.parent.mkdir(parents=True, exist_ok=True)
            async with aiofiles.open(file_path, 'w', encoding='utf-8') as f:
                await f.write(content)
        except IOError:
            pass

class Geolocation:
    _country_reader: Optional[geoip2.database.Reader] = None
    _asn_reader: Optional[geoip2.database.Reader] = None
    _ip_cache: Dict[str, Optional[str]] = {}

    @classmethod
    def initialize(cls):
        if CONFIG.GEOIP_DB_FILE.exists():
            try:
                cls._country_reader = geoip2.database.Reader(str(CONFIG.GEOIP_DB_FILE))
            except Exception: 
                cls._country_reader = None
        
        if CONFIG.GEOIP_ASN_DB_FILE.exists():
            try:
                cls._asn_reader = geoip2.database.Reader(str(CONFIG.GEOIP_ASN_DB_FILE))
            except Exception:
                cls._asn_reader = None

    @classmethod
    async def get_ip(cls, hostname: str) -> Optional[str]:
        if hostname in cls._ip_cache: return cls._ip_cache[hostname]
        if is_ip_address(hostname):
            cls._ip_cache[hostname] = hostname
            return hostname
        try:
            loop = asyncio.get_running_loop()
            addr_info = await loop.getaddrinfo(hostname, None, family=socket.AF_INET)
            ip = addr_info[0][4][0]
            cls._ip_cache[hostname] = ip
            return ip
        except Exception:
            cls._ip_cache[hostname] = None
            return None

    @classmethod
    def get_country_from_ip(cls, ip: str) -> str:
        if cls._country_reader is None or ip is None: return "XX"
        try:
            response = cls._country_reader.country(ip)
            return response.country.iso_code or "XX"
        except (geoip2.errors.AddressNotFoundError, Exception):
            return "XX"
    
    @classmethod
    def get_asn_from_ip(cls, ip: str) -> Optional[str]:
        if cls._asn_reader is None or ip is None: return None
        try:
            response = cls._asn_reader.asn(ip)
            return response.autonomous_system_organization
        except (geoip2.errors.AddressNotFoundError, Exception):
            return None

    @classmethod
    def close(cls):
        if cls._country_reader: cls._country_reader.close()
        if cls._asn_reader: cls._asn_reader.close()

class ConfigProcessor:
    def __init__(self, raw_configs_by_type: Dict[str, List[str]]):
        self.raw_configs_by_type = raw_configs_by_type
        self.parsed_configs: Dict[str, BaseConfig] = {}
        self.total_raw_count = sum(len(v) for v in raw_configs_by_type.values())
        self.allowed_protocols = {'vless', 'vmess'}
        self.passed_connectivity_test_count = 0

    async def process(self):
        console.log(f"Processing {self.total_raw_count} raw config strings...")

        # Pipeline Step 1: Parsing
        all_parsed_configs: List[BaseConfig] = []
        for config_type, configs in self.raw_configs_by_type.items():
            for uri in configs:
                parsed = V2RayParser.parse(uri, source_type=config_type)
                if parsed:
                    all_parsed_configs.append(parsed)
        console.log(f"Successfully parsed {len(all_parsed_configs)} configs.")

        # Pipeline Step 2: Protocol Filtering
        filtered_by_protocol = [c for c in all_parsed_configs if c.protocol in self.allowed_protocols]
        console.log(f"Protocol filter kept {len(filtered_by_protocol)} configs (vless/vmess).")
        
        # Pipeline Step 3: URI Deduplication
        for config in filtered_by_protocol:
            key = config.get_deduplication_key()
            if key not in self.parsed_configs:
                self.parsed_configs[key] = config
        console.log(f"Deduplication by URI resulted in {len(self.parsed_configs)} unique configs.")

        # Pipeline Step 4: Geolocation
        await self._resolve_geo_info()
        
        # Pipeline Step 5: Connectivity Test
        if CONFIG.ENABLE_CONNECTIVITY_TEST:
            await self._test_connectivity()
        
        # Pipeline Step 6: Endpoint Deduplication
        if CONFIG.ENABLE_IP_DEDUPLICATION:
            self._deduplicate_by_endpoint()
            
        # Pipeline Step 7: Formatting and Sorting
        self._format_config_remarks()
        self.parsed_configs = dict(sorted(self.parsed_configs.items(), key=lambda item: (item[1].country, item[1].asn_org or "")))

    async def _resolve_geo_info(self):
        hosts_to_resolve = set()
        for config in self.parsed_configs.values():
            target_host = config.sni if config.sni and not is_ip_address(config.sni) else config.host
            hosts_to_resolve.add(target_host)
        
        console.log(f"Resolving geo-information for {len(hosts_to_resolve)} unique hosts/SNIs...")
        await asyncio.gather(*[Geolocation.get_ip(host) for host in hosts_to_resolve])
        
        for config in self.parsed_configs.values():
            target_host = config.sni if config.sni and not is_ip_address(config.sni) else config.host
            ip_address = Geolocation._ip_cache.get(target_host)
            if ip_address:
                config.country = Geolocation.get_country_from_ip(ip_address)
                config.asn_org = Geolocation.get_asn_from_ip(ip_address)

    async def _test_tcp_connection(self, config: BaseConfig, semaphore: asyncio.Semaphore) -> Optional[str]:
        async with semaphore:
            ip = Geolocation._ip_cache.get(config.host)
            if not ip:
                return None
            
            try:
                fut = asyncio.open_connection(ip, config.port)
                reader, writer = await asyncio.wait_for(fut, timeout=CONFIG.CONNECTIVITY_TEST_TIMEOUT)
                writer.close()
                await writer.wait_closed()
                return config.get_deduplication_key()
            except (asyncio.TimeoutError, ConnectionRefusedError, OSError, Exception):
                return None

    async def _test_connectivity(self):
        configs_to_test = list(self.parsed_configs.values())
        if not configs_to_test:
            return

        console.log(f"Performing connectivity test for {len(configs_to_test)} configs...")
        semaphore = asyncio.Semaphore(CONFIG.CONNECTIVITY_TEST_CONCURRENCY)
        
        passed_keys: Set[str] = set()
        passed_count = 0
        failed_count = 0
        
        with Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            BarColumn(),
            TextColumn("[progress.percentage]{task.percentage:>3.0f}%"),
            "•",
            TextColumn("Passed: [bold green]{task.fields[passed]}"),
            "•",
            TextColumn("Failed: [bold red]{task.fields[failed]}"),
            console=console,
            transient=True
        ) as progress:
            task = progress.add_task(
                "Testing...", 
                total=len(configs_to_test), 
                passed=0, 
                failed=0
            )
            
            test_tasks = [self._test_tcp_connection(c, semaphore) for c in configs_to_test]
            
            for future in asyncio.as_completed(test_tasks):
                result_key = await future
                if result_key:
                    passed_keys.add(result_key)
                    passed_count += 1
                else:
                    failed_count += 1
                
                progress.update(task, advance=1, fields={"passed": passed_count, "failed": failed_count})

        self.passed_connectivity_test_count = len(passed_keys)
        self.parsed_configs = {key: self.parsed_configs[key] for key in passed_keys}
        console.log(f"Connectivity test complete: {self.passed_connectivity_test_count} configs passed.")

    def _deduplicate_by_endpoint(self):
        initial_count = len(self.parsed_configs)
        seen_endpoints: Set[str] = set()
        kept_configs: Dict[str, BaseConfig] = {}
        
        for uri_key, config in self.parsed_configs.items():
            ip = Geolocation._ip_cache.get(config.host)
            if not ip:
                kept_configs[uri_key] = config
                continue

            endpoint_key = f"{ip}:{config.port}:{config.protocol}"
            if endpoint_key not in seen_endpoints:
                seen_endpoints.add(endpoint_key)
                kept_configs[uri_key] = config

        self.parsed_configs = kept_configs
        removed_count = initial_count - len(self.parsed_configs)
        if removed_count > 0:
            console.log(f"Endpoint deduplication removed {removed_count} configs. {len(self.parsed_configs)} remaining.")

    def _format_config_remarks(self):
        for config in self.parsed_configs.values():
            proto_full_map = {'vmess': 'VMESS', 'vless': 'VLESS'}
            proto_full = proto_full_map.get(config.protocol, 'CFG')

            net_type = config.network.upper()
            if config.protocol == 'vless' and config.network == 'http':
                net_type = 'XHTTP'

            sec = 'NTLS'
            if config.security == 'tls':
                sec = 'TLS'
            elif config.security == 'reality':
                sec = 'RLT'
            elif config.security == 'xtls':
                sec = 'XTLS'

            flag = COUNTRY_CODE_TO_FLAG.get(config.country, "🏳️")
            ip_address = Geolocation._ip_cache.get(config.host, "N/A")
            
            asn_str = f" - {config.asn_org}" if config.asn_org else ""
            new_remark = f"{config.country} {flag} ┇ {proto_full}-{net_type}-{sec}{asn_str} ┇ {ip_address}"
            config.remarks = new_remark.strip()

    def get_all_unique_configs(self) -> List[BaseConfig]:
        return list(self.parsed_configs.values())

    # ИЗМЕНЕНО: Полностью переписанный метод для классификации, а не фильтрации
    def categorize(self) -> Dict[str, Dict[str, List[BaseConfig]]]:
        """
        Categorizes configs into different buckets for saving.
        - 'custom_datacenters' for desired ASNs.
        - 'datacenters' for other ASNs.
        - 'protocols' with '_custom' suffix for desired ASNs.
        """
        console.log("Categorizing final configs...")
        configs = self.get_all_unique_configs()
        
        categories: Dict[str, Dict[str, List[BaseConfig]]] = { 
            "protocols": {}, 
            "datacenters": {},
            "custom_datacenters": {}
        }
        
        for config in configs:
            is_desired = False
            if config.asn_org:
                is_desired = any(keyword in config.asn_org.lower() for keyword in CONFIG.DESIRED_ASN_KEYWORDS)

            # Route to the correct datacenter folder
            if is_desired:
                target_datacenter_cat = "custom_datacenters"
            else:
                target_datacenter_cat = "datacenters"
            
            if config.asn_org:
                sanitized_asn = re.sub(r'[\\/*?:"<>|,]', "", config.asn_org).replace(" ", "_")
                categories[target_datacenter_cat].setdefault(sanitized_asn, []).append(config)

            # Route to the correct protocol file
            protocol_key = f"{config.protocol}_custom" if is_desired else config.protocol
            categories["protocols"].setdefault(protocol_key, []).append(config)
                
        return categories

class V2RayCollectorApp:
    def __init__(self):
        self.config = CONFIG
        self.file_manager = FileManager(self.config)
        self.last_update_time = datetime.now(get_iran_timezone()) - timedelta(days=1)

    async def run(self):
        console.rule("[bold green]V2Ray Config Collector - v33.0.0 (Classified & Tested)[/bold green]")
        await self._load_state()

        tg_channels = await self._fetch_source(CONFIG.REMOTE_TELEGRAM_CHANNELS_URL, "Telegram channels")
        sub_links = await self._fetch_source(CONFIG.REMOTE_SUBSCRIPTION_LINKS_URL, "subscription links")

        tg_scraper = TelegramScraper(tg_channels, self.last_update_time)
        sub_fetcher = SubscriptionFetcher(sub_links)

        if tg_channels: await tg_scraper.scrape_all()
        if sub_links and CONFIG.ENABLE_SUBSCRIPTION_FETCHING: await sub_fetcher.fetch_all()

        combined_raw_configs: Dict[str, List[str]] = {key: [] for key in RawConfigCollector.PATTERNS.keys()}
        for config_type in combined_raw_configs.keys():
            combined_raw_configs[config_type].extend(tg_scraper.total_configs_by_type.get(config_type, []))
            combined_raw_configs[config_type].extend(sub_fetcher.total_configs_by_type.get(config_type, []))

        if not any(combined_raw_configs.values()):
            console.log("[yellow]No new configurations found. Exiting.[/yellow]")
            return

        processor = ConfigProcessor(combined_raw_configs)
        await processor.process()

        all_unique_configs = processor.get_all_unique_configs()
        if not all_unique_configs:
            console.log("[yellow]No valid unique configurations to save. Exiting.[/yellow]")
            return
            
        categories = processor.categorize()
        await self._save_results(categories)
        await self._save_state()
        self._print_summary_report(processor)
        console.log("[bold green]Collection and processing complete.[/bold green]")

    async def _fetch_source(self, url: str, description: str) -> List[str]:
        try:
            console.log(f"Fetching {description} from {url}...")
            status, content = await AsyncHttpClient.get(url)
            if status == 200 and content:
                data = json.loads(content)
                if isinstance(data, list):
                    console.log(f"[green]Successfully fetched {len(data)} {description}.[/green]")
                    return data
            console.log(f"[bold red]Failed to fetch {description}. Status: {status}[/bold red]")
        except (NetworkError, json.JSONDecodeError, Exception) as e:
            console.log(f"[bold red]Error fetching {description}: {e}[/bold red]")
        return []

    async def _load_state(self):
        if self.config.LAST_UPDATE_FILE.exists():
            try:
                async with aiofiles.open(self.config.LAST_UPDATE_FILE, 'r') as f:
                    self.last_update_time = datetime.fromisoformat(await f.read())
            except Exception: pass

    async def _save_state(self):
        try:
            async with aiofiles.open(self.config.LAST_UPDATE_FILE, 'w') as f:
                await f.write(datetime.now(get_iran_timezone()).isoformat())
        except IOError: pass

    def _sanitize_filename(self, name: str) -> str:
        name = re.sub(r'[\U0001F600-\U0001F64F\U0001F300-\U0001F5FF\U0001F680-\U0001F6FF\U0001F700-\U0001F77F\U0001F780-\U0001F7FF\U0001F800-\U0001F8FF\U0001F900-\U0001F9FF\U0001FA00-\U0001FA6F\U0001FA70-\U0001FAFF\U00002702-\U000027B0\U00002620-\U0000262F\U00002300-\U000023FF\U00002B50]', '', name)
        return re.sub(r'[\\/*?:"<>|,@=]', "", name).replace(" ", "_")

    async def _save_results(self, categories: Dict[str, Any]):
        console.log("Saving categorized configurations...")
        save_tasks: List[Coroutine] = []
        
        for cat_name, cat_items in categories.items():
            if cat_name in self.config.DIRS:
                for item_name, configs in cat_items.items():
                    if configs:
                        sanitized_name = self._sanitize_filename(str(item_name))
                        if not sanitized_name: continue
                        path = self.config.DIRS[cat_name] / f"{sanitized_name}.txt"
                        save_tasks.append(self.file_manager.write_configs_to_file(path, configs))
            
        await asyncio.gather(*save_tasks)

    def _print_summary_report(self, processor: ConfigProcessor):
        all_configs = processor.get_all_unique_configs()
        protocol_counts = Counter(c.protocol for c in all_configs)
        country_counts = Counter(c.country for c in all_configs if c.country and c.country != 'XX')
        asn_counts = Counter(c.asn_org for c in all_configs if c.asn_org)

        summary_table = Table(title="📊 Final Collection Report 📊", title_style="bold magenta", show_header=False)
        summary_table.add_column("Key", style="cyan")
        summary_table.add_column("Value", style="bold green")

        summary_table.add_row("Raw Configs Found", str(processor.total_raw_count))
        if CONFIG.ENABLE_CONNECTIVITY_TEST:
            summary_table.add_row("Passed Connectivity Test", str(processor.passed_connectivity_test_count))
        summary_table.add_row("Final Saved Configs", str(len(all_configs)))
        
        console.print(summary_table)

        proto_table = Table(title="📈 Configs by Protocol", title_style="bold blue")
        proto_table.add_column("Protocol", style="cyan")
        proto_table.add_column("Count", style="bold green")
        for protocol, count in protocol_counts.most_common():
            proto_table.add_row(protocol.upper(), str(count))
            
        country_table = Table(title="🌍 Top 5 Countries", title_style="bold blue")
        country_table.add_column("Flag")
        country_table.add_column("Country", style="cyan")
        country_table.add_column("Count", style="bold green")
        for country_code, count in country_counts.most_common(5):
            flag = COUNTRY_CODE_TO_FLAG.get(country_code, '🏳️')
            country_table.add_row(flag, country_code, str(count))

        asn_table = Table(title="🏢 Top 5 Datacenters", title_style="bold blue")
        asn_table.add_column("Datacenter", style="cyan")
        asn_table.add_column("Count", style="bold green")
        for asn, count in asn_counts.most_common(5):
            asn_table.add_row(asn, str(count))

        console.print(proto_table)
        console.print(country_table)
        console.print(asn_table)
        
async def _download_db_if_needed(url: str, file_path: Path):
    if not file_path.exists():
        console.log(f"[yellow]{file_path.name} not found, downloading...[/yellow]")
        try:
            async with httpx.AsyncClient() as client:
                response = await client.get(url, follow_redirects=True, timeout=120.0)
                response.raise_for_status()
                async with aiofiles.open(file_path, "wb") as f:
                    await f.write(response.content)
                console.log(f"[green]{file_path.name} downloaded successfully.[/green]")
        except Exception as e:
            console.log(f"[bold red]Failed to download {file_path.name}: {e}.[/bold red]")

async def main():
    CONFIG.DATA_DIR.mkdir(exist_ok=True)

    await _download_db_if_needed(CONFIG.GEOIP_DB_URL, CONFIG.GEOIP_DB_FILE)
    await _download_db_if_needed(CONFIG.GEOIP_ASN_DB_URL, CONFIG.GEOIP_ASN_DB_FILE)

    Geolocation.initialize()

    app = V2RayCollectorApp()
    try:
        await app.run()
    except KeyboardInterrupt:
        console.log("\n[yellow]Application interrupted by user.[/yellow]")
    except Exception as e:
        console.log(f"\n[bold red]An unhandled exception occurred: {e}[/bold red]")
        console.print_exception()
    finally:
        await AsyncHttpClient.close()
        Geolocation.close()
        console.rule("[bold green]Shutdown complete.[/bold green]")

if __name__ == "__main__":
    asyncio.run(main())

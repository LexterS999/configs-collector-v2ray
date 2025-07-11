# 🚀 V2Ray Config Collector

### Автоматизированный сбор, проверка и классификация конфигураций V2Ray

<div align="center">

![Статус](https://img.shields.io/badge/Статус-Активен-brightgreen?style=for-the-badge&logo=github)
![Протоколы](https://img.shields.io/badge/Протоколы-Vmess%20%26%20Vless-blueviolet?style=for-the-badge&logo=v2ray)
![Проверка](https://img.shields.io/badge/Проверка%20порта-Выключена-blue?style=for-the-badge&logo=dependabot)
![Обновление](https://img.shields.io/badge/Автообновление-Каждые%2012%20часов-teal?style=for-the-badge&logo=clock)
![Лицензия](https://img.shields.io/badge/Лицензия-MIT-lightgrey?style=for-the-badge&logo=mit)

</div>

---

## 💡 О проекте

**V2Ray Config Collector** — это полностью автоматизированный инструмент для сбора, обработки и предоставления рабочих конфигураций V2Ray. Система сканирует публичные Telegram-каналы и ссылки на подписки, извлекая из них конфигурации.

В отличие от простых сборщиков, этот проект реализует многоступенчатый конвейер обработки данных:

1.  **Сбор:** Агрегирует конфигурации из множества источников.
2.  **Парсинг и фильтрация:** Извлекает только конфигурации **Vmess** и **Vless**, отбрасывая остальные.
3.  **Проверка доступности:** Выполняет базовую проверку доступности TCP-порта для каждой конфигурации, чтобы отсеять заведомо нерабочие серверы.
4.  **Обогащение данных:** Определяет страну (GeoIP) и провайдера (ASN) для каждого сервера.
5.  **Дедупликация:** Удаляет дубликаты как по URI, так и по конечному эндпоинту (IP:Port), оставляя только уникальные серверы.
6.  **Классификация и сохранение:** Формирует удобные списки подписок, сгруппированные по протоколу, стране и, что особенно важно, по **провайдеру/дата-центру**.

Результатом являются чистые, проверенные и структурированные списки конфигураций, готовые к использованию.

### 🎯 Ключевые особенности

*   **Полная автоматизация:** Сбор и обработка выполняются автономно без ручного вмешательства.
*   **Проверка качества:** Базовая проверка доступности портов и умная дедупликация значительно повышают качество итоговых списков.
*   **Обогащение данных:** Каждая конфигурация содержит информацию о стране и провайдере (ASN), что помогает в выборе оптимального сервера.
*   **Структурированный вывод:** Конфигурации разделены на категории для удобной навигации и интеграции.
*   **Прозрачность:** Весь процесс обработки данных открыт и описан в исходном коде.

---

## ⚙️ Принцип работы

Процесс обработки данных можно представить в виде следующего конвейера:

1.  **Сбор сырых данных:** Скрипт загружает списки Telegram-каналов и ссылок на подписки, после чего асинхронно собирает из них текстовые данные, содержащие конфигурации.
2.  **Парсинг и фильтрация:** Из сырого текста извлекаются все найденные конфигурации. На этом этапе происходит **фильтрация**: в дальнейшую обработку попадают **только Vmess и Vless**.
3.  **Проверка доступности порта:** Для каждой конфигурации выполняется попытка установить TCP-соединение с сервером по указанному порту. Конфигурации, не прошедшие проверку, отбрасываются.
4.  **Гео-обогащение и дедупликация:** Для прошедших проверку конфигураций определяются IP-адрес, страна и ASN. Затем удаляются дубликаты по конечному адресу (`IP:Port`).
5.  **Форматирование:** Имена (remarks) конфигураций приводятся к единому стандарту для наглядности: `Страна [Флаг] ┇ ПРОТОКОЛ-СЕТЬ-ЗАЩИТА - Провайдер ┇ IP`.
6.  **Классификация и сохранение:** Финальный список конфигураций распределяется по файлам в зависимости от протокола, страны и провайдера.

---

## 🗂️ Структура подписок

Все подписки находятся в директории [`/sub`](https://github.com/LexterS999/configs-collector-v2ray/tree/main/sub).

### По протоколу

Эти файлы содержат конфигурации, сгруппированные по типу протокола.

| Протокол | Описание | Ссылка на подписку |
| :--- | :--- | :--- |
| **Vmess** | Стандартный протокол V2Ray | [`📡 Ссылка`](https://raw.githubusercontent.com/LexterS999/configs-collector-v2ray/main/sub/protocols/vmess.txt) |
| **Vless** | Облегченный протокол V2Ray | [`📡 Ссылка`](https://raw.githubusercontent.com/LexterS999/configs-collector-v2ray/main/sub/protocols/vless.txt) |

#### ⭐ Избранные конфигурации (Custom)

Это подмножество конфигураций от избранных, проверенных провайдеров (например, Hetzner, AEZA, DigitalOcean). Часто они показывают лучшую стабильность и скорость.

| Протокол | Описание | Ссылка на подписку |
| :--- | :--- | :--- |
| **Vmess (Custom)** | Vmess от избранных провайдеров | [`📡 Ссылка`](https://raw.githubusercontent.com/LexterS999/configs-collector-v2ray/main/sub/protocols/vmess_custom.txt) |
| **Vless (Custom)** | Vless от избранных провайдеров | [`📡 Ссылка`](https://raw.githubusercontent.com/LexterS999/configs-collector-v2ray/main/sub/protocols/vless_custom.txt) |

### 🏢 По провайдеру (ASN)

Для более точного выбора сервера конфигурации также сгруппированы по провайдерам.

*   **[⭐ Избранные провайдеры (Custom Datacenters)](https://github.com/LexterS999/configs-collector-v2ray/tree/main/sub/custom_datacenters)** — папка с подписками от избранных провайдеров.
*   **[🌐 Остальные провайдеры (Datacenters)](https://github.com/LexterS999/configs-collector-v2ray/tree/main/sub/datacenters)** — папка с подписками от всех остальных провайдеров.

---

## 🚀 Быстрый старт

1.  **Выберите подписку:** Определитесь с нужной категорией (по протоколу, стране или провайдеру). Для начала рекомендуем попробовать ссылки из раздела **"Избранные конфигурации"**.
2.  **Скопируйте ссылку:** Нажмите правой кнопкой мыши на `📡 Ссылка` и скопируйте адрес.
3.  **Добавьте в клиент:** Вставьте скопированную ссылку в ваш V2Ray-клиент (например, V2RayNG, Nekoray, Streisand) в разделе управления подписками.
4.  **Обновите подписку:** После добавления обновите подписку в клиенте, чтобы загрузить список серверов.
5.  **Подключитесь:** Выберите любой сервер из списка и подключитесь.

> **Совет:** Если скорость или стабильность вас не устраивает, просто попробуйте другой сервер из списка.

---

## ❓ Часто задаваемые вопросы

**Как часто обновляются конфигурации?**
Процесс сбора и обновления запускается автоматически каждые 30 минут.

**Какие клиенты V2Ray поддерживаются?**
Наши подписки совместимы с большинством популярных клиентов, поддерживающих стандартные форматы ссылок, включая V2RayNG, Nekoray, v2flyNG, Qv2ray и другие.

**Безопасно ли это?**
Проект собирает конфигурации из публичных источников. Мы выполняем базовую проверку доступности, но не можем гарантировать безопасность каждого отдельного сервера. Используйте на свой страх и риск.

---

## 📜 Лицензия

Этот проект распространяется под лицензией MIT. Подробности смотрите в файле [LICENSE](https://github.com/LexterS999/configs-collector-v2ray/blob/main/LICENSE).

---

<div align="center">
  <strong>Создано с ❤️ для глобального сообщества</strong><br>
  <a href="https://github.com/LexterS999/configs-collector-v2ray">🌟 Поставьте звезду на GitHub</a>
</div>

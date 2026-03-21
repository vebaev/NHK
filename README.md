<p align="center">

[![NHK Easy](docs/android-chrome-192x192.png)](https://vebaev.github.io/NHK/)
# 最新ニュース
![License](https://img.shields.io/badge/license-GPL--3.0-green)
![Platform](https://img.shields.io/badge/platform-Web-blue)
![PWA](https://img.shields.io/badge/PWA-supported-orange)

</p>

# NHK Easy Японски новини

Уеб приложение за четене на **NHK Easy News** с помощни инструменти за изучаване на японски.

Публичен сайт: [https://vebaev.github.io/NHK/](https://vebaev.github.io/NHK/)

## Какво прави проектът

Скриптът [`nhk_easy_pipeline.py`](nhk_easy_pipeline.py) изтегля последните NHK Easy статии, анализира ги и генерира статичен сайт в [`docs/index.html`](docs/index.html).

Текущата версия:
- показва заглавие, изображение, аудио и японски текст за последните статии
- поддържа превод на български и английски за заглавия, абзаци и popup съдържание
- отваря popup при клик върху елемент от текста
- показва за глаголите: превод, речникова форма, образуване и формула
- подчертава граматични конструкции в синьо
- подчертава глаголи с пастелно оранжево
- подчертава имена, държави, градове, институции и други named entities с пастелно зелено
- генерира Anki файлове за основните елементи от текста
- генерира PWA файлове и service worker за GitHub Pages

## AI и анализ

Проектът вече използва **Gemini**, не Groq.

- API ключ: `GEMINI_API` или `GEMINI_API_KEY`
- модел по подразбиране: `gemini-3.1-flash-lite-preview`
- override: `GEMINI_MODEL`
- limiter в кода: `15 RPM` и `250000 TPM`

Gemini се използва за:
- анализ на елементи в статиите
- корекции и нормализация на глаголни форми
- извличане на граматика на ниво статия

## Генерирани файлове

Основният локален build създава или обновява:
- [`docs/index.html`](docs/index.html)
- [`docs/anki_cards_bg.tsv`](docs/anki_cards_bg.tsv)
- [`docs/nhk_easy_elements_bg.apkg`](docs/nhk_easy_elements_bg.apkg)
- [`docs/anki_seen_words.json`](docs/anki_seen_words.json)
- [`docs/translations_cache.json`](docs/translations_cache.json)
- [`docs/gemini_verbs_cache.json`](docs/gemini_verbs_cache.json)
- [`docs/manifest.webmanifest`](docs/manifest.webmanifest)
- [`docs/sw.js`](docs/sw.js)

В `docs/` може да има и по-стари или допълнителни артефакти от предишни версии. Реалният current pipeline работи основно с файловете по-горе.

## Локално пускане

Изисквания:
- Python 3.11+
- инсталирани зависимости от [`requirements.txt`](requirements.txt)
- валиден Gemini API ключ

Инсталация:

```bash
cd /Users/baev/Desktop/NHK
pip install -r requirements.txt
```

Примерен run:

```bash
cd /Users/baev/Desktop/NHK
GEMINI_API='YOUR_KEY' python3 nhk_easy_pipeline.py --output docs/index.html --count 4
```

Полезни аргументи:
- `--output` за изходния HTML файл
- `--count` за брой статии
- `--gemini-key` за API ключ
- `--gemini-model` за override на модела
- `--deepl-key` ако искаш да подадеш DeepL ключ от CLI

Има оставени `--groq-key` и `--groq-model` аргументи само за backward compatibility, но те вече се пренасочват към Gemini настройките.

## Автоматично обновяване

GitHub Actions workflow: [`.github/workflows/daily_nhk_easy.yml`](.github/workflows/daily_nhk_easy.yml)

В момента workflow-ът:
- се пуска при `push`
- може да се пусне ръчно чрез `workflow_dispatch`
- е планиран на `12:00 UTC` и `16:00 UTC`
- използва `GEMINI_API` от GitHub `secrets` или `vars`
- commit-ва обновените `docs/` артефакти обратно в репото

## Как се използва сайтът

1. Отвори [https://vebaev.github.io/NHK/](https://vebaev.github.io/NHK/)
2. Избери език на помощния интерфейс: български или английски
3. Чети японския текст
4. Кликни върху абзац за превод
5. Кликни върху подчертана дума или форма за popup обяснение
6. По желание свали Anki deck-а или TSV файла

## За кого е полезен

Най-подходящо е за:
- учащи около `N5`, `N4` и ранно `N3`
- хора, които искат преход от учебни примери към реални текстове
- учащи, които комбинират четене, слушане, граматика и Anki

## Ограничения

Анализът е автоматичен. Въпреки че pipeline-ът е по-силен от предишната версия, все още са възможни:
- неточни lemma или reading стойности
- частично разпознати grammar patterns
- случаи, в които лексика и граматика се припокриват
- named entity heuristics, които не хващат всички имена или понякога маркират прекалено широко

## Източник на съдържанието

Новините идват от **NHK Easy News**. Проектът не е официален продукт на NHK.

## Автор

Създадено от **Веселин Баев**  
GitHub: **vebaev**  
Email: **vebaev@gmail.com**

## License

This project is licensed under the **GNU General Public License v3.0 (GPL-3.0)**.

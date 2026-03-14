
import os
import re
import argparse
import html as html_lib
import hashlib
import json
import logging
import time
from urllib.parse import urljoin, urlparse

import requests
from requests import Session
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from bs4 import BeautifulSoup, NavigableString
from googletrans import Translator
import sqlite3

try:
    import fugashi
except Exception:
    fugashi = None

try:
    import genanki
except Exception:
    genanki = None

EASY_SITEMAP_URL = "https://news.web.nhk/news/easy/sitemap/sitemap.xml"
NHKEASIER_FEED_URL = "https://nhkeasier.com/feed/"
DEFAULT_OUTPUT = "docs/index.html"
DEFAULT_ANKI_FILENAME = "anki_cards_bg.tsv"
DEFAULT_ANKI_APKG_FILENAME = "nhk_easy_vocab_bg.apkg"
DEFAULT_GRAMMAR_TSV_FILENAME = "anki_grammar_bg.tsv"
DEFAULT_GRAMMAR_APKG_FILENAME = "nhk_easy_grammar_bg.apkg"
DEFAULT_ANKI_EN_FILENAME = "anki_cards_en.tsv"
DEFAULT_ANKI_EN_APKG_FILENAME = "nhk_easy_vocab_en.apkg"
DEFAULT_GRAMMAR_EN_TSV_FILENAME = "anki_grammar_en.tsv"
DEFAULT_GRAMMAR_EN_APKG_FILENAME = "nhk_easy_grammar_en.apkg"
DEFAULT_ANKI_SEEN_WORDS_FILENAME = "anki_seen_words.json"

translator = Translator()
DEEPL_API_KEY = os.environ.get("DEEPL_API_KEY", "").strip()
_TRANSLATION_CACHE = {}
_TRANSLATION_STATS = {"deepl": 0, "google": 0, "cache": 0}
_TRANSLATION_CACHE_PATH = None
_TRANSLATION_CACHE_DIRTY = False
_MECAB_TAGGER = None
_WORD_GLOSSARY = None
_JMDICT_DB = None
_HTTP_SESSION = None

logger = logging.getLogger(__name__)

PARTICLE_PREFIXES = ("が", "を", "に", "で", "は", "と", "へ", "や", "も", "の")
GODAN_I_TO_U = {"い":"う","き":"く","ぎ":"ぐ","し":"す","ち":"つ","に":"ぬ","び":"ぶ","み":"む","り":"る"}
GODAN_A_TO_U = {"わ":"う","か":"く","が":"ぐ","さ":"す","た":"つ","な":"ぬ","ば":"ぶ","ま":"む","ら":"る"}

GRAMMAR_RULES = [
    {"id": "kedo", "label": "けど / けれど", "explanation_bg": "Съюз за противопоставяне: но / обаче.", "explanation_en": ""},
    {"id": "shikashi", "label": "しかし", "explanation_bg": "Обаче / въпреки това.", "explanation_en": ""},
    {"id": "temo", "label": "〜ても / 〜でも", "explanation_bg": "Дори ако / дори и да.", "explanation_en": ""},
    {"id": "nagara", "label": "〜ながら", "explanation_bg": "Едновременно действие: докато...", "explanation_en": ""},
    {"id": "tsutsu", "label": "〜つつ", "explanation_bg": "Докато..., в хода на...", "explanation_en": ""},
    {"id": "aida_ni", "label": "間 / あいだ(に)", "explanation_bg": "Докато / през времето, когато...", "explanation_en": ""},
    {"id": "uchi_ni", "label": "うちに", "explanation_bg": "Докато все още..., преди да се промени...", "explanation_en": ""},
    {"id": "kara_reason", "label": "〜から", "explanation_bg": "Причина: защото / понеже.", "explanation_en": ""},
    {"id": "node", "label": "〜ので", "explanation_bg": "Причина: тъй като / понеже.", "explanation_en": ""},
    {"id": "sorede", "label": "それで", "explanation_bg": "И затова / поради това.", "explanation_en": ""},
    {"id": "soshite", "label": "そして", "explanation_bg": "И / и след това.", "explanation_en": ""},
    {"id": "yori", "label": "〜より", "explanation_bg": "Сравнение: по-... от...", "explanation_en": ""},
    {"id": "hou", "label": "〜方", "explanation_bg": "Страна / начин; използва се и в сравнения.", "explanation_en": ""},
    {"id": "hou_ga_ii", "label": "〜方がいい / 〜方がよい", "explanation_bg": "По-добре е да...", "explanation_en": ""},
    {"id": "noni", "label": "〜のに", "explanation_bg": "Въпреки че / макар че.", "explanation_en": ""},
    {"id": "you_ni", "label": "〜ように", "explanation_bg": "Така че да..., по начин, че...", "explanation_en": ""},
    {"id": "tame_ni", "label": "〜ため(に)", "explanation_bg": "За да..., заради..., в името на...", "explanation_en": ""},
    {"id": "sei_de", "label": "〜せいで", "explanation_bg": "По вина на..., заради (негативно).", "explanation_en": ""},
    {"id": "okage_de", "label": "〜おかげで", "explanation_bg": "Благодарение на...", "explanation_en": ""},
    {"id": "rashii", "label": "〜らしい", "explanation_bg": "Изглежда / явно / характерно за.", "explanation_en": ""},
    {"id": "ppoi", "label": "〜っぽい", "explanation_bg": "Прилича на..., има оттенък на...", "explanation_en": ""},
    {"id": "dame", "label": "だめ", "explanation_bg": "Не става / не бива / забранено е.", "explanation_en": ""},
    {"id": "naranai", "label": "〜ならない", "explanation_bg": "Не бива / не става; в комбинации може да означава задължение.", "explanation_en": ""},
    {"id": "ikenai", "label": "〜いけない", "explanation_bg": "Не бива / не става; в комбинации може да означава задължение.", "explanation_en": ""},
    {"id": "nakereba_naranai", "label": "〜なければならない", "explanation_bg": "Трябва да...", "explanation_en": ""},
    {"id": "nakereba_ikenai", "label": "〜なければいけない", "explanation_bg": "Трябва да...", "explanation_en": ""},
    {"id": "nakutewa_naranai", "label": "〜なくてはならない", "explanation_bg": "Трябва да...", "explanation_en": ""},
    {"id": "tari_tari", "label": "〜たり〜たりする", "explanation_bg": "Правя разни неща като...", "explanation_en": ""},
    {"id": "dake", "label": "〜だけ", "explanation_bg": "Само / единствено.", "explanation_en": ""},
    {"id": "nomi", "label": "〜のみ", "explanation_bg": "Само / единствено (по-формално).", "explanation_en": ""},
    {"id": "bakari", "label": "〜ばかり", "explanation_bg": "Само..., все...", "explanation_en": ""},
    {"id": "shika_nai", "label": "〜しか〜ない", "explanation_bg": "Нищо друго освен..., само...", "explanation_en": ""},
    {"id": "mou", "label": "もう", "explanation_bg": "Вече.", "explanation_en": ""},
    {"id": "mada", "label": "まだ", "explanation_bg": "Още / все още.", "explanation_en": ""},
    {"id": "mata", "label": "また", "explanation_bg": "Пак / отново / също така.", "explanation_en": ""},
    {"id": "te_ii", "label": "〜ていい", "explanation_bg": "Разрешено е да...", "explanation_en": ""},
    {"id": "temo_ii", "label": "〜てもいい", "explanation_bg": "Може да... / разрешено е да...", "explanation_en": ""},
    {"id": "te_miru", "label": "〜てみる", "explanation_bg": "Да пробвам да...", "explanation_en": ""},
    {"id": "kke", "label": "〜っけ", "explanation_bg": "Беше ли..., как беше...", "explanation_en": ""},
    {"id": "kana", "label": "〜かな", "explanation_bg": "Чудя се дали..., дали...", "explanation_en": ""},
    {"id": "kai_dai", "label": "〜かい / 〜だい", "explanation_bg": "Разговорна въпросителна форма.", "explanation_en": ""},
    {"id": "janai", "label": "〜じゃない", "explanation_bg": "Не е ли..., нали...", "explanation_en": ""},
    {"id": "causative_saseru", "label": "使役 (〜させる / 〜せる)", "explanation_bg": "Каузатив: карам/оставям някого да...", "explanation_en": ""},
    {"id": "nakute", "label": "〜なくて", "explanation_bg": "Без да..., не и..., понеже не...", "explanation_en": ""},
    {"id": "naide", "label": "〜ないで", "explanation_bg": "Без да..., не правейки...", "explanation_en": ""},
    {"id": "zu", "label": "〜ず / 〜ずに", "explanation_bg": "Без да...", "explanation_en": ""},
    {"id": "te_shimau", "label": "〜てしまう", "explanation_bg": "Завършеност или нежелан резултат.", "explanation_en": ""},
    {"id": "te_oku", "label": "〜ておく", "explanation_bg": "Правя нещо предварително.", "explanation_en": ""},
    {"id": "datte", "label": "だって", "explanation_bg": "Защото..., дори..., дори и...", "explanation_en": ""},
    {"id": "wake", "label": "〜わけ", "explanation_bg": "Причина / смисъл / следва, че...", "explanation_en": ""},
    {"id": "hazu", "label": "〜はず", "explanation_bg": "Би трябвало / очаква се.", "explanation_en": ""},
    {"id": "beki", "label": "〜べき", "explanation_bg": "Трябва / редно е.", "explanation_en": ""},
    {"id": "beki_datta", "label": "〜べきだった", "explanation_bg": "Трябвало е да...", "explanation_en": ""},
    {"id": "beshi", "label": "〜べし", "explanation_bg": "Трябва / следва (книжовно).", "explanation_en": ""},
    {"id": "mono_da", "label": "〜ものだ", "explanation_bg": "По принцип така е / естествено е / подобава.", "explanation_en": ""},
    {"id": "kamoshirenai", "label": "〜かもしれない", "explanation_bg": "Може би...", "explanation_en": ""},
    {"id": "kamo", "label": "〜かも", "explanation_bg": "Може би... (разговорно).", "explanation_en": ""},
    {"id": "koro", "label": "〜ころ", "explanation_bg": "Около даден момент / по времето, когато...", "explanation_en": ""},
    {"id": "goro", "label": "〜ごろ", "explanation_bg": "Около (час/период).", "explanation_en": ""},
    {"id": "kurai_gurai", "label": "〜くらい / 〜ぐらい", "explanation_bg": "Около / приблизително / до такава степен.", "explanation_en": ""},
    {"id": "made", "label": "〜まで", "explanation_bg": "До / чак до.", "explanation_en": ""},
    {"id": "kara_made", "label": "〜から〜まで", "explanation_bg": "От... до...", "explanation_en": ""},
    {"id": "made_ni", "label": "〜までに", "explanation_bg": "До (краен срок).", "explanation_en": ""},
    {"id": "hodo", "label": "〜ほど", "explanation_bg": "До такава степен / колкото...", "explanation_en": ""},
    {"id": "sugiru", "label": "〜すぎる", "explanation_bg": "Прекалено / твърде много.", "explanation_en": ""},
]
GRAMMAR_RULES_BY_ID = {r["id"]: r for r in GRAMMAR_RULES}

def configure_logging(verbose: bool = False):
    level = logging.DEBUG if verbose else logging.INFO
    logging.basicConfig(level=level, format="%(levelname)s %(message)s")

def build_http_session() -> Session:
    session = Session()
    retries = Retry(
        total=3,
        connect=3,
        read=3,
        backoff_factor=1.0,
        status_forcelist=[429, 500, 502, 503, 504],
        allowed_methods=frozenset(["GET", "POST"]),
        raise_on_status=False,
    )
    adapter = HTTPAdapter(max_retries=retries)
    session.mount("https://", adapter)
    session.mount("http://", adapter)
    session.headers.update({"User-Agent": "nhk-easy-pipeline/2.0"})
    return session

def get_http_session() -> Session:
    global _HTTP_SESSION
    if _HTTP_SESSION is None:
        _HTTP_SESSION = build_http_session()
    return _HTTP_SESSION

def http_get(url: str, **kwargs):
    timeout = kwargs.pop("timeout", 20)
    logger.debug("HTTP GET %s", url)
    response = get_http_session().get(url, timeout=timeout, **kwargs)
    response.raise_for_status()
    return response

def http_post(url: str, **kwargs):
    timeout = kwargs.pop("timeout", 20)
    logger.debug("HTTP POST %s", url)
    response = get_http_session().post(url, timeout=timeout, **kwargs)
    response.raise_for_status()
    return response

def set_translation_cache_path(path: str = ""):
    global _TRANSLATION_CACHE_PATH
    _TRANSLATION_CACHE_PATH = path or None

def load_translation_cache():
    global _TRANSLATION_CACHE
    if not _TRANSLATION_CACHE_PATH or not os.path.exists(_TRANSLATION_CACHE_PATH):
        return
    try:
        with open(_TRANSLATION_CACHE_PATH, "r", encoding="utf-8") as f:
            raw = json.load(f)
        if isinstance(raw, dict):
            _TRANSLATION_CACHE = {}
            for key, value in raw.items():
                try:
                    parsed_key = tuple(json.loads(key))
                except Exception:
                    continue
                _TRANSLATION_CACHE[parsed_key] = value
            logger.info("Loaded %d cached translations from %s", len(_TRANSLATION_CACHE), _TRANSLATION_CACHE_PATH)
    except Exception as e:
        logger.warning("Failed to load translation cache from %s: %s", _TRANSLATION_CACHE_PATH, e)

def save_translation_cache(force: bool = False):
    global _TRANSLATION_CACHE_DIRTY
    if not _TRANSLATION_CACHE_PATH or (not _TRANSLATION_CACHE_DIRTY and not force):
        return
    try:
        cache_dir = os.path.dirname(_TRANSLATION_CACHE_PATH)
        if cache_dir:
            os.makedirs(cache_dir, exist_ok=True)
        serializable = {json.dumps(list(key), ensure_ascii=False): value for key, value in _TRANSLATION_CACHE.items()}
        with open(_TRANSLATION_CACHE_PATH, "w", encoding="utf-8") as f:
            json.dump(serializable, f, ensure_ascii=False, indent=2)
        _TRANSLATION_CACHE_DIRTY = False
        logger.info("Saved %d cached translations to %s", len(_TRANSLATION_CACHE), _TRANSLATION_CACHE_PATH)
    except Exception as e:
        logger.warning("Failed to save translation cache to %s: %s", _TRANSLATION_CACHE_PATH, e)

def cache_translation_result(cache_key, result: str) -> str:
    global _TRANSLATION_CACHE_DIRTY
    _TRANSLATION_CACHE[cache_key] = result
    _TRANSLATION_CACHE_DIRTY = True
    return result

def ensure_grammar_bilingual():
    for rule in GRAMMAR_RULES:
        if not rule.get("explanation_en"):
            rule["explanation_en"] = rule.get("explanation_bg", "")
    global GRAMMAR_RULES_BY_ID
    GRAMMAR_RULES_BY_ID = {r["id"]: r for r in GRAMMAR_RULES}


def load_word_glossary():
    global _WORD_GLOSSARY
    if _WORD_GLOSSARY is not None:
        return _WORD_GLOSSARY
    candidates = ["glossary_overrides.json", os.path.join(os.path.dirname(__file__), "glossary_overrides.json")]
    for path in candidates:
        if os.path.exists(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    _WORD_GLOSSARY = {str(k).strip(): str(v).strip() for k, v in data.items() if str(k).strip()}
                    return _WORD_GLOSSARY
            except Exception as e:
                logger.warning("Failed to load glossary file %s: %s", path, e)
    _WORD_GLOSSARY = {}
    return _WORD_GLOSSARY

def get_jmdict_db_path():
    candidates = [
        os.environ.get("JMDICT_DB", "").strip(),
        "data/jmdict.db",
        "jmdict.db",
        os.path.join(os.path.dirname(__file__), "data", "jmdict.db"),
        os.path.join(os.path.dirname(__file__), "jmdict.db"),
    ]
    for path in candidates:
        if path and os.path.exists(path):
            return path
    return ""


def get_jmdict_connection():
    global _JMDICT_DB
    if _JMDICT_DB is not None:
        return _JMDICT_DB
    db_path = get_jmdict_db_path()
    if not db_path:
        return None
    try:
        _JMDICT_DB = sqlite3.connect(db_path)
        _JMDICT_DB.row_factory = sqlite3.Row
        return _JMDICT_DB
    except Exception as e:
        logger.warning("Failed to open JMdict database %s: %s", db_path, e)
        _JMDICT_DB = None
        return None


def lookup_dictionary_meaning(word: str, reading: str = "") -> str:
    glossary = load_word_glossary()
    if word in glossary:
        return glossary[word]
    if reading and reading in glossary:
        return glossary[reading]

    conn = get_jmdict_connection()
    if conn is None:
        return ""

    queries = []
    if word:
        queries.append(("surface", word))
        lemma = to_dictionary_form(word)
        if lemma and lemma != word:
            queries.append(("surface", lemma))
    if reading:
        queries.append(("reading", reading))

    seen = set()
    for mode, value in queries:
        if not value or (mode, value) in seen:
            continue
        seen.add((mode, value))
        try:
            if mode == "surface":
                rows = conn.execute(
                    "SELECT gloss FROM entries WHERE surface = ? ORDER BY priority DESC, length(surface) DESC LIMIT 3",
                    (value,)
                ).fetchall()
            else:
                rows = conn.execute(
                    "SELECT gloss FROM entries WHERE reading = ? ORDER BY priority DESC LIMIT 3",
                    (value,)
                ).fetchall()
            if rows:
                glosses = []
                for row in rows:
                    gloss = (row["gloss"] or "").strip()
                    if gloss and gloss not in glosses:
                        glosses.append(gloss)
                if glosses:
                    return "; ".join(glosses[:2])
        except Exception as e:
            logger.warning("Dictionary lookup failed for %s=%r: %s", mode, value, e)
            continue
    return ""



def lookup_dictionary_entry(word: str, reading: str = ""):
    glossary = load_word_glossary()
    if word in glossary:
        return {"gloss": glossary[word], "reading": reading}
    if reading and reading in glossary:
        return {"gloss": glossary[reading], "reading": reading}

    conn = get_jmdict_connection()
    if conn is None:
        return None

    queries = []
    if word:
        queries.append(("surface", word))
        lemma = to_dictionary_form(word)
        if lemma and lemma != word:
            queries.append(("surface", lemma))
    if reading:
        queries.append(("reading", reading))

    seen = set()
    for mode, value in queries:
        if not value or (mode, value) in seen:
            continue
        seen.add((mode, value))
        try:
            if mode == "surface":
                rows = conn.execute(
                    "SELECT surface, reading, gloss, pos, priority FROM entries WHERE surface = ? ORDER BY priority DESC, length(surface) DESC LIMIT 5",
                    (value,),
                ).fetchall()
            else:
                rows = conn.execute(
                    "SELECT surface, reading, gloss, pos, priority FROM entries WHERE reading = ? ORDER BY priority DESC, length(surface) DESC LIMIT 5",
                    (value,),
                ).fetchall()
            if rows:
                row = rows[0]
                return {
                    "surface": (row["surface"] or "").strip(),
                    "reading": (row["reading"] or "").strip(),
                    "gloss": (row["gloss"] or "").strip(),
                    "pos": (row["pos"] or "").strip(),
                    "priority": int(row["priority"] or 0),
                }
        except Exception as e:
            logger.warning("Dictionary entry lookup failed for %s=%r: %s", mode, value, e)
            continue
    return None


def merge_compound_nouns(tokens):
    compounds = []
    current = []
    for token in tokens:
        feat = token_feature(token)
        pos1 = getattr(feat, "pos1", "") if feat is not None else ""
        pos2 = getattr(feat, "pos2", "") if feat is not None else ""
        surface = token_surface(token).strip()
        reading = normalize_katakana_to_hiragana(feature_reading(token).strip())
        if pos1 == "名詞" and pos2 not in {"代名詞", "非自立"} and surface:
            current.append((surface, reading))
        else:
            if len(current) >= 2:
                compounds.append(current[:])
            current = []
    if len(current) >= 2:
        compounds.append(current[:])
    return compounds

def translate_text(text: str, dest: str = "bg") -> str:
    text = (text or "").strip()
    if not text:
        return ""
    cache_key = ("text", text, dest, bool(DEEPL_API_KEY))
    if cache_key in _TRANSLATION_CACHE:
        _TRANSLATION_STATS["cache"] += 1
        return _TRANSLATION_CACHE[cache_key]
    if DEEPL_API_KEY:
        try:
            deepl_url = "https://api-free.deepl.com/v2/translate"
            if not DEEPL_API_KEY.endswith(":fx"):
                deepl_url = "https://api.deepl.com/v2/translate"
            resp = http_post(deepl_url, headers={"Authorization": f"DeepL-Auth-Key {DEEPL_API_KEY}"}, data={"text": text, "target_lang": dest.upper()})
            data = resp.json()
            translations = data.get("translations") or []
            if translations and translations[0].get("text"):
                result = translations[0]["text"].strip()
                _TRANSLATION_STATS["deepl"] += 1
                return cache_translation_result(cache_key, result)
        except Exception as e:
            logger.warning("DeepL translation failed for dest=%s text=%r: %s", dest, text[:80], e)
    try:
        result = translator.translate(text, dest=dest).text
        _TRANSLATION_STATS["google"] += 1
        return cache_translation_result(cache_key, result)
    except Exception as e:
        logger.warning("googletrans translation failed for dest=%s text=%r: %s", dest, text[:80], e)
        return ""


def translate_word(word: str, reading: str = "") -> str:
    word = (word or "").strip()
    if not word:
        return ""
    cache_key = ("word", word, reading)
    if cache_key in _TRANSLATION_CACHE:
        return _TRANSLATION_CACHE[cache_key]

    entry = lookup_dictionary_entry(word, reading=reading)
    if entry and entry.get("gloss"):
        result = entry["gloss"]
        return cache_translation_result(cache_key, result)

    result = translate_text(word, dest="bg")
    _TRANSLATION_CACHE[cache_key] = result
    return result


def translate_word_lang(word: str, reading: str = "", dest: str = "bg") -> str:
    word = (word or "").strip()
    if not word:
        return ""
    cache_key = ("word_lang", word, reading, dest)
    if cache_key in _TRANSLATION_CACHE:
        return _TRANSLATION_CACHE[cache_key]

    entry = lookup_dictionary_entry(word, reading=reading)
    if entry and entry.get("gloss"):
        gloss = entry["gloss"].strip()
        result = gloss if dest == "en" else (translate_text(gloss, dest=dest) or gloss)
        return cache_translation_result(cache_key, result)

    # Fallback path for words missing from JMdict:
    # JP -> EN is often more reliable than JP -> BG, so bridge through EN for BG.
    direct = translate_text(word, dest=dest)
    if direct and direct.strip() != word:
        return cache_translation_result(cache_key, direct.strip())

    en_guess = translate_text(word, dest="en")
    if en_guess and en_guess.strip() != word:
        if dest == "en":
            return cache_translation_result(cache_key, en_guess.strip())
        bridged = translate_text(en_guess, dest=dest)
        if bridged and bridged.strip() != en_guess:
            return cache_translation_result(cache_key, bridged.strip())
        return cache_translation_result(cache_key, en_guess.strip())

    return cache_translation_result(cache_key, "")


def contextual_surface_meaning(surface: str, lemma: str = "", reading_surface: str = "", reading_lemma: str = "", form_label_bg: str = "", form_label_en: str = ""):
    surface = (surface or "").strip()
    lemma = (lemma or "").strip()
    reading_surface = normalize_katakana_to_hiragana((reading_surface or "").strip())
    reading_lemma = normalize_katakana_to_hiragana((reading_lemma or "").strip())
    form_label_bg = (form_label_bg or "").strip()
    form_label_en = (form_label_en or "").strip()

    base_bg = translate_word_lang(lemma or surface, reading_lemma or reading_surface, dest="bg") or ""
    base_en = translate_word_lang(lemma or surface, reading_lemma or reading_surface, dest="en") or ""

    direct_bg = translate_text(surface, dest="bg") or ""
    direct_en = translate_text(surface, dest="en") or ""

    def usable_direct(src, out):
        src = (src or "").strip()
        out = (out or "").strip()
        return bool(out and out != src)

    if form_label_bg == "учтива отрицателна форма на 〜ている":
        bg = "не е " + base_bg if base_bg and not base_bg.startswith("не ") else (base_bg or "")
        en = "has not been " + base_en if base_en else ""
        if not bg:
            bg = direct_bg if usable_direct(surface, direct_bg) else "не е намерено"
        if not en:
            en = direct_en if usable_direct(surface, direct_en) else "has not been found"
        return {"bg": bg, "en": en}

    if form_label_bg == "учтива форма на 〜ている" and base_bg:
        return {"bg": "е " + base_bg, "en": ("is " + base_en) if base_en else direct_en}
    if form_label_bg == "минала форма на 〜ている" and base_bg:
        return {"bg": "беше " + base_bg, "en": ("was " + base_en) if base_en else direct_en}

    return {
        "bg": direct_bg if usable_direct(surface, direct_bg) else base_bg,
        "en": direct_en if usable_direct(surface, direct_en) else base_en,
    }


def get_article_blocks(content):
    blocks = []
    for el in content.find_all(["p", "h2", "h3", "li"], recursive=True):
        txt = el.get_text(" ", strip=True)
        if not txt or len(txt) < 3:
            continue
        blocks.append({"text": txt, "html": "".join(str(x) for x in el.contents).strip()})
    return blocks

def get_mecab_tagger():
    global _MECAB_TAGGER
    if _MECAB_TAGGER is not None:
        return _MECAB_TAGGER
    if fugashi is None:
        return None
    try:
        _MECAB_TAGGER = fugashi.Tagger()
    except Exception as e:
        logger.warning("Failed to initialize fugashi tagger: %s", e)
        _MECAB_TAGGER = None
    return _MECAB_TAGGER

def token_feature(token):
    return getattr(token, "feature", None)
def token_surface(token) -> str:
    return getattr(token, "surface", "") or ""
def token_lemma(token) -> str:
    feat = token_feature(token)
    if feat is None:
        return ""
    for name in ("lemma", "dictionary_form", "lemma_form", "orthBase"):
        value = getattr(feat, name, "") or ""
        if value:
            return value.strip()
    return ""
def feature_reading(token) -> str:
    feat = token_feature(token)
    if feat is None:
        return ""
    for name in ("kana", "pron", "reading", "pronBase"):
        value = getattr(feat, name, "") or ""
        if value and value != "*":
            return value.strip()
    return ""
def normalize_katakana_to_hiragana(text: str) -> str:
    result = []
    for ch in text or "":
        code = ord(ch)
        result.append(chr(code - 0x60) if 0x30A1 <= code <= 0x30F6 else ch)
    return "".join(result)


def get_reading_for_word(word: str, fallback: str = "") -> str:
    word = (word or "").strip()
    fallback = normalize_katakana_to_hiragana((fallback or "").strip())
    if not word:
        return fallback
    entry = lookup_dictionary_entry(word)
    if entry and (entry.get("reading") or "").strip():
        return normalize_katakana_to_hiragana((entry.get("reading") or "").strip())
    tagger = get_mecab_tagger()
    if tagger is not None:
        try:
            tokens = list(tagger(word))
            if tokens:
                reading = normalize_katakana_to_hiragana("".join(feature_reading(t).strip() for t in tokens))
                if reading:
                    return reading
        except Exception as e:
            logger.warning("Failed to derive reading for %r: %s", word, e)
    return fallback

def unique_keep_order(values):
    seen = set()
    out = []
    for v in values or []:
        s = (v or "").strip()
        if s and s not in seen:
            seen.add(s)
            out.append(s)
    return out

def safe_feature_value(feat, *names):
    if feat is None:
        return ""
    for name in names:
        value = getattr(feat, name, "") or ""
        if value and value != "*":
            return str(value).strip()
    return ""

def classify_japanese_form(surface: str, lemma: str = "", pos1: str = "", pos2: str = "", ctype: str = "", cform: str = ""):
    s = (surface or "").strip()
    l = (lemma or "").strip()
    low = (ctype + " " + cform).lower()

    if s and l and s == l:
        return {"bg": "речникова форма", "en": "dictionary form"}
    if s.endswith(("ていません", "でいません")):
        return {"bg": "учтива отрицателна форма на 〜ている", "en": "polite negative 〜te iru form"}
    if s.endswith(("ていました", "でいました")):
        return {"bg": "учтива минала форма на 〜ている", "en": "polite past 〜te iru form"}
    if s.endswith(("ています", "でいます")):
        return {"bg": "учтива форма на 〜ている", "en": "polite 〜te iru form"}
    if s.endswith(("ていない", "でいない")):
        return {"bg": "отрицателна форма на 〜ている", "en": "negative 〜te iru form"}
    if s.endswith(("ていた", "でいた")):
        return {"bg": "минала форма на 〜ている", "en": "past 〜te iru form"}
    if s.endswith(("ている", "でいる")):
        return {"bg": "форма на 〜ている", "en": "〜te iru form"}
    if s.endswith("なかった"):
        return {"bg": "отрицателна минала форма", "en": "past negative form"}
    if s.endswith("なくて"):
        return {"bg": "форма なくて", "en": "nakute form"}
    if s.endswith("ないで"):
        return {"bg": "форма ないで", "en": "naide form"}
    if any(x in low for x in ["past", "連用タ接続"]) or (s.endswith(("た","だ")) and s != l):
        if pos1 == "形容詞" or s.endswith("かった"):
            return {"bg": "минала форма на i-прилагателно", "en": "past i-adjective form"}
        if "polite" in low or s.endswith("ました"):
            return {"bg": "учтива минала форма", "en": "polite past form"}
        return {"bg": "минало време", "en": "past tense"}
    if s.endswith("ません"):
        return {"bg": "учтива отрицателна форма", "en": "polite negative form"}
    if s.endswith(("ない","ぬ","ん")) and s != l:
        return {"bg": "отрицателна форма", "en": "negative form"}
    if s.endswith(("て","で")) and s != l:
        return {"bg": "て-форма", "en": "te-form"}
    if s.endswith(("ます","です")) and s != l:
        return {"bg": "учтива форма", "en": "polite form"}
    if s.endswith("ましょう"):
        return {"bg": "учтива волева форма", "en": "polite volitional form"}
    if s.endswith(("よう","おう")) and s != l:
        return {"bg": "волева форма", "en": "volitional form"}
    if s.endswith(("れる","られる")) and s != l:
        return {"bg": "пасивна / потенциална форма", "en": "passive / potential form"}
    if "使役" in ctype or s.endswith(("せる","させる")):
        return {"bg": "каузативна форма", "en": "causative form"}
    if s.endswith("たい"):
        return {"bg": "форма за желание", "en": "desire form"}
    if s.endswith("くて"):
        return {"bg": "свързваща форма на i-прилагателно", "en": "i-adjective conjunctive form"}
    if s.endswith("くない"):
        return {"bg": "отрицателна форма на i-прилагателно", "en": "negative i-adjective form"}
    if s.endswith("かった"):
        return {"bg": "минала форма на i-прилагателно", "en": "past i-adjective form"}
    if pos1 == "動詞":
        return {"bg": "глаголна форма", "en": "verb form"}
    if pos1 == "形容詞":
        return {"bg": "форма на прилагателно", "en": "adjective form"}
    return {"bg": "форма в текста", "en": "form in context"}

def analyze_japanese_word(surface: str, reading_hint: str = "", lemma_hint: str = ""):
    surface = (surface or "").strip()
    reading_hint = normalize_katakana_to_hiragana((reading_hint or "").strip())
    lemma_hint = (lemma_hint or "").strip()
    info = {
        "surface": surface,
        "lemma": surface,
        "reading_surface": reading_hint,
        "reading_lemma": "",
        "pos1": "",
        "pos2": "",
        "ctype": "",
        "cform": "",
        "form_bg": "форма в текста",
        "form_en": "form in context",
    }
    tagger = get_mecab_tagger()
    if tagger is not None and surface:
        try:
            tokens = list(tagger(surface))
            if tokens:
                if len(tokens) == 1:
                    tok = tokens[0]
                    feat = token_feature(tok)
                    lemma = token_lemma(tok).strip() or to_dictionary_form(surface) or lemma_hint or surface
                    reading_surface = normalize_katakana_to_hiragana(feature_reading(tok).strip() or reading_hint)
                    info["lemma"] = lemma
                    info["reading_surface"] = reading_surface
                    info["reading_lemma"] = normalize_katakana_to_hiragana(reading_surface if lemma == surface else (lookup_dictionary_entry(lemma, reading=reading_surface) or {}).get("reading",""))
                    info["pos1"] = safe_feature_value(feat, "pos1")
                    info["pos2"] = safe_feature_value(feat, "pos2")
                    info["ctype"] = safe_feature_value(feat, "cType", "ctype", "conjType", "inflectionType")
                    info["cform"] = safe_feature_value(feat, "cForm", "cform", "conjForm", "inflectionForm")
                else:
                    token_lemmas = [token_lemma(t).strip() or token_surface(t).strip() for t in tokens]
                    derived = to_dictionary_form(surface)
                    non_aux_lemmas = [x for x in token_lemmas if x not in {"て", "で", "いる", "居る", "ます", "です", "ん", "ない"}]
                    if derived and derived != surface:
                        info["lemma"] = derived
                    elif non_aux_lemmas:
                        info["lemma"] = non_aux_lemmas[0]
                    elif lemma_hint:
                        info["lemma"] = lemma_hint
                    else:
                        info["lemma"] = "".join(token_lemmas).strip() or surface
                    info["reading_surface"] = normalize_katakana_to_hiragana("".join(feature_reading(t).strip() for t in tokens) or reading_hint)
        except Exception:
            pass
    if not info["lemma"] or info["lemma"] == surface:
        info["lemma"] = to_dictionary_form(surface) or lemma_hint or surface
    if not info["reading_surface"]:
        info["reading_surface"] = reading_hint
    if not info["reading_lemma"]:
        if info["lemma"] == info["surface"]:
            info["reading_lemma"] = info["reading_surface"]
        else:
            info["reading_lemma"] = get_reading_for_word(info["lemma"], fallback="")
    form_labels = classify_japanese_form(info["surface"], info["lemma"], info["pos1"], info["pos2"], info["ctype"], info["cform"])
    info["form_bg"] = form_labels["bg"]
    info["form_en"] = form_labels["en"]
    return info

def build_lookup_candidates(surface: str, reading: str = "", lemma: str = ""):
    surface = (surface or "").strip()
    reading = normalize_katakana_to_hiragana((reading or "").strip())
    lemma = (lemma or "").strip()
    candidates = [surface, lemma, lemmatize_japanese(surface), to_dictionary_form(surface), reading]
    return unique_keep_order(candidates)

def register_vocab_item(vocab_lookup, item, extra_keys=None):
    extra_keys = extra_keys or []
    word = (item.get("word") or "").strip()
    reading = normalize_katakana_to_hiragana((item.get("reading") or "").strip())
    keys = unique_keep_order([word, reading] + list(extra_keys))
    for key in keys:
        if key and key not in vocab_lookup:
            vocab_lookup[key] = item
def is_target_pos(token) -> bool:
    feat = token_feature(token)
    pos1 = getattr(feat, "pos1", "") if feat is not None else ""
    return pos1 in {"動詞", "形容詞"} or "動詞" in str(feat) or "形容詞" in str(feat)
def lemmatize_japanese(word: str) -> str:
    w = (word or "").strip()
    if not w:
        return w
    tagger = get_mecab_tagger()
    if tagger is None:
        return to_dictionary_form(w)
    try:
        tokens = list(tagger(w))
        if len(tokens) == 1 and is_target_pos(tokens[0]):
            lemma = token_lemma(tokens[0])
            if lemma and lemma not in {"*", w}:
                return lemma
    except Exception as e:
        logger.warning("Lemmatization via fugashi failed for %r: %s", w, e)
    return to_dictionary_form(w)
def extract_following_okurigana(ruby_tag):
    sibling = ruby_tag.next_sibling
    while sibling is not None:
        txt = ""
        if isinstance(sibling, str):
            txt = sibling
        elif hasattr(sibling, "get_text"):
            break
        txt = (txt or "").lstrip(" 　\n\t")
        if not txt:
            sibling = sibling.next_sibling
            continue
        m = re.match(r"^([ぁ-んー]{1,8})", txt)
        if m:
            return m.group(1)
        return ""
    return ""
def to_dictionary_form(word: str) -> str:
    w = (word or "").strip()
    if not w:
        return w

    tagger = get_mecab_tagger()
    if tagger is not None:
        try:
            tokens = list(tagger(w))
            if len(tokens) == 1:
                lemma = token_lemma(tokens[0]).strip()
                if lemma and lemma != "*":
                    return lemma
        except Exception as e:
            logger.warning("MeCab dictionary-form lookup failed for %r: %s", w, e)

    irregular_map = {
        "した": "する",
        "して": "する",
        "します": "する",
        "しました": "する",
        "しない": "する",
        "しなかった": "する",
        "きた": "くる",
        "きて": "くる",
        "きます": "くる",
        "きました": "くる",
        "こない": "くる",
        "こなかった": "くる",
    }
    if w in irregular_map:
        return irregular_map[w]

    for suffix in ["していませんでした", "していました", "しています", "していません", "していない", "していた", "している"]:
        if w.endswith(suffix):
            return w[:-len(suffix)] + "する"
    for suffix in ["きていませんでした", "きていました", "きています", "きていません", "きていない", "きていた", "きている"]:
        if w.endswith(suffix):
            return w[:-len(suffix)] + "くる"

    def te_base_to_dictionary(stem: str, voiced: bool = False) -> str:
        stem = (stem or "").strip()
        if not stem:
            return stem
        if stem.endswith("っ"):
            return stem[:-1] + "う"
        if stem.endswith("ん"):
            return stem[:-1] + ("ぶ" if voiced else "む")
        if stem.endswith("し"):
            return stem[:-1] + "す"
        if stem.endswith("い"):
            return stem[:-1] + ("ぐ" if voiced else "く")
        if stem.endswith("ち"):
            return stem[:-1] + "つ"
        if stem.endswith("り"):
            return stem[:-1] + "る"
        if stem.endswith("び"):
            return stem[:-1] + "ぶ"
        if stem.endswith("み"):
            return stem[:-1] + "む"
        if stem.endswith("ぎ"):
            return stem[:-1] + "ぐ"
        return stem + "る"

    te_iru_suffixes = [
        "ていませんでした", "でいませんでした",
        "ていました", "でいました",
        "ていません", "でいません",
        "ていない", "でいない",
        "ています", "でいます",
        "ていた", "でいた",
        "ている", "でいる",
    ]
    for suffix in te_iru_suffixes:
        if w.endswith(suffix) and len(w) > len(suffix):
            stem = w[:-len(suffix)]
            return te_base_to_dictionary(stem, voiced=suffix.startswith("で"))

    for suffix in ["していました", "しています", "しました", "します", "して", "した", "しない", "しなかった"]:
        if w.endswith(suffix):
            return w[:-len(suffix)] + "する"
    for suffix in ["きました", "きます", "きて", "きた", "こない", "こなかった"]:
        if w.endswith(suffix):
            return w[:-len(suffix)] + "くる"

    for src, dst in [("かった", "い"), ("くて", "い"), ("くない", "い")]:
        if w.endswith(src) and len(w) > len(src):
            return w[:-len(src)] + dst

    for suffix in ["ました", "ます"]:
        if w.endswith(suffix):
            stem = w[:-len(suffix)]
            if not stem:
                return w
            mapped = GODAN_I_TO_U.get(stem[-1])
            return stem[:-1] + mapped if mapped else stem + "る"

    if w.endswith("なかった") and len(w) > 4:
        stem = w[:-4]
        mapped = GODAN_A_TO_U.get(stem[-1]) if stem else None
        return stem[:-1] + mapped if mapped else stem + "る"

    if w.endswith("ない") and len(w) > 2:
        stem = w[:-2]
        mapped = GODAN_A_TO_U.get(stem[-1]) if stem else None
        return stem[:-1] + mapped if mapped else stem + "る"

    for src, dst in [("いて", "く"), ("いで", "ぐ"), ("して", "す"), ("した", "す"), ("いた", "く"), ("いだ", "ぐ")]:
        if w.endswith(src) and len(w) > len(src):
            return w[:-len(src)] + dst

    return w

def is_person_name_span(tokens_slice) -> bool:
    if not tokens_slice:
        return False
    pos1s = []
    pos2s = []
    surfaces = []
    for t in tokens_slice:
        feat = token_feature(t)
        pos1s.append(getattr(feat, "pos1", "") if feat is not None else "")
        pos2s.append(getattr(feat, "pos2", "") if feat is not None else "")
        surfaces.append(token_surface(t).strip())
    if any(p1 != "名詞" for p1 in pos1s):
        return False
    joined = "".join(surfaces)
    if joined.endswith(("さん", "君", "くん", "ちゃん", "氏")):
        return True
    markers = ("人名", "姓", "名")
    return any(any(m in (p2 or "") for m in markers) for p2 in pos2s)

def is_matchable_token_span(tokens_slice) -> bool:
    if not tokens_slice:
        return False
    if len(tokens_slice) == 1:
        return True
    pos1s = []
    surfaces = []
    for t in tokens_slice:
        feat = token_feature(t)
        pos1s.append(getattr(feat, "pos1", "") if feat is not None else "")
        surfaces.append(token_surface(t).strip())

    if any(p in {"記号", "補助記号"} for p in pos1s):
        return False

    # Reject phrases carrying particles such as で / を / が / の / など
    if any(p == "助詞" for p in pos1s):
        return False

    if all(p == "名詞" for p in pos1s):
        return True

    first = pos1s[0]
    if first in {"動詞", "形容詞"}:
        allowed_tail = {"助動詞", "動詞", "形容詞", "接尾辞", "接尾", "非自立"}
        return all((p in allowed_tail or p == "") for p in pos1s[1:])

    return False

def should_keep_token_for_vocab(token) -> bool:
    surface = token_surface(token).strip()
    if not surface:
        return False
    if len(surface) == 1 and re.fullmatch(r"[ぁ-んァ-ンー]", surface):
        return False
    feat = token_feature(token)
    pos1 = getattr(feat, "pos1", "") if feat is not None else ""
    pos2 = getattr(feat, "pos2", "") if feat is not None else ""
    if pos1 in {"名詞", "動詞", "形容詞", "副詞"}:
        if pos1 == "名詞" and pos2 in {"代名詞", "数詞", "非自立"}:
            return False
        return True
    return False

def is_suspicious_vocab_word(word: str) -> bool:
    w = (word or "").strip()
    if not w:
        return True
    if len(w) < 2:
        return True
    if re.match(r"^[ぁ-んー]+[ァ-ン一-龯]", w):
        return True
    if re.search(r"[<>{}=]", w):
        return True
    return False


def ruby_base_text(ruby_tag) -> str:
    text = ""
    for child in ruby_tag.contents:
        name = getattr(child, "name", None)
        if name in {"rt", "rp"}:
            continue
        text += child.get_text("", strip=True) if hasattr(child, "get_text") else str(child)
    return text.strip()


def make_dict_span(soup, item, inner_html: str, analysis=None):
    span = soup.new_tag("span")
    span["class"] = "dict-word"

    analysis = analysis or analyze_japanese_word((item.get("word") or "").strip(), reading_hint=(item.get("reading") or "").strip(), lemma_hint=(item.get("word") or "").strip())
    surface = (analysis.get("surface") or item.get("word") or "").strip()
    lemma = (analysis.get("lemma") or item.get("word") or surface).strip()
    reading_surface = normalize_katakana_to_hiragana((analysis.get("reading_surface") or item.get("reading") or "").strip())
    reading_lemma = normalize_katakana_to_hiragana((analysis.get("reading_lemma") or "").strip())
    if not reading_lemma:
        reading_lemma = reading_surface if lemma == surface else get_reading_for_word(lemma, fallback="")
    form_bg = (analysis.get("form_bg") or "форма в текста").strip()
    form_en = (analysis.get("form_en") or "form in context").strip()

    lemma_entry = lookup_dictionary_entry(lemma) or lookup_dictionary_entry(lemma, reading=reading_lemma)
    lemma_gloss_en = ((lemma_entry or {}).get("gloss") or "").strip()
    lemma_meaning_en = lemma_gloss_en
    lemma_meaning_bg = (translate_text(lemma_gloss_en, dest="bg") if lemma_gloss_en else "").strip()

    exact_item_match = lemma == (item.get("word") or "").strip() == surface
    if not lemma_meaning_bg and exact_item_match and (item.get("meaning_bg") or "").strip():
        lemma_meaning_bg = (item.get("meaning_bg") or "").strip()
    if not lemma_meaning_en and exact_item_match and (item.get("meaning_en") or "").strip():
        lemma_meaning_en = (item.get("meaning_en") or "").strip()
    if not lemma_meaning_bg:
        lemma_meaning_bg = lemma_meaning_en
    if not lemma_meaning_en:
        lemma_meaning_en = lemma_meaning_bg

    contextual = contextual_surface_meaning(
        surface=surface,
        lemma=lemma,
        reading_surface=reading_surface,
        reading_lemma=reading_lemma,
        form_label_bg=form_bg,
        form_label_en=form_en,
    )
    surface_meaning_bg = (contextual.get("bg") or "").strip() or lemma_meaning_bg
    surface_meaning_en = (contextual.get("en") or "").strip() or lemma_meaning_en

    if lemma == surface:
        reading_lemma = ""
        lemma_meaning_bg = ""
        lemma_meaning_en = ""

    span["data-surface"] = surface
    span["data-lemma"] = lemma
    span["data-reading-surface"] = reading_surface
    span["data-reading-lemma"] = reading_lemma
    span["data-form-bg"] = form_bg
    span["data-form-en"] = form_en
    span["data-meaning-surface-bg"] = surface_meaning_bg
    span["data-meaning-surface-en"] = surface_meaning_en
    span["data-meaning-lemma-bg"] = lemma_meaning_bg
    span["data-meaning-lemma-en"] = lemma_meaning_en

    frag = BeautifulSoup(inner_html, "html.parser")
    for node in list(frag.contents):
        span.append(node)
    return span

def extract_vocab_from_blocks(blocks):
    vocab_map = {}
    for block in blocks:
        soup = BeautifulSoup(block["html"], "html.parser")
        for ruby in soup.find_all("ruby"):
            rb_text = ""
            rt_text = ""
            for child in ruby.contents:
                name = getattr(child, "name", None)
                if name == "rt":
                    rt_text += child.get_text("", strip=True)
                elif name == "rp":
                    continue
                else:
                    rb_text += child.get_text("", strip=True) if hasattr(child, "get_text") else str(child).strip()
            rb_text = rb_text.strip()
            rt_text = rt_text.strip()
            if not rb_text or not re.search(r"[一-龯]", rb_text):
                continue
            okurigana = extract_following_okurigana(ruby)
            word = rb_text
            reading = rt_text
            if okurigana and okurigana.startswith(PARTICLE_PREFIXES):
                okurigana = ""
            if okurigana:
                surface_word = rb_text + okurigana
                surface_reading = (rt_text + okurigana).strip()
                word = lemmatize_japanese(surface_word)
                reading = to_dictionary_form(surface_reading)
            if not is_suspicious_vocab_word(word) and word not in vocab_map:
                vocab_map[word] = reading
    tagger = get_mecab_tagger()
    if tagger is not None:
        for block in blocks:
            text = (block.get("text") or "").strip()
            if not text:
                continue
            try:
                tokens = list(tagger(text))
            except Exception:
                continue
            for token in tokens:
                if not should_keep_token_for_vocab(token):
                    continue
                surface = token_surface(token).strip()
                lemma = token_lemma(token).strip() or surface
                reading = normalize_katakana_to_hiragana(feature_reading(token).strip())
                word = lemma if re.search(r"[一-龯ぁ-んァ-ン]", lemma) else surface
                if not word or is_suspicious_vocab_word(word):
                    continue
                if word not in vocab_map:
                    vocab_map[word] = reading
            for compound in merge_compound_nouns(tokens):
                word = "".join(x[0] for x in compound).strip()
                reading = "".join(x[1] for x in compound).strip()
                if not is_suspicious_vocab_word(word) and word not in vocab_map:
                    vocab_map[word] = reading
    vocab = []
    for word, reading in vocab_map.items():
        meaning_bg = translate_word_lang(word, reading, dest="bg")
        meaning_en = translate_word_lang(word, reading, dest="en")
        vocab.append({"word": word, "reading": reading, "meaning_bg": meaning_bg, "meaning_en": meaning_en, "meaning": meaning_bg})
    vocab.sort(key=lambda x: (-len(x["word"]), x["word"]))
    return vocab[:80]


def contains_digit(word: str) -> bool:
    return any(ch.isdigit() for ch in (word or ""))

def is_all_katakana(word: str) -> bool:
    w = (word or "").strip()
    return bool(w) and all(("ァ" <= ch <= "ヶ") or ch == "ー" for ch in w)

def canonicalize_vocab_item(word: str, reading: str = "", meaning_bg: str = "", meaning_en: str = ""):
    word = (word or "").strip()
    reading = normalize_katakana_to_hiragana((reading or "").strip())
    meaning_bg = (meaning_bg or "").strip()
    meaning_en = (meaning_en or "").strip()
    if not word:
        return None

    lemma = lemmatize_japanese(word) or to_dictionary_form(word) or word
    entry = lookup_dictionary_entry(lemma, reading=reading) or lookup_dictionary_entry(word, reading=reading)

    canonical_word = (entry.get("surface") if entry else "") or lemma or word
    canonical_word = canonical_word.strip()
    canonical_reading = normalize_katakana_to_hiragana(((entry.get("reading") if entry else "") or reading).strip())

    if not canonical_reading:
        lemma_entry = lookup_dictionary_entry(canonical_word, reading=reading)
        canonical_reading = normalize_katakana_to_hiragana(((lemma_entry or {}).get("reading","") or reading).strip())

    canonical_meaning_en = ((entry.get("gloss") if entry else "") or meaning_en).strip()
    canonical_meaning_bg = (translate_text(canonical_meaning_en, dest="bg") if canonical_meaning_en else "") or meaning_bg or canonical_meaning_en

    if not canonical_meaning_bg and meaning_bg:
        canonical_meaning_bg = meaning_bg
    if not canonical_meaning_en and meaning_en:
        canonical_meaning_en = meaning_en

    if not canonical_word:
        return None
    if contains_digit(canonical_word) or contains_digit(canonical_reading):
        return None
    if is_all_katakana(canonical_word):
        return None
    if is_suspicious_vocab_word(canonical_word) or is_single_kanji_word(canonical_word):
        return None
    if not re.search(r"[一-龯ぁ-ん]", canonical_word):
        return None
    if not canonical_meaning_bg and not canonical_meaning_en:
        return None

    return {
        "word": canonical_word,
        "reading": canonical_reading,
        "meaning_bg": canonical_meaning_bg or canonical_meaning_en,
        "meaning_en": canonical_meaning_en or canonical_meaning_bg,
    }

def normalize_vocab_group_key(word: str, reading: str = "") -> str:
    base = lemmatize_japanese((word or "").strip())
    entry = lookup_dictionary_entry(base, reading=reading) or lookup_dictionary_entry(word, reading=reading)
    if entry and (entry.get("surface") or "").strip():
        return (entry.get("surface") or "").strip()
    return base or (word or "").strip()

def is_single_kanji_word(word: str) -> bool:
    return bool(re.fullmatch(r"[一-龯]", (word or "").strip()))
def is_known_vocab_item(word: str, known_items):
    return word in known_items or f"v:{word}" in known_items
def is_valid_anki_vocab_item(item):
    word = (item.get("word") or "").strip()
    reading = (item.get("reading") or "").strip()
    meaning_bg = (item.get("meaning_bg") or item.get("meaning") or "").strip()
    meaning_en = (item.get("meaning_en") or "").strip()

    if not word or is_suspicious_vocab_word(word) or is_single_kanji_word(word):
        return None
    if contains_digit(word) or contains_digit(reading):
        return None
    if is_all_katakana(word):
        return None

    return canonicalize_vocab_item(word, reading=reading, meaning_bg=meaning_bg, meaning_en=meaning_en)

def build_vocab_anki_cards(articles, lang="bg"):
    cards = []
    grouped = {}

    for article in articles:
        for item in article.get("vocab", []):
            validated = is_valid_anki_vocab_item(item)
            if not validated:
                continue

            canonical = canonicalize_vocab_item(
                validated["word"],
                reading=validated.get("reading", ""),
                meaning_bg=validated.get("meaning_bg", ""),
                meaning_en=validated.get("meaning_en", ""),
            )
            if not canonical:
                continue

            word = canonical["word"]
            reading = canonical["reading"]
            meaning = canonical["meaning_bg"] if lang == "bg" else canonical["meaning_en"]
            group_key = normalize_vocab_group_key(word, reading=reading) or word

            if is_all_katakana(group_key) or is_all_katakana(word):
                continue
            if not re.search(r"[一-龯ぁ-ん]", group_key):
                continue

            existing = grouped.get(group_key)
            if existing is None:
                grouped[group_key] = {"word": group_key, "reading": reading, "meanings": [meaning] if meaning else []}
            else:
                if reading and not existing["reading"]:
                    existing["reading"] = reading
                if meaning and meaning not in existing["meanings"]:
                    existing["meanings"].append(meaning)

    for item in grouped.values():
        word = (item["word"] or "").strip()
        reading = normalize_katakana_to_hiragana((item["reading"] or "").strip())
        meaning = "; ".join(item["meanings"][:3]).strip()
        if not word or not meaning:
            continue
        if is_all_katakana(word):
            continue
        if not re.search(r"[一-龯ぁ-ん]", word):
            continue
        front = f"<ruby>{word}<rt>{reading}</rt></ruby>" if reading and reading != word else word
        cards.append((front, meaning))

    cards.sort(key=lambda x: x[0])
    return cards


def build_grammar_anki_cards(grammar_points, lang="bg"):
    cards = []
    seen_labels = set()

    for g in grammar_points or []:
        label = (g.get("label") or "").strip()
        explanation = (g.get("explanation_bg") if lang == "bg" else g.get("explanation_en") or "").strip()
        if not label or not explanation or label in seen_labels:
            continue
        seen_labels.add(label)
        cards.append((label, explanation))

    return cards
def load_seen_words(path):
    if not os.path.exists(path):
        return set()
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        return {str(x).strip() for x in data if str(x).strip()} if isinstance(data, list) else set()
    except Exception:
        return set()
def save_seen_words(path, words):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(sorted({w.strip() for w in words if w and w.strip()}), f, ensure_ascii=False, indent=2)
def add_known_progress_to_articles(articles, known_words):
    known = set(known_words or [])
    for article in articles:
        vocab_words = []
        seen_in_article = set()
        for item in article.get("vocab", []):
            word = (item.get("word") or "").strip()
            if not word or is_single_kanji_word(word) or word in seen_in_article:
                continue
            seen_in_article.add(word)
            vocab_words.append(word)
        total = len(vocab_words)
        known_count = sum(1 for w in vocab_words if is_known_vocab_item(w, known))
        article["known_total"] = total
        article["known_count"] = known_count
        article["known_percent"] = int(round((known_count / total) * 100)) if total else 0
def save_anki_tsv(cards, path):
    with open(path, "w", encoding="utf-8") as f:
        for front, back in cards:
            f.write(f"{front}\t{back}\n")
def stable_int_id(seed: str, digits: int = 10) -> int:
    digest = hashlib.sha1(seed.encode("utf-8")).hexdigest()
    h = int(digest[:12], 16)
    mod = 10 ** digits
    return (h % mod) + (10 ** (digits - 1))
def build_anki_apkg(cards, apkg_path, deck_name="NHK Easy Vocabulary"):
    if genanki is None:
        print("genanki is not installed; skipping .apkg generation")
        return False

    model = genanki.Model(
        stable_int_id("nhk_easy_vocab_model_" + deck_name),
        "NHK Easy Card Model " + deck_name,
        fields=[{"name": "Front"}, {"name": "Back"}],
        templates=[{
            "name": "Card 1",
            "qfmt": "<div class='jp-word'>{{Front}}</div>",
            "afmt": "<div class='jp-word'>{{Front}}</div><hr id='answer'><div class='bg-meaning'>{{Back}}</div>",
        }],
        css=".card {font-family: Arial, sans-serif; font-size: 25px; text-align: center; color: black; background-color: white;}.jp-word {font-size: 31px;}.bg-meaning {font-size: 25px;}.jp-word ruby rt {font-size: 14px;}",
    )

    deck = genanki.Deck(stable_int_id("nhk_easy_vocab_deck_" + deck_name), deck_name)
    for front, back in cards:
        deck.add_note(genanki.Note(model=model, fields=[front, back], guid=genanki.guid_for(front, back)))

    genanki.Package(deck).write_to_file(apkg_path)
    return True
def split_japanese_sentences(text: str):
    t = (text or "").strip()
    if not t:
        return []
    return [p.strip() for p in re.split(r"(?<=[。！？])\s*", t) if p.strip()]
def _s(tokens, idx):
    return token_surface(tokens[idx]) if 0 <= idx < len(tokens) else ""
def _l(tokens, idx):
    return token_lemma(tokens[idx]) if 0 <= idx < len(tokens) else ""
def _seq(tokens, start, end):
    return [token_surface(t) for t in tokens[start:end]]
def detect_grammar_in_sentence(sentence: str):
    tagger = get_mecab_tagger()
    found = set()
    if tagger is None:
        return found
    try:
        tokens = list(tagger(sentence))
    except Exception:
        return found
    surfaces = [token_surface(t) for t in tokens]
    lemmas = [token_lemma(t) for t in tokens]
    for i in range(len(tokens)):
        s = surfaces[i]
        l = lemmas[i]
        if s in {"けど", "けれど", "けれども"}: found.add("kedo")
        if s == "しかし": found.add("shikashi")
        if s in {"ても", "でも"} or (s in {"て", "で"} and _s(tokens, i + 1) == "も"): found.add("temo")
        if s == "ながら": found.add("nagara")
        if s == "つつ": found.add("tsutsu")
        if s in {"間", "あいだ"}: found.add("aida_ni")
        if s == "うち" and _s(tokens, i + 1) == "に": found.add("uchi_ni")
        if s == "から": found.add("kara_reason")
        if s == "ので": found.add("node")
        if s == "それで": found.add("sorede")
        if s == "そして": found.add("soshite")
        if s == "より": found.add("yori")
        if s in {"方", "ほう"}:
            found.add("hou")
            if _s(tokens, i + 1) == "が" and _s(tokens, i + 2) in {"いい", "よい", "良い"}: found.add("hou_ga_ii")
        if s == "のに": found.add("noni")
        if s == "よう" and _s(tokens, i + 1) == "に": found.add("you_ni")
        if s == "ため" and (_s(tokens, i + 1) in {"", "に"}): found.add("tame_ni")
        if s == "せい" and _s(tokens, i + 1) == "で": found.add("sei_de")
        if s == "おかげ" and _s(tokens, i + 1) == "で": found.add("okage_de")
        if s == "らしい": found.add("rashii")
        if s == "っぽい": found.add("ppoi")
        if s == "だめ": found.add("dame")
        if s == "なら" and _s(tokens, i + 1) == "ない": found.add("naranai")
        if s == "いけ" and _s(tokens, i + 1) == "ない": found.add("ikenai")
        if s == "なけれ" and _s(tokens, i + 1) == "ば":
            if _s(tokens, i + 2) == "なら" and _s(tokens, i + 3) == "ない": found.add("nakereba_naranai")
            if _s(tokens, i + 2) == "いけ" and _s(tokens, i + 3) == "ない": found.add("nakereba_ikenai")
        if s == "なく" and _seq(tokens, i + 1, i + 5) == ["て", "は", "なら", "ない"]: found.add("nakutewa_naranai")
        if s == "たり" and surfaces.count("たり") >= 2: found.add("tari_tari")
        if s == "だけ": found.add("dake")
        if s == "のみ": found.add("nomi")
        if s == "ばかり": found.add("bakari")
        if s == "しか" and "ない" in surfaces[i + 1:]: found.add("shika_nai")
        if s == "もう": found.add("mou")
        if s == "まだ": found.add("mada")
        if s == "また": found.add("mata")
        if (s in {"て", "で"} and _s(tokens, i + 1) in {"いい", "よい", "良い"}) or s in {"ていい", "でいい"}: found.add("te_ii")
        if s in {"ても", "でも"} and _s(tokens, i + 1) in {"いい", "よい", "良い"}: found.add("temo_ii")
        if s in {"て", "で"} and _s(tokens, i + 1) == "も" and _s(tokens, i + 2) in {"いい", "よい", "良い"}: found.add("temo_ii")
        if s in {"て", "で"} and _l(tokens, i + 1) in {"見る", "みる"}: found.add("te_miru")
        if s == "っけ": found.add("kke")
        if s == "かな": found.add("kana")
        if s in {"かい", "だい"}: found.add("kai_dai")
        if s == "じゃ" and _s(tokens, i + 1) == "ない": found.add("janai")
        if "させ" in s or l in {"させる", "せる"}: found.add("causative_saseru")
        if s == "なく" and _s(tokens, i + 1) == "て": found.add("nakute")
        if s == "ない" and _s(tokens, i + 1) == "で": found.add("naide")
        if s in {"ず", "ずに"} or (s == "ず" and _s(tokens, i + 1) == "に"): found.add("zu")
        if s in {"て", "で"} and _l(tokens, i + 1) in {"仕舞う", "しまう"}: found.add("te_shimau")
        if s in {"て", "で"} and _l(tokens, i + 1) in {"置く", "おく"}: found.add("te_oku")
        if s == "だって": found.add("datte")
        if s == "わけ": found.add("wake")
        if s == "はず": found.add("hazu")
        if s == "べき":
            found.add("beki")
            if _s(tokens, i + 1) == "だっ" and _s(tokens, i + 2) == "た": found.add("beki_datta")
        if s == "べし": found.add("beshi")
        if s == "もの" and _s(tokens, i + 1) == "だ": found.add("mono_da")
        if s == "かも" and _s(tokens, i + 1) == "しれ" and _s(tokens, i + 2) == "ない": found.add("kamoshirenai")
        elif s == "かも": found.add("kamo")
        if s == "ころ": found.add("koro")
        if s == "ごろ": found.add("goro")
        if s in {"くらい", "ぐらい"}: found.add("kurai_gurai")
        if s == "まで":
            found.add("made")
            if _s(tokens, i + 1) == "に": found.add("made_ni")
            if "から" in surfaces[:i]: found.add("kara_made")
        if s == "ほど": found.add("hodo")
        if l == "過ぎる" or s == "すぎる": found.add("sugiru")
    return found
def extract_grammar_details(articles):
    details = []
    for article in articles:
        entry = {"title": article.get("title", ""), "items": []}
        for block in article.get("blocks", []):
            for sentence in split_japanese_sentences(block.get("text", "")):
                rule_ids = sorted(detect_grammar_in_sentence(sentence))
                if not rule_ids:
                    continue
                entry["items"].append({"sentence": sentence, "grammar": [GRAMMAR_RULES_BY_ID[r]["label"] for r in rule_ids if r in GRAMMAR_RULES_BY_ID]})
        details.append(entry)
    return details
def extract_grammar_points(articles):
    found = {}
    for article in articles:
        for block in article.get("blocks", []):
            for sentence in split_japanese_sentences(block.get("text", "")):
                for rule_id in detect_grammar_in_sentence(sentence):
                    if rule_id not in found and rule_id in GRAMMAR_RULES_BY_ID:
                        rule = GRAMMAR_RULES_BY_ID[rule_id]
                        found[rule_id] = {"label": rule["label"], "explanation_bg": rule["explanation_bg"], "explanation_en": rule["explanation_en"]}
    return [found[rule["id"]] for rule in GRAMMAR_RULES if rule["id"] in found]
def extract_ne_id(text: str) -> str:
    m = re.search(r"(ne\d{10,})", text or "")
    return m.group(1) if m else ""
def get_nhkeasier_items():
    r = http_get(NHKEASIER_FEED_URL)
    soup = BeautifulSoup(r.text, "xml")
    items = {}
    for item in soup.find_all("item"):
        title = (item.title.get_text() if item.title else "").strip()
        desc_raw = (item.description.get_text() if item.description else "").strip()
        desc_html = html_lib.unescape(desc_raw)
        desc_soup = BeautifulSoup(desc_html, "html.parser")
        audio_url = ""
        enclosure = item.find("enclosure")
        if enclosure and enclosure.get("url"):
            audio_url = enclosure.get("url").strip()
        if not audio_url:
            audio_tag = desc_soup.select_one("audio[src], audio source[src]")
            if audio_tag:
                audio_url = (audio_tag.get("src") or "").strip()
        image_url = ""
        itunes_img = item.find("itunes:image")
        if itunes_img and itunes_img.get("href"):
            image_url = itunes_img.get("href").strip()
        if not image_url:
            img_tag = desc_soup.select_one("img[src]")
            if img_tag:
                image_url = (img_tag.get("src") or "").strip()
        blocks = []
        for b in get_article_blocks(desc_soup):
            t = b["text"].strip()
            if not t:
                continue
            if t.lower() in {"original", "permalink"} or "Original" in t or "Permalink" in t:
                continue
            blocks.append(b)
        ne_id = ""
        original_link = ""
        for a in desc_soup.select("a[href]"):
            href = (a.get("href") or "").strip()
            if "/news/easy/ne" in href:
                original_link = href
                ne_id = extract_ne_id(href)
                break
        if not ne_id:
            ne_id = extract_ne_id(audio_url) or extract_ne_id(image_url) or extract_ne_id(desc_html)
        if ne_id:
            items[ne_id] = {"title": title, "blocks": blocks, "audio_url": audio_url, "image_url": image_url, "original_link": original_link}
    return items
def extract_easy_article_links_from_sitemap(n=4):
    r = http_get(EASY_SITEMAP_URL)
    soup = BeautifulSoup(r.text, "xml")
    links = []
    seen = set()
    for loc in soup.find_all("loc"):
        url = (loc.get_text() or "").strip()
        if not url:
            continue
        parsed = urlparse(url)
        if "/news/easy/ne" not in parsed.path or not parsed.path.endswith(".html") or url in seen:
            continue
        seen.add(url)
        links.append(url)
        if len(links) >= n:
            break
    return links
def parse_article_from_nhk_easy(link: str):
    page = http_get(link)
    psoup = BeautifulSoup(page.text, "html.parser")
    title_tag = psoup.select_one("h1")
    title = ""
    title_html = ""
    if title_tag:
        title = title_tag.get_text(" ", strip=True)
        title_html = "".join(str(x) for x in title_tag.contents).strip() or title
    if not title:
        og_title = psoup.select_one('meta[property="og:title"]')
        if og_title:
            title = (og_title.get("content") or "").strip()
    if not title:
        title = "NHK Easy Article"
    if not title_html:
        title_html = title
    image_url = ""
    for sel in ['meta[property="og:image"]', 'meta[name="og:image"]', "article img[src]", "main img[src]", "img[src]"]:
        el = psoup.select_one(sel)
        if not el:
            continue
        candidate = (el.get("content") or el.get("src") or "").strip()
        if candidate:
            image_url = urljoin(link, candidate)
            break
    audio_url = ""
    for sel in ["audio source[src]", "audio[src]", 'a[href$=".mp3"]', 'a[href*=".mp3"]']:
        el = psoup.select_one(sel)
        if not el:
            continue
        candidate = (el.get("src") or el.get("href") or "").strip()
        if candidate:
            audio_url = urljoin(link, candidate)
            break
    if not audio_url:
        mp3_match = re.search(r"https?://[^\"'\s]+\.mp3(?:\?[^\"'\s]*)?", page.text)
        if mp3_match:
            audio_url = mp3_match.group(0)
    if not audio_url:
        audio_field_match = re.search(r'"(?:audio|voice|sound|movie)Url"\s*:\s*"([^"]+)"', page.text, re.IGNORECASE)
        if audio_field_match:
            audio_url = urljoin(link, audio_field_match.group(1))
    content = psoup.select_one(".article-main__body") or psoup.select_one(".module--content") or psoup.select_one("#js-article-body") or psoup.select_one(".content--detail-body") or psoup.select_one("article") or psoup.select_one("main")
    filtered_blocks = []
    if content is not None:
        for bad in content.select("script, style, nav, footer, header, aside, form"):
            bad.decompose()
        for b in get_article_blocks(content):
            t = b["text"]
            if "share" in t.lower() or "follow us" in t.lower():
                continue
            filtered_blocks.append(b)
    if not filtered_blocks:
        payload_texts = []
        for txt in re.findall(r'"children":"([^"]{10,}?)"', page.text):
            if "NHK" in txt or "トップ" in txt or "ニュース・防災" in txt:
                continue
            if not re.search(r"[ぁ-んァ-ン一-龯]", txt):
                continue
            cleaned = txt.replace("\\n", " ").strip()
            if len(cleaned) >= 10:
                payload_texts.append(cleaned)
        seen_text = set()
        for t in payload_texts:
            if t in seen_text:
                continue
            seen_text.add(t)
            filtered_blocks.append({"html": t, "text": t})
            if len(filtered_blocks) >= 8:
                break
    if not filtered_blocks:
        desc_meta = psoup.select_one('meta[name="description"]')
        desc = (desc_meta.get("content") or "").strip() if desc_meta else ""
        if desc:
            filtered_blocks.append({"html": desc, "text": desc})
    if not filtered_blocks:
        return None
    vocab = extract_vocab_from_blocks(filtered_blocks)
    translated_blocks = []
    for b in filtered_blocks:
        bg_tr = translate_text(b["text"], dest="bg") or b["text"]
        en_tr = translate_text(b["text"], dest="en") or b["text"]
        translated_blocks.append({"html": b["html"], "text": b["text"], "translation_bg": bg_tr, "translation_en": en_tr})
    return {"title": title, "title_html": title_html, "title_translation_bg": (translate_text(title, dest="bg") or title), "title_translation_en": (translate_text(title, dest="en") or title), "link": link, "image_url": image_url, "audio_url": audio_url, "blocks": translated_blocks, "vocab": vocab}
def get_articles(n=4):
    links = extract_easy_article_links_from_sitemap(max(n * 8, n))
    nhkeasier_items = {}
    try:
        nhkeasier_items = get_nhkeasier_items()
    except Exception as e:
        logger.warning("Could not load nhkeasier fallback feed: %s", e)
    articles = []
    for link in links:
        try:
            article = parse_article_from_nhk_easy(link)
            ne_id = extract_ne_id(link)
            fallback = nhkeasier_items.get(ne_id)
            if article and fallback and fallback.get("blocks"):
                article["blocks"] = []
                for b in fallback["blocks"]:
                    bg_tr = translate_text(b["text"], dest="bg") or b["text"]
                    en_tr = translate_text(b["text"], dest="en") or b["text"]
                    article["blocks"].append({"html": b["html"], "text": b["text"], "translation_bg": bg_tr, "translation_en": en_tr})
                article["vocab"] = extract_vocab_from_blocks(fallback["blocks"])
                if fallback.get("audio_url"):
                    article["audio_url"] = fallback["audio_url"]
                if fallback.get("image_url"):
                    article["image_url"] = fallback["image_url"]
                for b in fallback["blocks"]:
                    if "<ruby" in b["html"]:
                        article["title_html"] = b["html"]
                        break
            if article and article.get("blocks"):
                if not article.get("vocab"):
                    article["vocab"] = extract_vocab_from_blocks(article["blocks"])
                article.setdefault("image_url", "")
                article.setdefault("audio_url", "")
                articles.append(article)
                if len(articles) >= n:
                    break
            else:
                logger.info("Discarded article without content blocks: %s", link)
        except Exception as e:
            logger.warning("Skipping article %s because of error: %s", link, e)
            continue
    return articles[:n]
def wrap_vocab_words_in_html(html_fragment, vocab_items):
    if not html_fragment:
        return html_fragment

    soup = BeautifulSoup(html_fragment, "html.parser")
    vocab_lookup = {}
    for item in vocab_items or []:
        word = (item.get("word") or "").strip()
        reading = normalize_katakana_to_hiragana((item.get("reading") or "").strip())
        if word and not is_suspicious_vocab_word(word):
            register_vocab_item(vocab_lookup, item, extra_keys=build_lookup_candidates(word, reading=reading, lemma=word))

    if not vocab_lookup:
        return html_fragment

    # 1) Wrap ruby words first, so kanji + reading stay intact.
    for ruby in list(soup.find_all("ruby")):
        if ruby.find_parent(class_="dict-word"):
            continue

        base = ruby_base_text(ruby)
        ruby_reading = "".join(rt.get_text("", strip=True) for rt in ruby.find_all("rt"))
        okurigana = extract_following_okurigana(ruby)
        candidates = []
        if base and okurigana:
            surface = base + okurigana
            candidates.extend([surface, lemmatize_japanese(surface)])
        if base:
            candidates.append(base)

        item = None
        analysis = None
        for cand in unique_keep_order(candidates + build_lookup_candidates(base + okurigana if okurigana else base, reading=ruby_reading)):
            if cand in vocab_lookup:
                item = vocab_lookup[cand]
                analysis = analyze_japanese_word(base + okurigana if okurigana else base, reading_hint=(ruby_reading + okurigana).strip() if okurigana else ruby_reading, lemma_hint=(item.get("word") or "").strip())
                break
        if item is None:
            continue

        inner_html = str(ruby) + html_lib.escape(okurigana)
        span = make_dict_span(soup, item, inner_html, analysis=analysis)
        ruby.replace_with(span)

        nxt = span.next_sibling
        if isinstance(nxt, NavigableString) and okurigana and str(nxt).startswith(okurigana):
            rest = str(nxt)[len(okurigana):]
            nxt.replace_with(rest)

    # 2) Wrap remaining plain text by MeCab token boundaries, not raw substring search.
    tagger = get_mecab_tagger()
    skip_tags = {"rt", "rp", "script", "style"}

    for text_node in list(soup.find_all(string=True)):
        parent = getattr(text_node, "parent", None)
        if parent is None or getattr(parent, "name", None) in skip_tags:
            continue
        if parent.get("class") and "dict-word" in parent.get("class", []):
            continue

        original = str(text_node)
        if not original.strip():
            continue

        if tagger is None:
            continue

        try:
            tokens = list(tagger(original))
        except Exception:
            continue

        surfaces = [token_surface(t) for t in tokens]
        if not surfaces:
            continue

        # Only rewrite node if we actually match something.
        matched_any = False
        rebuilt = []
        i = 0
        while i < len(surfaces):
            best = None
            best_item = None
            best_analysis = None
            max_j = min(len(surfaces), i + 5)
            for j in range(max_j, i, -1):
                if not is_matchable_token_span(tokens[i:j]):
                    continue
                candidate = "".join(surfaces[i:j]).strip()
                candidate_reading = normalize_katakana_to_hiragana("".join(feature_reading(t).strip() for t in tokens[i:j]))
                lemma_joined = "".join((token_lemma(t).strip() or token_surface(t).strip()) for t in tokens[i:j]).strip()
                key_candidates = build_lookup_candidates(candidate, reading=candidate_reading, lemma=lemma_joined)
                matched_key = None
                for key in key_candidates:
                    if key in vocab_lookup and not is_suspicious_vocab_word(candidate):
                        matched_key = key
                        break
                if matched_key:
                    best = candidate
                    best_item = vocab_lookup[matched_key]
                    best_analysis = analyze_japanese_word(candidate, reading_hint=candidate_reading, lemma_hint=(best_item.get("word") or lemma_joined or candidate))
                    best_j = j
                    break
            if best is not None:
                matched_any = True
                rebuilt.append(make_dict_span(soup, best_item, html_lib.escape(best), analysis=best_analysis))
                i = best_j
            else:
                rebuilt.append(NavigableString(surfaces[i]))
                i += 1

        if matched_any:
            for node in rebuilt[::-1]:
                text_node.insert_after(node)
            text_node.extract()

    return "".join(str(x) for x in soup.contents)
def build_html(articles, grammar_points=None, build_version="", build_code=""):
    grammar_points = grammar_points or []
    html = """<!doctype html>
<html lang=\"ja\">
<head>
<meta charset=\"UTF-8\">
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">
<meta http-equiv=\"Cache-Control\" content=\"no-cache, no-store, must-revalidate\">
<meta http-equiv=\"Pragma\" content=\"no-cache\">
<meta http-equiv=\"Expires\" content=\"0\">
<meta http-equiv=\"refresh\" content=\"7200\">
<title>最新ニュース</title>
<meta name=\"theme-color\" content=\"#0f1115\">
<meta name=\"app-version\" content=\"{build_version}\">
<link rel=\"manifest\" href=\"manifest.webmanifest?v={build_version}\">
<link rel=\"icon\" type=\"image/x-icon\" href=\"favicon.ico?v={build_version}\">
<link rel=\"icon\" type=\"image/png\" sizes=\"16x16\" href=\"favicon-16x16.png?v={build_version}\">
<link rel=\"icon\" type=\"image/png\" sizes=\"32x32\" href=\"favicon-32x32.png?v={build_version}\">
<link rel=\"apple-touch-icon\" href=\"apple-touch-icon.png?v={build_version}\">
<style>
:root{--bg:#0f1115;--card:#171a21;--card2:#1d212b;--text:#e8ecf1;--muted:#aeb7c2;--accent:#8ab4ff;--border:#2a3040;--jp-panel:#12151c;--trans-text:#d2dae3;--popup:#202532;--jp-font:"Hiragino Mincho ProN","Hiragino Mincho Pro","Yu Mincho","MS PMincho",serif;--ui-font:system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif}
body.theme-light{--bg:#f7f7f5;--card:#ffffff;--card2:#f2f2ee;--text:#1d232a;--muted:#596572;--accent:#275cc7;--border:#d3d9e1;--jp-panel:#fcfcfb;--trans-text:#3c4652;--popup:#ffffff}
body.theme-sepia{--bg:#f3eadb;--card:#fbf4e7;--card2:#f4ead9;--text:#3c2f22;--muted:#6e5d4b;--accent:#8a5a22;--border:#d8c7b0;--jp-panel:#fffaf0;--trans-text:#4e3f31;--popup:#fffaf0}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--text);font-family:var(--ui-font);line-height:1.8}
.wrap{max-width:980px;margin:0 auto;padding:26px 16px 40px}
h1{margin:0 0 18px;color:var(--accent);font-size:2rem;text-align:center;font-family:var(--jp-font)}
.site-logo{display:block;width:100px;height:100px;object-fit:contain;margin:0 auto 14px auto}
.lang-top{max-width:260px;margin:0 auto 18px auto}
.lang-top select{width:100%;background:var(--card2);color:var(--text);border:1px solid var(--border);border-radius:12px;padding:10px 12px;font:inherit}
.lang-top .control-label{text-align:center}
.lang-hint{max-width:760px;margin:0 auto 10px auto;text-align:center;color:var(--muted);font-size:.95rem;line-height:1.6}
.update-hint{max-width:760px;margin:0 auto 10px auto;text-align:center;color:var(--muted);font-size:.95rem;line-height:1.6}
.author-info{max-width:760px;margin:0 auto 18px auto;text-align:center;color:var(--muted);font-size:.92rem;line-height:1.7;font-family:ui-monospace,SFMono-Regular,Menlo,Monaco,Consolas,"Liberation Mono","Courier New",monospace;white-space:pre-line}
.build-marker{max-width:760px;margin:20px auto 8px auto;text-align:center;color:var(--muted);font-size:.84rem;opacity:.9}
article{background:var(--card);border:1px solid var(--border);border-radius:18px;padding:22px;margin-bottom:24px}
h2{margin:0 0 6px;font-size:1.38rem;cursor:pointer;font-family:var(--jp-font)}
.article-image{width:100%;max-height:420px;object-fit:cover;border-radius:12px;border:1px solid var(--border);display:block;margin:10px 0 14px}
.title-translation{display:none;color:var(--muted);margin:0 0 14px}
.article-audio{width:100%;margin:0 0 10px}
.section-title{margin:18px 0 10px;font-size:1.05rem;color:var(--accent);font-weight:700}
.jp-block{background:var(--jp-panel);border:1px solid var(--border);border-radius:12px;padding:14px 16px;margin:12px 0 6px;font-size:1.08rem;font-family:var(--jp-font);word-break:break-word;overflow-wrap:anywhere}
.trans-block{color:var(--trans-text);padding:0 2px 8px 2px;margin-bottom:8px;border-bottom:1px dashed var(--border);display:none}
.trans-block.is-visible{display:block}
.grammar{background:var(--card);border:1px solid var(--border);border-radius:18px;padding:18px}
.grammar ul{list-style:none;padding:0;margin:10px 0 0}
.grammar li{padding:12px 14px;border:1px solid var(--border);border-radius:12px;background:var(--card2);margin-bottom:10px}
.grammar-rule{font-weight:700;color:var(--accent);font-family:var(--jp-font);display:block;margin-bottom:4px}
.downloads{display:flex;justify-content:center;gap:10px;flex-wrap:wrap;margin:22px 0}
.download-btn{display:inline-block;padding:10px 14px;border-radius:12px;border:1px solid var(--border);background:var(--card2);color:var(--text);text-decoration:none}
.contacts{text-align:center;color:var(--muted);margin-top:10px}
.bottom-controls{margin-top:22px;padding:14px;border:1px solid var(--border);border-radius:16px;background:var(--card)}
.control-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px}
.control-grid select{width:100%;background:var(--card2);color:var(--text);border:1px solid var(--border);border-radius:12px;padding:10px 12px;font:inherit}
.control-label{font-size:.92rem;color:var(--muted);margin-bottom:6px}
.dict-word{text-decoration:underline;text-decoration-thickness:1.5px;text-underline-offset:3px;cursor:pointer;border-radius:4px}
.dict-word.is-active{background:rgba(138,180,255,.18)}

.shadow-sentence{display:block;margin:2px 0;padding-left:10px}
.shadow-sentence.shadow-active{border-left:3px solid #ff7a00}

.dict-popup{position:fixed;z-index:9999;display:none;max-width:min(96vw,440px);background:var(--popup);color:var(--text);border:1px solid var(--border);border-radius:12px;padding:10px 12px;box-shadow:0 12px 32px rgba(0,0,0,.28)}
.dict-popup .dw{font-weight:700;font-size:1.08rem;font-family:var(--jp-font);line-height:1.6;white-space:normal;word-break:break-word}
.dict-popup .dr{color:var(--accent);font-size:.95rem;margin-top:2px}
.dict-popup .dm{color:var(--text);margin-top:6px;line-height:1.65;white-space:normal;word-break:break-word}
ruby rt{font-size:.68em;color:var(--muted)}
</style>
</head>
<body class=\"theme-dark\">
<div class=\"wrap\">
<img class=\"site-logo\" src=\"android-chrome-192x192.png?v={build_version}\" alt=\"NHK logo\" loading=\"lazy\">
<h1>最新ニュース</h1>
<div class=\"lang-top\">
  <div class=\"control-label\" data-ui=\"translation_language\"></div>
  <select id=\"lang-select\" onchange=\"setContentLanguage(this.value)\">
    <option value=\"bg\">🇧🇬 Български</option>
    <option value=\"en\">🇬🇧 English</option>
  </select>
</div>
<div class=\"lang-hint\" data-ui=\"help_hint\"></div>
<div class=\"update-hint\" data-ui=\"update_hint\"></div>
<div class=\"author-info\" data-bg=\"Създадено от Веселин Баев&#10;GitHub: vebaev&#10;Email: vebaev@gmail.com\" data-en=\"Created by Veselin Baev&#10;GitHub: vebaev&#10;Email: vebaev@gmail.com\"></div>
<div id=\"dict-popup\" class=\"dict-popup\" aria-hidden=\"true\"></div>
"""
    for idx, article in enumerate(articles, start=1):
        html += "<article>"
        num_map = {1:'1️⃣',2:'2️⃣',3:'3️⃣',4:'4️⃣'}
        prefix = num_map.get(idx, f'{idx}.')
        html += f"<h2 class='title-toggle'>{prefix} {article.get('title_html', article['title'])}</h2>"
        html += f"<div class='title-translation' data-bg='{html_lib.escape(article.get('title_translation_bg',''), quote=True)}' data-en='{html_lib.escape(article.get('title_translation_en',''), quote=True)}'></div>"
        if article.get("image_url"):
            html += f"<img class='article-image' src='{article['image_url']}' alt='{html_lib.escape(article['title'], quote=True)}' loading='lazy'/>"
        if article.get("audio_url"):
            html += f"<audio class='article-audio' controls preload='none' src='{article['audio_url']}'></audio>"
        html += "<div class='section-title' data-ui='text'></div>"
        for block in article["blocks"]:
            wrapped_html = wrap_vocab_words_in_html(block["html"], article.get("vocab", []))
            html += f"<div class='jp-block'>{wrapped_html}</div>"
            html += f"<div class='trans-block' data-bg='{html_lib.escape(block.get('translation_bg',''), quote=True)}' data-en='{html_lib.escape(block.get('translation_en',''), quote=True)}'></div>"
        html += "</article>"
    html += "<div class='downloads'>"
    html += f"<a class='download-btn download-link' data-kind='vocab_apkg' href='{DEFAULT_ANKI_APKG_FILENAME}' download></a>"
    html += f"<a class='download-btn download-link' data-kind='vocab_tsv' href='{DEFAULT_ANKI_FILENAME}' download></a>"
    html += f"<a class='download-btn download-link' data-kind='grammar_apkg' href='{DEFAULT_GRAMMAR_APKG_FILENAME}' download></a>"
    html += f"<a class='download-btn download-link' data-kind='grammar_tsv' href='{DEFAULT_GRAMMAR_TSV_FILENAME}' download></a>"
    html += "</div>"
    if grammar_points:
        html += "<section class='grammar'><div class='section-title' data-ui='grammar_in_texts'></div><ul>"
        for g in grammar_points:
            html += f"<li><span class='grammar-rule'>{g['label']}</span><span class='grammar-expl' data-bg='{html_lib.escape(g.get('explanation_bg',''), quote=True)}' data-en='{html_lib.escape(g.get('explanation_en',''), quote=True)}'></span></li>"
        html += "</ul></section>"
    html += """
<div class='bottom-controls'>
  <div class='control-grid'>
    <div><div class='control-label' data-ui='theme'></div><select id='theme-select' onchange='setTheme(this.value)'><option value='theme-dark'>Dark</option><option value='theme-sepia'>Sepia</option><option value='theme-light'>Light</option></select></div>
    <div><div class='control-label' data-ui='japanese_font'></div><select id='font-select' onchange='setJapaneseFont(this.value)'><option value='mincho'>Mincho</option><option value='gothic'>Gothic</option></select></div>
  </div>
</div>
<div class='contacts'>vebaev.github.io</div>
</div>
<script>
const UI_TEXT={bg:{text:"Текст",grammar_in_texts:"Граматика в текстовете",theme:"Тема",japanese_font:"Японски шрифт",translation_language:"Език",help_hint:"ℹ️ Кликни върху абзац за превод или върху дума за значение.",update_hint:"⏱️ Новините се обновяват веднъж дневно около 14:00 ч. българско време (12:00 UTC).",vocab_apkg:"Свали Anki речник (.apkg)",vocab_tsv:"Свали речник TSV",grammar_apkg:"Свали Anki граматика (.apkg)",grammar_tsv:"Свали граматика TSV"},en:{text:"Text",grammar_in_texts:"Grammar in the texts",theme:"Theme",japanese_font:"Japanese font",translation_language:"Language",help_hint:"ℹ️ Click a paragraph for translation or a word for its meaning.",update_hint:"⏱️ News updates once daily around 14:00 Bulgarian time (12:00 UTC).",vocab_apkg:"Download Anki vocabulary (.apkg)",vocab_tsv:"Download vocabulary TSV",grammar_apkg:"Download Anki grammar (.apkg)",grammar_tsv:"Download grammar TSV"}};
const FILES={bg:{vocab_apkg:"nhk_easy_vocab_bg.apkg",vocab_tsv:"anki_cards_bg.tsv",grammar_apkg:"nhk_easy_grammar_bg.apkg",grammar_tsv:"anki_grammar_bg.tsv"},en:{vocab_apkg:"nhk_easy_vocab_en.apkg",vocab_tsv:"anki_cards_en.tsv",grammar_apkg:"nhk_easy_grammar_en.apkg",grammar_tsv:"anki_grammar_en.tsv"}};
function getContentLanguage(){return localStorage.getItem('nhk_content_lang')||'bg';}
function loadPrefs(){const theme=localStorage.getItem('nhk_theme')||'theme-dark';document.body.className=theme;const themeSel=document.getElementById('theme-select');if(themeSel)themeSel.value=theme;const jpFont=localStorage.getItem('nhk_jp_font')||'mincho';applyJapaneseFont(jpFont);const fontSel=document.getElementById('font-select');if(fontSel)fontSel.value=jpFont;const lang=getContentLanguage();const langSel=document.getElementById('lang-select');if(langSel)langSel.value=lang;applyContentLanguage(lang);}
function setTheme(theme){document.body.className=theme;localStorage.setItem('nhk_theme',theme);const meta=document.querySelector('meta[name="theme-color"]');if(meta){meta.setAttribute('content',theme==='theme-light'?'#f7f7f5':theme==='theme-sepia'?'#f3eadb':'#0f1115');}}
function applyJapaneseFont(kind){const font=kind==='gothic'?'"Hiragino Kaku Gothic ProN","Yu Gothic","Meiryo",sans-serif':'"Hiragino Mincho ProN","Hiragino Mincho Pro","Yu Mincho","MS PMincho",serif';document.documentElement.style.setProperty('--jp-font',font);}
function setJapaneseFont(kind){localStorage.setItem('nhk_jp_font',kind);applyJapaneseFont(kind);}
function setContentLanguage(lang){localStorage.setItem('nhk_content_lang',lang);applyContentLanguage(lang);closeDictPopup();}
function applyContentLanguage(lang){document.querySelectorAll('[data-ui]').forEach(el=>{const key=el.dataset.ui;if(UI_TEXT[lang]&&UI_TEXT[lang][key])el.textContent=UI_TEXT[lang][key];});document.querySelectorAll('.title-translation,.trans-block,.grammar-expl,.author-info').forEach(el=>{el.textContent=el.dataset[lang]||'';});document.querySelectorAll('.download-link').forEach(el=>{const kind=el.dataset.kind;el.textContent=UI_TEXT[lang][kind]||kind;el.setAttribute('href',FILES[lang][kind]);});}
function closeDictPopup(){const popup=document.getElementById('dict-popup');if(!popup)return;popup.style.display='none';popup.setAttribute('aria-hidden','true');document.querySelectorAll('.dict-word.is-active').forEach(el=>el.classList.remove('is-active'));}
function positionPopupNear(el,popup){const rect=el.getBoundingClientRect();popup.style.display='block';popup.setAttribute('aria-hidden','false');const popupRect=popup.getBoundingClientRect();let top=rect.bottom+8;let left=rect.left;if(left+popupRect.width>window.innerWidth-8)left=window.innerWidth-popupRect.width-8;if(left<8)left=8;if(top+popupRect.height>window.innerHeight-8)top=rect.top-popupRect.height-8;if(top<8)top=8;popup.style.left=left+'px';popup.style.top=top+'px';}
function showDictPopup(el){const popup=document.getElementById('dict-popup');if(!popup)return;const alreadyActive=el.classList.contains('is-active');closeDictPopup();if(alreadyActive)return;const lang=getContentLanguage();const surface=(el.dataset.surface||'').trim();const lemma=(el.dataset.lemma||surface).trim();const rs=(el.dataset.readingSurface||'').trim();const rl=(el.dataset.readingLemma||'').trim();const form=(lang==='en'?el.dataset.formEn:el.dataset.formBg)||el.dataset.formBg||el.dataset.formEn||(lang==='en'?'form in context':'форма в текста');const ms=(lang==='en'?el.dataset.meaningSurfaceEn:el.dataset.meaningSurfaceBg)||el.dataset.meaningSurfaceBg||el.dataset.meaningSurfaceEn||(lang==='en'?'No translation found':'Няма намерен превод');const ml=(lang==='en'?el.dataset.meaningLemmaEn:el.dataset.meaningLemmaBg)||el.dataset.meaningLemmaBg||el.dataset.meaningLemmaEn||ms;const labelForm=(lang==='en'?'Form':'Форма');const line1=surface+(rs?' ['+rs+']':'')+' - '+ms;const line2=labelForm+': '+form;const line3=lemma+(rl?' ['+rl+']':'')+' - '+ml;const sameLemma=(lemma===surface);let html='<div class="dw">'+line1+'</div><div class="dm">'+line2+'</div>';if(!sameLemma){html+='<div class="dm">'+line3+'</div>';}popup.innerHTML=html;el.classList.add('is-active');positionPopupNear(el,popup);}


function splitSentenceParts(text){
  return (text || '').split(/(?<=[。！？?!])\s*/).filter(function(s){return s && s.trim();});
}

function wrapBlockSentences(block){
  if(!block) return [];
  if(block.dataset.shadowPrepared === '1'){
    return Array.from(block.querySelectorAll('.shadow-sentence'));
  }

  const originalNodes = Array.from(block.childNodes);
  const frag = document.createDocumentFragment();
  let current = document.createElement('span');
  current.className = 'shadow-sentence';

  function flushCurrent(){
    if(!current.childNodes.length) return;
    frag.appendChild(current);
    current = document.createElement('span');
    current.className = 'shadow-sentence';
  }

  function appendSplitText(txt){
    const parts = splitSentenceParts(txt);
    if(!parts.length){
      if(txt) current.appendChild(document.createTextNode(txt));
      return;
    }
    parts.forEach(function(part){
      current.appendChild(document.createTextNode(part));
      if(/[。！？?!]\s*$/.test(part)){
        flushCurrent();
      }
    });
  }

  originalNodes.forEach(function(node){
    if(node.nodeType === Node.TEXT_NODE){
      appendSplitText(node.textContent || '');
    } else {
      const clone = node.cloneNode(true);
      current.appendChild(clone);
      const t = (current.textContent || '').trim();
      if(/[。！？?!]\s*$/.test(t)){
        flushCurrent();
      }
    }
  });

  flushCurrent();
  block.innerHTML = '';
  block.appendChild(frag);
  block.dataset.shadowPrepared = '1';
  return Array.from(block.querySelectorAll('.shadow-sentence'));
}

function sentenceWeight(text){
  let score = 0;
  for(const ch of (text || '')){
    if(/[一-龯]/.test(ch)) score += 1.8;
    else if(/[ぁ-ゖ]/.test(ch)) score += 1.1;
    else if(/[ァ-ヺー]/.test(ch)) score += 1.2;
    else if(/[、]/.test(ch)) score += 0.6;
    else if(/[。！？?!]/.test(ch)) score += 0.8;
    else score += 0.9;
  }
  return Math.max(score, 1);
}

function setupArticleShadowing(article){
  const audio = article.querySelector('.article-audio');
  if(!audio) return;

  const sentenceEls = [];
  article.querySelectorAll('.jp-block').forEach(function(block){
    wrapBlockSentences(block).forEach(function(el){ sentenceEls.push(el); });
  });
  if(!sentenceEls.length) return;

  let timings = [];

  function buildTimings(){
    const duration = audio.duration || 0;
    if(!duration || !isFinite(duration)) return;
    const weights = sentenceEls.map(function(el){ return sentenceWeight((el.textContent || '').trim()); });
    const total = weights.reduce(function(a,b){ return a+b; }, 0) || 1;
    let acc = 0;
    timings = weights.map(function(w, idx){
      const start = acc;
      acc += duration * (w / total);
      return { index: idx, start: start, end: acc };
    });
    if(timings.length){
      timings[0].start = 0;
      timings[timings.length - 1].end = duration;
    }
  }

  function clearActive(){
    sentenceEls.forEach(function(el){ el.classList.remove('shadow-active'); });
  }

  function updateHighlight(){
    if(!timings.length) buildTimings();
    if(!timings.length) return;
    const t = audio.currentTime || 0;
    let current = timings.find(function(seg){ return t >= seg.start && t < seg.end; });
    if(!current) current = timings[timings.length - 1];
    if(!current) return;
    clearActive();
    const el = sentenceEls[current.index];
    if(el) el.classList.add('shadow-active');
  }

  audio.addEventListener('loadedmetadata', buildTimings);
  audio.addEventListener('canplay', buildTimings);
  audio.addEventListener('play', updateHighlight);
  audio.addEventListener('timeupdate', updateHighlight);
  audio.addEventListener('seeked', updateHighlight);
  audio.addEventListener('pause', updateHighlight);
  audio.addEventListener('ended', clearActive);
}

function forceFreshReloadCheck(){fetch(window.location.pathname + '?v=' + encodeURIComponent(document.querySelector('meta[name="app-version"]')?.content || Date.now()), {cache:'no-store'}).then(r=>r.text()).then(html=>{const m=html.match(/<meta name=\"app-version\" content=\"([^\"]+)\"/);const current=document.querySelector('meta[name="app-version"]')?.content||'';if(m&&m[1]&&m[1]!==current){window.location.reload();}}).catch(function(){});}
document.addEventListener('DOMContentLoaded',function(){loadPrefs();document.querySelectorAll('article').forEach(function(article){setupArticleShadowing(article);});if('serviceWorker' in navigator){navigator.serviceWorker.register('./sw.js?v='+encodeURIComponent(document.querySelector('meta[name="app-version"]')?.content || '')).then(function(reg){if(reg&&reg.update){reg.update();}}).catch(function(){});}forceFreshReloadCheck();setInterval(forceFreshReloadCheck,120000);document.querySelectorAll('.title-toggle').forEach(function(title){title.addEventListener('click',function(){const tr=title.nextElementSibling;if(!tr||!tr.classList.contains('title-translation'))return;tr.style.display=tr.style.display==='block'?'none':'block';});});document.querySelectorAll('.dict-word').forEach(function(el){el.addEventListener('click',function(event){event.stopPropagation();showDictPopup(el);});});document.addEventListener('click',function(){closeDictPopup();});document.querySelectorAll('.jp-block + .trans-block').forEach(function(trBlock){const jpBlock=trBlock.previousElementSibling;if(!jpBlock)return;jpBlock.style.cursor='pointer';jpBlock.addEventListener('click',function(event){if(event.target.closest('.dict-word'))return;trBlock.classList.toggle('is-visible');});});});
</script>
</body>
</html>"""
    return html

def write_pwa_files(output_dir, build_version=""):
    if not output_dir:
        return
    manifest = {
        "name": "NHK Easy News",
        "id": f"./?v={build_version}",
        "short_name": "NHK Easy",
        "start_url": f"./index.html?v={build_version}",
        "display": "standalone",
        "background_color": "#0f1115",
        "theme_color": "#0f1115",
        "icons": [
            {"src": "android-chrome-192x192.png", "sizes": "192x192", "type": "image/png"},
            {"src": "android-chrome-512x512.png", "sizes": "512x512", "type": "image/png"},
            {"src": "apple-touch-icon.png", "sizes": "180x180", "type": "image/png"}
        ]
    }
    with open(os.path.join(output_dir, "manifest.webmanifest"), "w", encoding="utf-8") as f:
        json.dump(manifest, f, ensure_ascii=False, indent=2)
    sw_js = "const CACHE_NAME='nhk-easy-'+(%r||Date.now());\nself.addEventListener('install',e=>{self.skipWaiting();});\nself.addEventListener('activate',e=>{e.waitUntil(caches.keys().then(keys=>Promise.all(keys.filter(k=>k!==CACHE_NAME).map(k=>caches.delete(k)))).then(()=>self.clients.claim()));});\nself.addEventListener('fetch',e=>{if(e.request.method!==\'GET\')return;e.respondWith(fetch(e.request,{cache:\'no-store\'}).catch(()=>caches.match(e.request)));});" % build_version
    with open(os.path.join(output_dir, "sw.js"), "w", encoding="utf-8") as f:
        f.write(sw_js)

def main():
    global DEEPL_API_KEY
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument("--count", type=int, default=4)
    parser.add_argument("--deepl-key", default=os.environ.get("DEEPL_API_KEY", ""))
    parser.add_argument("--translation-cache", default=os.environ.get("TRANSLATION_CACHE_PATH", ""))
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()

    configure_logging(args.verbose)
    DEEPL_API_KEY = (args.deepl_key or "").strip()
    build_version = str(int(time.time()))
    build_code = build_version[-4:] if len(build_version) >= 4 else build_version
    output_dir = os.path.dirname(args.output)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)
        write_pwa_files(output_dir, build_version=build_version)

    cache_path = (args.translation_cache or "").strip()
    if not cache_path:
        cache_path = os.path.join(output_dir or os.getcwd(), "translations_cache.json")
    set_translation_cache_path(cache_path)
    load_translation_cache()

    ensure_grammar_bilingual()
    articles = get_articles(args.count)
    if not articles:
        raise RuntimeError("No articles were extracted.")

    grammar_points = extract_grammar_points(articles)

    vocab_tsv_filename = DEFAULT_ANKI_FILENAME
    vocab_apkg_filename = DEFAULT_ANKI_APKG_FILENAME
    grammar_tsv_filename = DEFAULT_GRAMMAR_TSV_FILENAME
    grammar_apkg_filename = DEFAULT_GRAMMAR_APKG_FILENAME
    vocab_tsv_en_filename = DEFAULT_ANKI_EN_FILENAME
    vocab_apkg_en_filename = DEFAULT_ANKI_EN_APKG_FILENAME
    grammar_tsv_en_filename = DEFAULT_GRAMMAR_EN_TSV_FILENAME
    grammar_apkg_en_filename = DEFAULT_GRAMMAR_EN_APKG_FILENAME
    anki_seen_words_filename = DEFAULT_ANKI_SEEN_WORDS_FILENAME

    if output_dir:
        vocab_tsv_path = os.path.join(output_dir, vocab_tsv_filename)
        vocab_apkg_path = os.path.join(output_dir, vocab_apkg_filename)
        grammar_tsv_path = os.path.join(output_dir, grammar_tsv_filename)
        grammar_apkg_path = os.path.join(output_dir, grammar_apkg_filename)
        vocab_tsv_en_path = os.path.join(output_dir, vocab_tsv_en_filename)
        vocab_apkg_en_path = os.path.join(output_dir, vocab_apkg_en_filename)
        grammar_tsv_en_path = os.path.join(output_dir, grammar_tsv_en_filename)
        grammar_apkg_en_path = os.path.join(output_dir, grammar_apkg_en_filename)
        anki_seen_words_path = os.path.join(output_dir, anki_seen_words_filename)
    else:
        vocab_tsv_path = vocab_tsv_filename
        vocab_apkg_path = vocab_apkg_filename
        grammar_tsv_path = grammar_tsv_filename
        grammar_apkg_path = grammar_apkg_filename
        vocab_tsv_en_path = vocab_tsv_en_filename
        vocab_apkg_en_path = vocab_apkg_en_filename
        grammar_tsv_en_path = grammar_tsv_en_filename
        grammar_apkg_en_path = grammar_apkg_en_filename
        anki_seen_words_path = anki_seen_words_filename

    seen_words = load_seen_words(anki_seen_words_path)
    add_known_progress_to_articles(articles, seen_words)

    vocab_cards = build_vocab_anki_cards(articles, lang="bg")
    vocab_cards_en = build_vocab_anki_cards(articles, lang="en")
    grammar_cards = build_grammar_anki_cards(grammar_points, lang="bg")
    grammar_cards_en = build_grammar_anki_cards(grammar_points, lang="en")

    save_anki_tsv(vocab_cards, vocab_tsv_path)
    save_anki_tsv(vocab_cards_en, vocab_tsv_en_path)
    save_anki_tsv(grammar_cards, grammar_tsv_path)
    save_anki_tsv(grammar_cards_en, grammar_tsv_en_path)

    build_anki_apkg(vocab_cards, vocab_apkg_path, deck_name="NHK Easy Vocabulary BG")
    build_anki_apkg(vocab_cards_en, vocab_apkg_en_path, deck_name="NHK Easy Vocabulary EN")
    build_anki_apkg(grammar_cards, grammar_apkg_path, deck_name="NHK Easy Grammar BG")
    build_anki_apkg(grammar_cards_en, grammar_apkg_en_path, deck_name="NHK Easy Grammar EN")

    save_seen_words(anki_seen_words_path, seen_words)

    html = build_html(articles, grammar_points=grammar_points, build_version=build_version, build_code=build_code)
    with open(args.output, "w", encoding="utf-8") as f:
        f.write(html)

    save_translation_cache(force=True)
    logger.info("Translation stats: %s", _TRANSLATION_STATS)

if __name__ == "__main__":
    main()

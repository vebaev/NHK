import os
import re
import argparse
import html as html_lib
import hashlib
import json
import uuid
from urllib.parse import urljoin, urlparse
import requests
from bs4 import BeautifulSoup
from googletrans import Translator
try:
    import fugashi
except Exception:
    fugashi = None
try:
    import genanki
except Exception:
    genanki = None

EASY_INDEX_URL = "https://news.web.nhk/news/easy/"
EASY_SITEMAP_URL = "https://news.web.nhk/news/easy/sitemap/sitemap.xml"
NHKEASIER_FEED_URL = "https://nhkeasier.com/feed/"
DEFAULT_OUTPUT = "docs/index.html"
DEFAULT_ANKI_FILENAME = "anki_cards.tsv"
DEFAULT_ANKI_APKG_FILENAME = "nhk_easy_vocab.apkg"
DEFAULT_ANKI_SEEN_WORDS_FILENAME = "anki_seen_words.json"

translator = Translator()
DEEPL_API_KEY = os.environ.get("DEEPL_API_KEY", "").strip()
_TRANSLATION_CACHE = {}
_TRANSLATION_STATS = {"deepl": 0, "google": 0}
PARTICLE_PREFIXES = ("が", "を", "に", "で", "は", "と", "へ", "や", "も", "の")
GODAN_I_TO_U = {
    "い": "う",
    "き": "く",
    "ぎ": "ぐ",
    "し": "す",
    "ち": "つ",
    "に": "ぬ",
    "び": "ぶ",
    "み": "む",
    "り": "る",
}
GODAN_A_TO_U = {
    "わ": "う",
    "か": "く",
    "が": "ぐ",
    "さ": "す",
    "た": "つ",
    "な": "ぬ",
    "ば": "ぶ",
    "ま": "む",
    "ら": "る",
}
_MECAB_TAGGER = None
GRAMMAR_RULES = [
    {
        "id": "te_iru",
        "label": "〜ている / 〜ています",
        "regex": re.compile(r"てい(?:る|ます|て|た|ました)"),
        "explanation": "Продължително действие или състояние.",
    },
    {
        "id": "te_ita",
        "label": "〜ていた / 〜ていました",
        "regex": re.compile(r"てい(?:た|ました)"),
        "explanation": "Продължително действие/състояние в миналото.",
    },
    {
        "id": "nai",
        "label": "〜ない",
        "regex": re.compile(r"[ぁ-んァ-ン一-龯]ない"),
        "explanation": "Отрицателна форма (не правя/няма).",
    },
    {
        "id": "kamoshirenai",
        "label": "〜かもしれない",
        "regex": re.compile(r"かもしれない"),
        "explanation": "Вероятност: „може би...“.",
    },
    {
        "id": "koto_ga_dekiru",
        "label": "〜ことができる",
        "regex": re.compile(r"ことができ(?:る|ます|た|ました)"),
        "explanation": "Възможност/умение: „мога да...“.",
    },
    {
        "id": "koto_ni_naru",
        "label": "〜ことになる",
        "regex": re.compile(r"ことにな(?:る|り|った|ります|りました)"),
        "explanation": "Решение/резултат: „оказва се, че... / решено е да...“.",
    },
    {
        "id": "you_ni",
        "label": "〜ように",
        "regex": re.compile(r"ように"),
        "explanation": "Цел или начин: „за да... / така че...“.",
    },
    {
        "id": "tame_ni",
        "label": "〜ため(に)",
        "regex": re.compile(r"ため(?:に)?"),
        "explanation": "Причина или цел: „поради... / за да...“.",
    },
    {
        "id": "nagara",
        "label": "〜ながら",
        "regex": re.compile(r"ながら"),
        "explanation": "Едновременно действие: „докато...“.",
    },
    {
        "id": "tari_tari",
        "label": "〜たり〜たりする",
        "regex": re.compile(r"たり.*たり"),
        "explanation": "Непълен списък от действия: „... и ... и т.н.“.",
    },
    {
        "id": "te_shimau",
        "label": "〜てしまう",
        "regex": re.compile(r"てしま(?:う|います|った|いました)"),
        "explanation": "Завършеност или нежелан резултат.",
    },
    {
        "id": "to_omou",
        "label": "〜と思う",
        "regex": re.compile(r"と思(?:う|います|った|いました)"),
        "explanation": "Мнение/мисъл: „мисля, че...“.",
    },
    {
        "id": "to_iu",
        "label": "〜という",
        "regex": re.compile(r"という"),
        "explanation": "Назоваване/цитиране: „наречен... / че...“.",
    },
    {
        "id": "passive_rareru",
        "label": "受け身 (〜られる)",
        "regex": re.compile(r"[ぁ-んァ-ン一-龯]られ(?:る|ます|た|ました)"),
        "explanation": "Страдателен залог: „бива направено...“.",
    },
    {
        "id": "causative_saseru",
        "label": "使役 (〜させる)",
        "regex": re.compile(r"[ぁ-んァ-ン一-龯]させ(?:る|ます|た|ました)"),
        "explanation": "Каузатив: „карам/оставям някого да...“.",
    },
    {
        "id": "kara_reason",
        "label": "〜から",
        "regex": re.compile(r"から"),
        "explanation": "Причина или отправна точка („защото/от“ според контекста).",
    },
    {
        "id": "made",
        "label": "〜まで",
        "regex": re.compile(r"まで"),
        "explanation": "Граница във време/място: „до“.",
    },
    {
        "id": "ni",
        "label": "〜に",
        "regex": re.compile(r"に"),
        "explanation": "Частица за посока, време, цел или непряк обект.",
    },
]


def translate_text(text: str, dest: str = "bg") -> str:
    text = (text or "").strip()
    if not text:
        return ""
    cache_key = (text, dest, bool(DEEPL_API_KEY))
    if cache_key in _TRANSLATION_CACHE:
        return _TRANSLATION_CACHE[cache_key]

    if DEEPL_API_KEY:
        try:
            # Free plan ключовете обикновено завършват с :fx
            deepl_url = "https://api-free.deepl.com/v2/translate"
            if not DEEPL_API_KEY.endswith(":fx"):
                deepl_url = "https://api.deepl.com/v2/translate"

            target_lang = dest.upper()
            if target_lang == "BG":
                target_lang = "BG"

            resp = requests.post(
                deepl_url,
                headers={
                    "Authorization": f"DeepL-Auth-Key {DEEPL_API_KEY}",
                },
                data={
                    "text": text,
                    "target_lang": target_lang,
                },
                timeout=20,
            )
            resp.raise_for_status()
            data = resp.json()
            translations = data.get("translations") or []
            if translations and translations[0].get("text"):
                result = translations[0]["text"].strip()
                _TRANSLATION_STATS["deepl"] += 1
                _TRANSLATION_CACHE[cache_key] = result
                return result
        except Exception:
            # fallback към googletrans
            pass

    try:
        result = translator.translate(text, dest=dest).text
        _TRANSLATION_STATS["google"] += 1
        _TRANSLATION_CACHE[cache_key] = result
        return result
    except Exception:
        return ""


def get_article_blocks(content):
    blocks = []

    for el in content.find_all(["p", "h2", "h3", "li"], recursive=True):
        txt = el.get_text(" ", strip=True)
        if not txt:
            continue

        # махаме прекалено кратки / шумни редове
        if len(txt) < 3:
            continue

        blocks.append({
            "text": txt,
            "html": "".join(str(x) for x in el.contents).strip()
        })

    return blocks


def extract_vocab_from_blocks(blocks):
    vocab_map = {}

    for block in blocks:
        soup = BeautifulSoup(block["html"], "html.parser")
        rubies = soup.find_all("ruby")

        for ruby in rubies:
            rb_text = ""
            rt_text = ""

            # взимаме kanji/base text
            for child in ruby.contents:
                name = getattr(child, "name", None)
                if name == "rt":
                    rt_text += child.get_text("", strip=True)
                elif name == "rp":
                    continue
                else:
                    if hasattr(child, "get_text"):
                        rb_text += child.get_text("", strip=True)
                    else:
                        rb_text += str(child).strip()

            rb_text = rb_text.strip()
            rt_text = rt_text.strip()

            if not rb_text:
                continue

            # пропускаме чиста хирагана/катакана
            if not re.search(r"[一-龯]", rb_text):
                continue

            okurigana = extract_following_okurigana(ruby)
            word = rb_text
            reading = rt_text

            # Ако след канджи има частица, не я включваме в речниковата форма
            if okurigana and okurigana.startswith(PARTICLE_PREFIXES):
                okurigana = ""

            if okurigana:
                surface_word = rb_text + okurigana
                surface_reading = (rt_text + okurigana).strip()
                word = lemmatize_japanese(surface_word)
                reading = to_dictionary_form(surface_reading)

            if word not in vocab_map:
                vocab_map[word] = reading

    vocab = []
    for word, reading in vocab_map.items():
        meaning = translate_text(word, dest="bg")
        vocab.append({
            "word": word,
            "reading": reading,
            "meaning": meaning
        })

    return vocab[:20]


def is_single_kanji_word(word: str) -> bool:
    w = (word or "").strip()
    return bool(re.fullmatch(r"[一-龯]", w))


def is_known_vocab_item(word: str, known_items):
    return word in known_items or f"v:{word}" in known_items


def build_anki_cards(articles, grammar_points=None, seen_items=None):
    cards = []
    seen = set()
    known = set(seen_items or [])
    newly_added_items = set()

    for article in articles:
        for item in article.get("vocab", []):
            word = (item.get("word") or "").strip()
            reading = (item.get("reading") or "").strip()
            meaning = (item.get("meaning") or "").strip()
            if not word or not meaning:
                continue
            if is_single_kanji_word(word):
                continue
            if word in seen:
                continue
            if is_known_vocab_item(word, known):
                continue
            seen.add(word)
            newly_added_items.add(f"v:{word}")

            if reading and reading != word:
                front = f"<ruby>{word}<rt>{reading}</rt></ruby>"
            else:
                front = word
            back = meaning
            cards.append((front, back))

    for g in grammar_points or []:
        label = (g.get("label") or "").strip()
        explanation = (g.get("explanation") or "").strip()
        if not label or not explanation:
            continue
        grammar_key = f"g:{label}"
        if grammar_key in known:
            continue
        newly_added_items.add(grammar_key)
        cards.append((f"Граматика: {label}", explanation))

    return cards, newly_added_items


def load_seen_words(path):
    if not os.path.exists(path):
        return set()
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, list):
            return set()
        return {str(x).strip() for x in data if str(x).strip()}
    except Exception:
        return set()


def save_seen_words(path, words):
    unique_sorted_words = sorted({w.strip() for w in words if w and w.strip()})
    with open(path, "w", encoding="utf-8") as f:
        json.dump(unique_sorted_words, f, ensure_ascii=False, indent=2)


def add_known_progress_to_articles(articles, known_words):
    known = set(known_words or [])
    for article in articles:
        vocab_words = []
        seen_in_article = set()
        for item in article.get("vocab", []):
            word = (item.get("word") or "").strip()
            if not word:
                continue
            if is_single_kanji_word(word):
                continue
            if word in seen_in_article:
                continue
            seen_in_article.add(word)
            vocab_words.append(word)

        total = len(vocab_words)
        known_count = sum(1 for w in vocab_words if is_known_vocab_item(w, known))
        percent = int(round((known_count / total) * 100)) if total else 0
        article["known_total"] = total
        article["known_count"] = known_count
        article["known_percent"] = percent


def save_anki_tsv(cards, path):
    with open(path, "w", encoding="utf-8") as f:
        for front, back in cards:
            # TAB-separated, съвместимо с Anki import
            f.write(f"{front}\t{back}\n")


def split_japanese_sentences(text: str):
    t = (text or "").strip()
    if not t:
        return []
    parts = re.split(r"(?<=[。！？])\s*", t)
    return [p.strip() for p in parts if p.strip()]


def extract_grammar_points(articles):
    found = {}

    for article in articles:
        for block in article.get("blocks", []):
            sentences = split_japanese_sentences(block.get("text", ""))
            for sentence in sentences:
                for rule in GRAMMAR_RULES:
                    if rule["id"] in found:
                        continue
                    if rule["regex"].search(sentence):
                        found[rule["id"]] = {
                            "label": rule["label"],
                            "explanation": rule["explanation"],
                        }

    ordered = []
    for rule in GRAMMAR_RULES:
        item = found.get(rule["id"])
        if item:
            ordered.append(item)
    return ordered


def stable_int_id(seed: str, digits: int = 10) -> int:
    # genanki изисква integer ids; правим стабилен id от текстов seed
    digest = hashlib.sha1(seed.encode("utf-8")).hexdigest()
    h = int(digest[:12], 16)
    mod = 10 ** digits
    return (h % mod) + (10 ** (digits - 1))


def build_anki_apkg(cards, apkg_path, deck_name="NHK Easy Vocabulary"):
    if genanki is None:
        print("genanki is not installed; skipping .apkg generation")
        return False

    model_id = stable_int_id("nhk_easy_vocab_model")
    deck_id = stable_int_id("nhk_easy_vocab_deck")

    model = genanki.Model(
        model_id,
        "NHK Easy Vocab Model",
        fields=[
            {"name": "Front"},
            {"name": "Back"},
        ],
        templates=[
            {
                "name": "Card 1",
                "qfmt": "<div class='jp-word'>{{Front}}</div>",
                "afmt": "<div class='jp-word'>{{Front}}</div><hr id='answer'><div class='bg-meaning'>{{Back}}</div>",
            }
        ],
        css="""
.card {
  font-family: Arial, sans-serif;
  font-size: 25px;
  text-align: center;
  color: black;
  background-color: white;
}
.jp-word {
  font-size: 31px;
}
.bg-meaning {
  font-size: 25px;
}
.jp-word ruby rt {
  font-size: 14px;
}
""",
    )

    deck = genanki.Deck(deck_id, deck_name)
    for front, back in cards:
        note = genanki.Note(
            model=model,
            fields=[front, back],
            guid=uuid.uuid4().hex,
        )
        deck.add_note(note)

    genanki.Package(deck).write_to_file(apkg_path)
    return True


def get_mecab_tagger():
    global _MECAB_TAGGER
    if _MECAB_TAGGER is not None:
        return _MECAB_TAGGER
    if fugashi is None:
        return None
    try:
        _MECAB_TAGGER = fugashi.Tagger()
    except Exception:
        _MECAB_TAGGER = None
    return _MECAB_TAGGER


def is_target_pos(token) -> bool:
    # UniDic/BCCWJ полетата не са напълно стабилни между версии, затова
    # проверяваме както feature.pos1, така и fallback към string representation.
    feature = getattr(token, "feature", None)
    pos1 = getattr(feature, "pos1", "") if feature is not None else ""
    if pos1 in {"動詞", "形容詞"}:
        return True
    return "動詞" in str(feature) or "形容詞" in str(feature)


def token_lemma(token) -> str:
    feature = getattr(token, "feature", None)
    if feature is None:
        return ""

    lemma = getattr(feature, "lemma", "") or ""
    if not lemma:
        # някои версии използват други полета
        lemma = getattr(feature, "dictionary_form", "") or ""
    if not lemma:
        lemma = getattr(feature, "lemma_form", "") or ""
    return lemma.strip()


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
    except Exception:
        pass

    return to_dictionary_form(w)


def extract_following_okurigana(ruby_tag):
    sibling = ruby_tag.next_sibling
    while sibling is not None:
        txt = ""
        if isinstance(sibling, str):
            txt = sibling
        elif hasattr(sibling, "get_text"):
            # ако има следващ таг, не взимаме текст от него за окуригана
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

    # する
    for suffix in ["していました", "しています", "しました", "します", "して", "した"]:
        if w.endswith(suffix):
            stem = w[: -len(suffix)]
            return stem + "する"

    # くる
    for suffix in ["きました", "きます", "きて", "きた", "こない", "こなかった"]:
        if w.endswith(suffix):
            stem = w[: -len(suffix)]
            return stem + "くる"

    # ます形 -> 辞書形
    for suffix in ["ました", "ます"]:
        if w.endswith(suffix):
            stem = w[: -len(suffix)]
            if not stem:
                return w
            mapped = GODAN_I_TO_U.get(stem[-1])
            if mapped:
                return stem[:-1] + mapped
            return stem + "る"

    # ない形
    if w.endswith("ない") and len(w) > 2:
        stem = w[:-2]
        mapped = GODAN_A_TO_U.get(stem[-1]) if stem else None
        if mapped:
            return stem[:-1] + mapped
        return stem + "る"

    # て形 / た形 (нееднозначните って/んで ги пропускаме)
    for src, dst in [("いて", "く"), ("いで", "ぐ"), ("して", "す"), ("した", "す"), ("いた", "く"), ("いだ", "ぐ")]:
        if w.endswith(src) and len(w) > len(src):
            return w[: -len(src)] + dst

    # прилагателни
    for src, dst in [("かった", "い"), ("くて", "い"), ("くない", "い")]:
        if w.endswith(src) and len(w) > len(src):
            return w[: -len(src)] + dst

    return w


def extract_ne_id(text: str) -> str:
    m = re.search(r"(ne\d{10,})", text or "")
    return m.group(1) if m else ""


def get_nhkeasier_items():
    r = requests.get(NHKEASIER_FEED_URL, timeout=20)
    r.raise_for_status()
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

        blocks = get_article_blocks(desc_soup)
        cleaned_blocks = []
        for b in blocks:
            t = b["text"].strip()
            if not t:
                continue
            if t.lower() in {"original", "permalink"}:
                continue
            if "Original" in t or "Permalink" in t:
                continue
            cleaned_blocks.append(b)

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

        if not ne_id:
            continue

        items[ne_id] = {
            "title": title,
            "blocks": cleaned_blocks,
            "audio_url": audio_url,
            "image_url": image_url,
            "original_link": original_link,
        }

    return items


def extract_easy_article_links_from_sitemap(n=4):
    r = requests.get(EASY_SITEMAP_URL, timeout=20)
    r.raise_for_status()

    soup = BeautifulSoup(r.text, "xml")
    links = []
    seen = set()
    for loc in soup.find_all("loc"):
        url = (loc.get_text() or "").strip()
        if not url:
            continue
        parsed = urlparse(url)
        if "/news/easy/ne" not in parsed.path:
            continue
        if not parsed.path.endswith(".html"):
            continue
        if url in seen:
            continue
        seen.add(url)
        links.append(url)
        if len(links) >= n:
            break

    return links


def parse_article_from_nhk_easy(link: str):
    page = requests.get(link, timeout=20)
    page.raise_for_status()
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
        if not candidate:
            continue
        image_url = urljoin(link, candidate)
        break

    audio_url = ""
    for sel in ["audio source[src]", "audio[src]", 'a[href$=".mp3"]', 'a[href*=".mp3"]']:
        el = psoup.select_one(sel)
        if not el:
            continue
        candidate = (el.get("src") or el.get("href") or "").strip()
        if not candidate:
            continue
        audio_url = urljoin(link, candidate)
        break

    if not audio_url:
        mp3_match = re.search(r"https?://[^\"'\\s]+\\.mp3(?:\\?[^\"'\\s]*)?", page.text)
        if mp3_match:
            audio_url = mp3_match.group(0)

    if not audio_url:
        # Някои страници пазят линка като поле в JS payload
        audio_field_match = re.search(r'"(?:audio|voice|sound|movie)Url"\s*:\s*"([^"]+)"', page.text, re.IGNORECASE)
        if audio_field_match:
            audio_url = urljoin(link, audio_field_match.group(1))

    # Структурата е Next.js shell. Ако няма реален body в DOM,
    # взимаме смислени японски текстови фрагменти от payload-а.
    content = (
        psoup.select_one(".article-main__body")
        or psoup.select_one(".module--content")
        or psoup.select_one("#js-article-body")
        or psoup.select_one(".content--detail-body")
        or psoup.select_one("article")
        or psoup.select_one("main")
    )

    filtered_blocks = []
    if content is not None:
        for bad in content.select("script, style, nav, footer, header, aside, form"):
            bad.decompose()
        blocks = get_article_blocks(content)
        for b in blocks:
            t = b["text"]
            if "share" in t.lower() or "follow us" in t.lower():
                continue
            filtered_blocks.append(b)

    if not filtered_blocks:
        payload_texts = []
        for txt in re.findall(r'"children":"([^"]{10,}?)"', page.text):
            # филтрираме системни UI текстове
            if "NHK" in txt or "トップ" in txt or "ニュース・防災" in txt:
                continue
            # държим само текстове с японски букви
            if not re.search(r"[ぁ-んァ-ン一-龯]", txt):
                continue
            cleaned = txt.replace("\\n", " ").strip()
            if len(cleaned) < 10:
                continue
            payload_texts.append(cleaned)

        dedup = []
        seen_text = set()
        for t in payload_texts:
            if t in seen_text:
                continue
            seen_text.add(t)
            dedup.append(t)

        for t in dedup[:8]:
            filtered_blocks.append({"html": t, "text": t})

    if not filtered_blocks:
        desc = ""
        desc_meta = psoup.select_one('meta[name="description"]')
        if desc_meta:
            desc = (desc_meta.get("content") or "").strip()
        if desc:
            filtered_blocks.append({"html": desc, "text": desc})

    if not filtered_blocks:
        return None

    vocab = extract_vocab_from_blocks(filtered_blocks)
    translated_blocks = []
    for b in filtered_blocks:
        translated_blocks.append({
            "html": b["html"],
            "text": b["text"],
            "translation": translate_text(b["text"], dest="bg")
        })

    return {
        "title": title,
        "title_html": title_html,
        "title_translation": translate_text(title, dest="bg"),
        "link": link,
        "image_url": image_url,
        "audio_url": audio_url,
        "blocks": translated_blocks,
        "vocab": vocab,
    }


def get_articles(n=4):
    links = extract_easy_article_links_from_sitemap(max(n * 8, n))
    nhkeasier_items = {}
    try:
        nhkeasier_items = get_nhkeasier_items()
    except Exception as e:
        print(f"Could not load nhkeasier fallback feed: {e}")

    articles = []
    for link in links:
        try:
            article = parse_article_from_nhk_easy(link)
            ne_id = extract_ne_id(link)
            fallback = nhkeasier_items.get(ne_id)
            if article and fallback and fallback.get("blocks"):
                article["blocks"] = []
                for b in fallback["blocks"]:
                    tr = translate_text(b["text"], dest="bg")
                    article["blocks"].append({
                        "html": b["html"],
                        "text": b["text"],
                        "translation": tr
                    })
                article["vocab"] = extract_vocab_from_blocks(fallback["blocks"])
                if fallback.get("audio_url"):
                    article["audio_url"] = fallback["audio_url"]
                if fallback.get("image_url"):
                    article["image_url"] = fallback["image_url"]
                # Фуригана в заглавието - взимаме първия ruby блок ако е наличен
                for b in fallback["blocks"]:
                    if "<ruby" in b["html"]:
                        article["title_html"] = b["html"]
                        break

            has_blocks = bool(article and article.get("blocks"))
            has_vocab = bool(article and article.get("vocab"))
            has_image = bool(article and article.get("image_url"))
            has_audio = bool(article and article.get("audio_url"))

            if article and has_blocks and has_vocab and has_image and has_audio:
                articles.append(article)
                if len(articles) >= n:
                    break
        except Exception as e:
            print(f"Skipping article because of error: {e}")
            continue

    return articles[:n]


def build_html(
    articles,
    anki_filename=DEFAULT_ANKI_FILENAME,
    anki_apkg_filename=DEFAULT_ANKI_APKG_FILENAME,
    grammar_points=None,
):
    grammar_points = grammar_points or []
    html = """
<!doctype html>
<html lang="ja">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>最新ニュース</title>
<link rel="icon" type="image/x-icon" href="favicon.ico">
<style>
:root{
  --bg:#0f1115;
  --card:#171a21;
  --card2:#1d212b;
  --text:#e8ecf1;
  --muted:#aeb7c2;
  --accent:#8ab4ff;
  --border:#2a3040;
  --jp-panel:#12151c;
  --trans-text:#d2dae3;
  --ring-track:#1e222c;
  --ring-inner:#ffffff;
  --rt-color:#9fb3c8;
  --jp-font:"Hiragino Mincho ProN","Hiragino Mincho Pro","Yu Mincho","MS PMincho",serif;
}
*{box-sizing:border-box}
body{
  margin:0;
  background:var(--bg);
  color:var(--text);
  font-family:system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;
  line-height:1.8;
}
body.theme-light{
  --bg:#f3f4f6;
  --card:#ffffff;
  --card2:#f8fafc;
  --text:#111111;
  --muted:#4b5563;
  --accent:#1d4ed8;
  --border:#d1d5db;
  --jp-panel:#eef2f7;
  --trans-text:#111111;
  --ring-track:#d1d5db;
  --ring-inner:#ffffff;
  --rt-color:#5f6f84;
}
body.theme-sepia{
  --bg:#f1e5cf;
  --card:#f7ebd8;
  --card2:#efe0c8;
  --text:#111111;
  --muted:#3f3a2f;
  --accent:#8a5a1f;
  --border:#c8b79a;
  --jp-panel:#ead9bf;
  --trans-text:#111111;
  --ring-track:#c8b79a;
  --ring-inner:#f7ebd8;
  --rt-color:#645640;
}
.wrap{
  max-width:980px;
  margin:0 auto;
  padding:32px 16px 56px;
}
h1{
  margin:0 0 24px;
  color:var(--accent);
  font-size:2rem;
  text-align:center;
}
.font-picker{
  display:flex;
  align-items:center;
  justify-content:center;
  gap:10px;
  margin:-8px 0 10px;
}
.font-picker label{
  color:var(--muted);
  font-size:.92rem;
}
.font-picker select{
  background:var(--card2);
  color:var(--text);
  border:1px solid var(--border);
  border-radius:8px;
  padding:6px 10px;
}
.theme-picker{
  display:flex;
  align-items:center;
  justify-content:center;
  gap:10px;
  margin:0 0 22px;
}
.theme-picker label{
  color:var(--muted);
  font-size:.92rem;
}
.theme-picker select{
  background:var(--card2);
  color:var(--text);
  border:1px solid var(--border);
  border-radius:8px;
  padding:6px 10px;
}
article{
  background:var(--card);
  border:1px solid var(--border);
  border-radius:18px;
  padding:24px;
  margin-bottom:28px;
  box-shadow:0 8px 24px rgba(0,0,0,.22);
}
h2{
  margin:0 0 6px;
  font-size:1.375rem;
}
.article-head{
  display:block;
  margin-bottom:6px;
}
.article-head h2{
  margin:0;
  min-width:0;
  overflow-wrap:anywhere;
  word-break:break-word;
  line-height:1.4;
}
.known-progress{
  --p:0;
  --size:59px;
  width:var(--size);
  height:var(--size);
  border-radius:50%;
  position:relative;
  margin-top:8px;
  background:
    conic-gradient(
      from -90deg,
      #5f00ff 0%,
      #ff005a calc(var(--p) * 1%),
      var(--ring-track) calc(var(--p) * 1%),
      var(--ring-track) 100%
    );
}
.known-progress::before{
  content:"";
  position:absolute;
  inset:6px;
  border-radius:50%;
  background:var(--ring-inner);
}
.known-progress span{
  position:absolute;
  inset:0;
  display:flex;
  align-items:center;
  justify-content:center;
  color:#12151c;
  font-weight:700;
  font-size:.9rem;
  z-index:1;
}
@media (max-width:700px){
  .known-progress{
    --size:52px;
  }
}
.article-head h2 rt{
  font-size:.56em;
}
.article-media{
  margin:12px 0 14px;
}
.article-image{
  width:100%;
  max-height:420px;
  object-fit:cover;
  border-radius:12px;
  border:1px solid var(--border);
  display:block;
  margin-bottom:10px;
}
.article-audio{
  width:100%;
}
.meta{
  margin-bottom:18px;
  color:var(--muted);
  font-size:.95rem;
}
.meta a{
  color:var(--accent);
  text-decoration:none;
}
.section-title{
  margin:20px 0 10px;
  font-size:1.05rem;
  color:var(--accent);
  font-weight:700;
}
.vocab{
  background:var(--card2);
  border:1px solid var(--border);
  border-radius:14px;
  padding:16px 18px;
  margin-bottom:20px;
}
.vocab ul{
  margin:10px 0 0;
  padding-left:20px;
  columns:2;
  column-gap:24px;
}
.vocab li{
  margin:8px 0;
  break-inside:avoid;
}
@media (max-width:700px){
  .vocab ul{
    columns:1;
  }
}
.word{
  font-weight:700;
}
.meaning{
  color:var(--muted);
}
.jp-block{
  background:var(--jp-panel);
  border:1px solid var(--border);
  border-radius:12px;
  padding:14px 16px;
  margin:12px 0 6px;
  font-size:1.08rem;
}
.jp-block.is-clickable{
  cursor:pointer;
}
.jp-block.is-clickable:focus{
  outline:2px solid var(--accent);
  outline-offset:2px;
}
.jp-block.is-clickable::after{
  content:"  (клик за превод)";
  color:var(--muted);
  font-size:.8em;
}
.bg-block{
  color:var(--trans-text);
  padding:0 2px 8px 2px;
  margin-bottom:8px;
  border-bottom:1px dashed var(--border);
  display:none;
}
.bg-block.is-visible{
  display:block;
}
ruby{
  ruby-position:over;
}
rt{
  font-size:.68em;
  color:var(--rt-color);
}
.downloads{
  margin-top:20px;
  text-align:center;
}
.downloads a{
  color:var(--accent);
  font-weight:700;
  text-decoration:none;
}
.grammar{
  background:var(--card);
  border:1px solid var(--border);
  border-radius:18px;
  padding:20px;
  margin-top:20px;
}
.grammar ul{
  margin:8px 0 0;
  padding-left:20px;
}
.grammar li{
  margin:10px 0;
}
.grammar-rule{
  font-weight:700;
}
h1,
.article-head h2,
.jp-block,
.word,
.grammar-rule,
ruby,
rt{
  font-family:var(--jp-font);
}
</style>
</head>
<body>
<div class="wrap">
<h1>最新ニュース</h1>
<div class="font-picker">
  <label for="jp-font-select">Японски шрифт</label>
  <select id="jp-font-select">
    <option value="mincho">Hiragino Mincho</option>
    <option value="sans">Hiragino Sans</option>
  </select>
</div>
<div class="theme-picker">
  <label for="theme-select">Тема</label>
  <select id="theme-select">
    <option value="dark">Dark</option>
    <option value="light">Light</option>
    <option value="sepia">Sepia</option>
  </select>
</div>
"""

    for article in articles:
        html += "<article>"
        known_percent = int(article.get("known_percent", 0))
        known_count = int(article.get("known_count", 0))
        known_total = int(article.get("known_total", 0))
        progress_title = html_lib.escape(f"Познати думи: {known_count}/{known_total}")
        html += "<div class='article-head'>"
        html += f"<h2>{article.get('title_html', article['title'])}</h2>"
        html += (
            f"<div class='known-progress' style='--p:{known_percent};' "
            f"title='{progress_title}' aria-label='{progress_title}'>"
            f"<span>{known_percent}%</span></div>"
        )
        html += "</div>"

        if article["title_translation"]:
            html += f"<div class='meta'>{article['title_translation']}</div>"
        else:
            html += "<div class='meta'></div>"

        if article.get("image_url") or article.get("audio_url"):
            html += "<div class='article-media'>"
            if article.get("image_url"):
                html += f"<img class='article-image' src='{article['image_url']}' alt='{article['title']}' loading='lazy'/>"
            if article.get("audio_url"):
                html += f"<audio class='article-audio' controls preload='none' src='{article['audio_url']}'></audio>"
            html += "</div>"

        html += "<div class='section-title'>Речник</div>"
        html += "<div class='vocab'><ul>"

        for item in article["vocab"]:
            word = item["word"]
            reading = item["reading"]
            meaning = item["meaning"]

            if reading:
                word_html = f"<ruby>{word}<rt>{reading}</rt></ruby>"
            else:
                word_html = word

            if meaning:
                html += f"<li><span class='word'>{word_html}</span> — <span class='meaning'>{meaning}</span></li>"
            else:
                html += f"<li><span class='word'>{word_html}</span></li>"

        html += "</ul></div>"

        html += "<div class='section-title'>Текст</div>"

        for block in article["blocks"]:
            html += f"<div class='jp-block'>{block['html']}</div>"
            if block["translation"]:
                html += f"<div class='bg-block'>{block['translation']}</div>"

        html += "</article>"

    html += "<div class='downloads'>"
    html += f"<a href='{anki_apkg_filename}' download>Свали Anki Карти</a>"
    html += " | "
    html += f"<a href='{anki_filename}' download>TSV (backup)</a>"
    html += "</div>"

    if grammar_points:
        html += "<section class='grammar'>"
        html += "<div class='section-title'>Граматика в текстовете</div>"
        html += "<ul>"
        for g in grammar_points:
            html += "<li>"
            html += f"<span class='grammar-rule'>{g['label']}</span> — {g['explanation']}"
            html += "</li>"
        html += "</ul>"
        html += "</section>"

    html += """
</div>
<script>
document.addEventListener('DOMContentLoaded', function() {
  var jpFontSelect = document.getElementById('jp-font-select');
  var themeSelect = document.getElementById('theme-select');
  var rootStyle = document.documentElement.style;
  var jpFonts = {
    sans: '"Hiragino Sans","Hiragino Kaku Gothic ProN","Yu Gothic","Meiryo",sans-serif',
    mincho: '"Hiragino Mincho ProN","Hiragino Mincho Pro","Yu Mincho","MS PMincho",serif'
  };

  var applyJpFont = function(mode) {
    var selected = jpFonts[mode] ? mode : 'mincho';
    rootStyle.setProperty('--jp-font', jpFonts[selected]);
    if (jpFontSelect) {
      jpFontSelect.value = selected;
    }
    try {
      localStorage.setItem('jpFontMode', selected);
    } catch (e) {}
  };

  if (jpFontSelect) {
    var savedFont = 'mincho';
    try {
      savedFont = localStorage.getItem('jpFontMode') || 'mincho';
    } catch (e) {}
    applyJpFont(savedFont);
    jpFontSelect.addEventListener('change', function() {
      applyJpFont(jpFontSelect.value);
    });
  }

  var applyTheme = function(mode) {
    var selected = (mode === 'light' || mode === 'sepia') ? mode : 'dark';
    document.body.classList.remove('theme-dark', 'theme-light', 'theme-sepia');
    document.body.classList.add('theme-' + selected);
    if (themeSelect) {
      themeSelect.value = selected;
    }
    try {
      localStorage.setItem('themeMode', selected);
    } catch (e) {}
  };

  var savedTheme = 'dark';
  try {
    savedTheme = localStorage.getItem('themeMode') || 'dark';
  } catch (e) {}
  applyTheme(savedTheme);

  if (themeSelect) {
    themeSelect.addEventListener('change', function() {
      applyTheme(themeSelect.value);
    });
  }

  document.querySelectorAll('article').forEach(function(article) {
    var h2 = article.querySelector('h2');
    var firstJpBlock = article.querySelector('.jp-block');
    if (!h2 || !firstJpBlock) return;
    if (h2.querySelector('ruby')) return;
    if (!firstJpBlock.querySelector('ruby')) return;
    h2.innerHTML = firstJpBlock.innerHTML;
  });

  document.querySelectorAll('.jp-block + .bg-block').forEach(function(bgBlock) {
    var jpBlock = bgBlock.previousElementSibling;
    if (!jpBlock) return;
    jpBlock.classList.add('is-clickable');
    jpBlock.setAttribute('role', 'button');
    jpBlock.setAttribute('tabindex', '0');
    jpBlock.setAttribute('aria-expanded', 'false');

    var toggleTranslation = function() {
      var isVisible = bgBlock.classList.toggle('is-visible');
      jpBlock.setAttribute('aria-expanded', isVisible ? 'true' : 'false');
    };

    jpBlock.addEventListener('click', toggleTranslation);
    jpBlock.addEventListener('keydown', function(event) {
      if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        toggleTranslation();
      }
    });
  });
});
</script>
</body>
</html>
"""
    return html


def main():
    global DEEPL_API_KEY

    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument("--count", type=int, default=4)
    parser.add_argument("--deepl-key", default=os.environ.get("DEEPL_API_KEY", ""))
    args = parser.parse_args()
    DEEPL_API_KEY = (args.deepl_key or "").strip()

    articles = get_articles(args.count)
    if not articles:
        raise RuntimeError("No articles were extracted.")

    print(
        f"Translation provider usage: DeepL={_TRANSLATION_STATS['deepl']} "
        f"Google={_TRANSLATION_STATS['google']}"
    )

    output_dir = os.path.dirname(args.output)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)

    grammar_points = extract_grammar_points(articles)
    anki_filename = DEFAULT_ANKI_FILENAME
    anki_apkg_filename = DEFAULT_ANKI_APKG_FILENAME
    anki_seen_words_filename = DEFAULT_ANKI_SEEN_WORDS_FILENAME
    if output_dir:
        anki_path = os.path.join(output_dir, anki_filename)
        anki_apkg_path = os.path.join(output_dir, anki_apkg_filename)
        anki_seen_words_path = os.path.join(output_dir, anki_seen_words_filename)
    else:
        anki_path = anki_filename
        anki_apkg_path = anki_apkg_filename
        anki_seen_words_path = anki_seen_words_filename

    seen_words = load_seen_words(anki_seen_words_path)
    add_known_progress_to_articles(articles, seen_words)
    anki_cards, newly_added_words = build_anki_cards(
        articles,
        grammar_points=grammar_points,
        seen_items=seen_words,
    )
    save_anki_tsv(anki_cards, anki_path)
    build_anki_apkg(anki_cards, anki_apkg_path)
    save_seen_words(anki_seen_words_path, seen_words | newly_added_words)

    html = build_html(
        articles,
        anki_filename=anki_filename,
        anki_apkg_filename=anki_apkg_filename,
        grammar_points=grammar_points,
    )

    with open(args.output, "w", encoding="utf-8") as f:
        f.write(html)


if __name__ == "__main__":
    main()

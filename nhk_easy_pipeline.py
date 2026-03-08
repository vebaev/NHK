import os
import re
import argparse
import html
from urllib.parse import urljoin, urlparse
import requests
from bs4 import BeautifulSoup
from googletrans import Translator

EASY_INDEX_URL = "https://news.web.nhk/news/easy/"
EASY_SITEMAP_URL = "https://news.web.nhk/news/easy/sitemap/sitemap.xml"
NHKEASIER_FEED_URL = "https://nhkeasier.com/feed/"
DEFAULT_OUTPUT = "docs/index.html"

translator = Translator()


def translate_text(text: str, dest: str = "bg") -> str:
    text = (text or "").strip()
    if not text:
        return ""
    try:
        return translator.translate(text, dest=dest).text
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

            if rb_text not in vocab_map:
                vocab_map[rb_text] = rt_text

    vocab = []
    for word, reading in vocab_map.items():
        meaning = translate_text(word, dest="bg")
        vocab.append({
            "word": word,
            "reading": reading,
            "meaning": meaning
        })

    return vocab[:20]


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
        desc_html = html.unescape(desc_raw)
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
    links = extract_easy_article_links_from_sitemap(n)
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
                if not article.get("image_url") and fallback.get("image_url"):
                    article["image_url"] = fallback["image_url"]
                # Фуригана в заглавието - взимаме първия ruby блок ако е наличен
                for b in fallback["blocks"]:
                    if "<ruby" in b["html"]:
                        article["title_html"] = b["html"]
                        break

            if article:
                articles.append(article)
        except Exception as e:
            print(f"Skipping article because of error: {e}")
            continue

    return articles


def build_html(articles):
    html = """
<!doctype html>
<html lang="ja">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Новини от NHK</title>
<style>
:root{
  --bg:#0f1115;
  --card:#171a21;
  --card2:#1d212b;
  --text:#e8ecf1;
  --muted:#aeb7c2;
  --accent:#8ab4ff;
  --border:#2a3040;
}
*{box-sizing:border-box}
body{
  margin:0;
  background:var(--bg);
  color:var(--text);
  font-family:system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;
  line-height:1.8;
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
  font-size:1.5rem;
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
  background:#12151c;
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
  color:#d2dae3;
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
  color:#9fb3c8;
}
</style>
</head>
<body>
<div class="wrap">
<h1>Новини от NHK</h1>
"""

    for article in articles:
        html += "<article>"
        html += f"<h2>{article.get('title_html', article['title'])}</h2>"

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

    html += """
</div>
<script>
document.addEventListener('DOMContentLoaded', function() {
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
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument("--count", type=int, default=4)
    args = parser.parse_args()

    articles = get_articles(args.count)
    if not articles:
        raise RuntimeError("No articles were extracted.")

    html = build_html(articles)

    output_dir = os.path.dirname(args.output)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)

    with open(args.output, "w", encoding="utf-8") as f:
        f.write(html)


if __name__ == "__main__":
    main()

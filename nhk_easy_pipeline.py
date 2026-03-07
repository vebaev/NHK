import os
import re
import argparse
import requests
from bs4 import BeautifulSoup
from googletrans import Translator

RSS = "https://nhkeasier.com/feed/"
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


def get_articles(n=3):
    r = requests.get(RSS, timeout=20)
    r.raise_for_status()

    soup = BeautifulSoup(r.text, "xml")
    items = soup.find_all("item")[:n]

    articles = []

    for item in items:
        try:
            link = item.link.text.strip()
            title = item.title.text.strip()

            page = requests.get(link, timeout=20)
            page.raise_for_status()
            psoup = BeautifulSoup(page.text, "html.parser")

            content = (
                psoup.select_one(".entry-content")
                or psoup.select_one("article")
                or psoup.select_one("main")
                or psoup.body
            )

            if content is None:
                print(f"Skipping article, no content found: {link}")
                continue

            for bad in content.select("script, style, nav, footer, header, aside, form"):
                bad.decompose()

            blocks = get_article_blocks(content)

            # пазим само сравнително смислени блокове
            filtered_blocks = []
            for b in blocks:
                t = b["text"]

                # пропускаме навигационни и UI редове
                if "share" in t.lower():
                    continue
                if "follow us" in t.lower():
                    continue

                filtered_blocks.append(b)

            if not filtered_blocks:
                print(f"Skipping article, empty blocks: {link}")
                continue

            vocab = extract_vocab_from_blocks(filtered_blocks)

            translated_blocks = []
            for b in filtered_blocks:
                tr = translate_text(b["text"], dest="bg")
                translated_blocks.append({
                    "html": b["html"],
                    "text": b["text"],
                    "translation": tr
                })

            articles.append({
                "title": title,
                "title_translation": translate_text(title, dest="bg"),
                "link": link,
                "blocks": translated_blocks,
                "vocab": vocab
            })

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
<title>NHK Easy Reader</title>
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
}
.vocab li{
  margin:8px 0;
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
<h1>NHK Easy Reader</h1>
"""

    for article in articles:
        html += "<article>"
        html += f"<h2>{article['title']}</h2>"

        if article["title_translation"]:
            html += f"<div class='meta'>{article['title_translation']}</div>"
        else:
            html += "<div class='meta'></div>"

        html += f"<div class='meta'><a href='{article['link']}' target='_blank' rel='noopener noreferrer'>Source article</a></div>"

        html += "<div class='section-title'>Vocabulary</div>"
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

        html += "<div class='section-title'>Text</div>"

        for block in article["blocks"]:
            html += f"<div class='jp-block'>{block['html']}</div>"
            if block["translation"]:
                html += f"<div class='bg-block'>{block['translation']}</div>"

        html += "</article>"

    html += """
</div>
<script>
document.addEventListener('DOMContentLoaded', function() {
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
    parser.add_argument("--count", type=int, default=3)
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

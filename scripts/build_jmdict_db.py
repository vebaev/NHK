import argparse
import sqlite3
import xml.etree.ElementTree as ET
from pathlib import Path

def text_or_empty(el):
    return (el.text or "").strip() if el is not None else ""

def build_db(xml_path: str, db_path: str):
    Path(db_path).parent.mkdir(parents=True, exist_ok=True)

    conn = sqlite3.connect(db_path)
    cur = conn.cursor()
    cur.execute("DROP TABLE IF EXISTS entries")
    cur.execute(
        "CREATE TABLE entries (surface TEXT, reading TEXT, gloss TEXT, pos TEXT, priority INTEGER DEFAULT 0)"
    )
    cur.execute("CREATE INDEX IF NOT EXISTS idx_entries_surface ON entries(surface)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_entries_reading ON entries(reading)")

    tree = ET.parse(xml_path)
    root = tree.getroot()

    batch = []
    for entry in root.findall("entry"):
        surfaces = [text_or_empty(k) for k in entry.findall("k_ele/keb")]
        readings = [text_or_empty(r) for r in entry.findall("r_ele/reb")]
        senses = entry.findall("sense")

        glosses = []
        pos_tags = []
        priority = 0

        for s in senses[:3]:
            for g in s.findall("gloss"):
                txt = text_or_empty(g)
                if txt and txt not in glosses:
                    glosses.append(txt)
            for p in s.findall("pos"):
                txt = text_or_empty(p)
                if txt and txt not in pos_tags:
                    pos_tags.append(txt)

        for pr in entry.findall("k_ele/ke_pri") + entry.findall("r_ele/re_pri"):
            val = text_or_empty(pr)
            if val.startswith(("news", "ichi", "spec")):
                priority += 10
            elif val.startswith("nf"):
                try:
                    num = int(val[2:])
                    priority += max(1, 100 - num)
                except Exception:
                    priority += 1

        gloss = "; ".join(glosses[:3]).strip()
        pos = "; ".join(pos_tags[:3]).strip()

        if not readings and surfaces:
            readings = [""]

        for reading in readings:
            if surfaces:
                for surface in surfaces:
                    if surface:
                        batch.append((surface, reading, gloss, pos, priority))
            elif reading:
                batch.append((reading, reading, gloss, pos, priority))

        if len(batch) >= 5000:
            cur.executemany(
                "INSERT INTO entries(surface, reading, gloss, pos, priority) VALUES (?, ?, ?, ?, ?)",
                batch,
            )
            conn.commit()
            batch = []

    if batch:
        cur.executemany(
            "INSERT INTO entries(surface, reading, gloss, pos, priority) VALUES (?, ?, ?, ?, ?)",
            batch,
        )
        conn.commit()

    conn.close()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--xml", required=True, help="Path to JMdict XML file")
    parser.add_argument("--db", default="data/jmdict.db", help="Output SQLite DB path")
    args = parser.parse_args()
    build_db(args.xml, args.db)

if __name__ == "__main__":
    main()

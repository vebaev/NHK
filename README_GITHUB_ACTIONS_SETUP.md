# NHK Easy Daily Automation

This package gives you a simple daily pipeline:

1. GitHub Actions runs once per day.
2. `nhk_easy_pipeline.py` fetches the latest NHK Easier RSS items.
3. The script builds `docs/index.html` in dark mode.
4. The workflow commits the updated HTML back to the repository.
5. You can publish `docs/` with GitHub Pages.

## Files

- `nhk_easy_pipeline.py` — main generator script
- `requirements.txt` — Python dependencies
- `.github/workflows/daily_nhk_easy.yml` — daily scheduler
- `glossary_overrides.json` — optional manual meanings

## Setup

### 1. Create a GitHub repo
Upload these files to the root of the repository.

### 2. Enable GitHub Pages
In the repo settings:
- open **Pages**
- set source to **Deploy from a branch**
- choose **main** branch
- choose `/docs` folder

After the first workflow run, your page will be published from `docs/index.html`.

### 3. Check Actions permissions
In repo settings → **Actions** → **General**:
- allow workflows to have read and write permissions

If your repo uses the newer workflow permission model, also ensure:
- **Workflow permissions** → **Read and write permissions**

### 4. Run once manually
Open **Actions** in GitHub and run **Generate NHK Easy page** with **Run workflow**.

### 5. Daily schedule
The workflow uses:

```cron
10 4 * * *
```

That means **04:10 UTC every day**.

## Local test

```bash
python -m pip install -r requirements.txt
python nhk_easy_pipeline.py --output docs/index.html --count 3
```

## Notes

- Furigana is rendered with HTML `ruby` / `rt` when the source text contains `漢字(かな)` patterns.
- Vocabulary is shown before the article text.
- Meanings come from `glossary_overrides.json`. Add more entries there for cleaner vocabulary output.
- If the source site changes its HTML structure, the parser may need small selector updates.

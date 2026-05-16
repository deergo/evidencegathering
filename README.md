# Evidence Gathering

Flask app for viewing student grades and generating evidence PDFs.

## Requirements

- Python 3.12 or close equivalent
- `pip`

## Setup

Create and activate a virtual environment:

```bash
python3 -m venv venv
source venv/bin/activate
```

Install dependencies:

```bash
pip install -r requirements.txt
```

## Run

Start the app with:

```bash
python grades.py
```

Then open:

```text
http://127.0.0.1:5000
```

## Project Files

- `grades.py` — main Flask application
- `requirements.txt` — Python dependencies
- `candidates.csv` — candidate source data
- `y11scores.csv` — evidence score data

## Pulling On Another Device

After cloning or pulling the repository:

```bash
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt
python grades.py
```

## Notes

- The local virtual environment is intentionally not committed.
- Generated cache files and the local SQLite database are ignored by Git.
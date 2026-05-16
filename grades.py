"""
grades.py — Flask web app to view student grades and generate evidence PDFs.
Run:  python grades.py
Then open http://127.0.0.1:5000 in your browser.
"""

import csv
import io
import os
import sqlite3
import base64
import textwrap

import requests
from flask import Flask, render_template_string, request, send_file, g

from reportlab.lib.pagesizes import A4
from reportlab.lib.units import mm
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib import colors
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle,
    Image as RLImage, KeepTogether, HRFlowable,
)
from reportlab.lib.enums import TA_LEFT, TA_CENTER
from PIL import Image as PILImage

BASE = "https://aimarker.replit.app"
API_KEY = "vagEqbnj0uoocoXuqBQ69r7oYKlhbGWktPNorsYtTrz6PZRjLWE6aQ"
HEADERS = {"X-Api-Key": API_KEY}

DB_PATH = os.path.join(os.path.dirname(__file__), "candidates.db")
CSV_PATH = os.path.join(os.path.dirname(__file__), "candidates.csv")

app = Flask(__name__)

# ---------------------------------------------------------------------------
# Database helpers
# ---------------------------------------------------------------------------

def get_db():
    db = getattr(g, "_database", None)
    if db is None:
        db = g._database = sqlite3.connect(DB_PATH)
        db.row_factory = sqlite3.Row
    return db


@app.teardown_appcontext
def close_db(exc):
    db = getattr(g, "_database", None)
    if db is not None:
        db.close()


def init_db():
    """Create (or recreate) the candidates table from the CSV."""
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("DROP TABLE IF EXISTS candidates")
    cur.execute("""
        CREATE TABLE candidates (
            email        TEXT PRIMARY KEY,
            candidate_no TEXT,
            school_code  TEXT,
            surname      TEXT,
            forename     TEXT,
            year_group   TEXT,
            form         TEXT,
            gender       TEXT,
            dob          TEXT,
            uci          TEXT
        )
    """)
    with open(CSV_PATH, newline="", encoding="utf-8-sig") as f:
        reader = csv.DictReader(f)
        rows = []
        for row in reader:
            rows.append((
                row.get("Student Email Address", "").strip().lower(),
                row.get("Candidate #", "").strip(),
                row.get("School Code", "").strip(),
                row.get("Surname", "").strip(),
                row.get("Forename", "").strip(),
                row.get("Year Group", "").strip(),
                row.get("Form", "").strip(),
                row.get("Gender", "").strip(),
                row.get("DOB", "").strip(),
                row.get("UCI", "").strip(),
            ))
        cur.executemany(
            "INSERT OR IGNORE INTO candidates VALUES (?,?,?,?,?,?,?,?,?,?)", rows
        )
    conn.commit()
    conn.close()
    print(f"[DB] Imported {len(rows)} candidates into {DB_PATH}")


def lookup_candidate(email: str):
    """Return candidate row dict or None."""
    cur = get_db().execute(
        "SELECT * FROM candidates WHERE email = ?", (email.strip().lower(),)
    )
    row = cur.fetchone()
    return dict(row) if row else None


# ---------------------------------------------------------------------------
# API helpers
# ---------------------------------------------------------------------------

def fetch_grades(class_code: str, quiz_code: str):
    url = f"{BASE}/ext-api/classes/{class_code}/attempts/"
    params = {"quiz_code": quiz_code}
    resp = requests.get(url, headers=HEADERS, params=params, timeout=30)
    resp.raise_for_status()
    return resp.json()


def fetch_grades(class_code: str, quiz_code: str, include_questions: bool = False):
    """Fetch attempt list, optionally with inline question/answer data."""
    url = f"{BASE}/ext-api/classes/{class_code}/attempts/"
    params = {"quiz_code": quiz_code}
    if include_questions:
        params["include_questions"] = "true"
    resp = requests.get(url, headers=HEADERS, params=params, timeout=60)
    resp.raise_for_status()
    return resp.json()


def fetch_attempt_detail(attempt_id: str):
    """Fetch full question/answer detail for a single attempt (fallback)."""
    url = f"{BASE}/ext-api/attempts/{attempt_id}/"
    resp = requests.get(url, headers=HEADERS, timeout=30)
    resp.raise_for_status()
    return resp.json()


def fetch_all_attempts(class_code: str):
    """Fetch ALL attempts for a class with no quiz_code filter."""
    url = f"{BASE}/ext-api/classes/{class_code}/attempts/"
    resp = requests.get(url, headers=HEADERS, timeout=60)
    resp.raise_for_status()
    data = resp.json()
    if isinstance(data, list):
        return data
    return data.get("attempts", [])


def _attempt_date(attempt: dict):
    """Return a datetime for the attempt, or None if unparseable."""
    from datetime import datetime, timezone
    for key in ("last_answer_at", "first_answer_at", "submitted_at", "completed_at", "created_at", "date", "timestamp", "taken_at", "answered_at"):
        raw = attempt.get(key)
        if not raw:
            continue
        try:
            raw = str(raw).replace("Z", "+00:00")
            return datetime.fromisoformat(raw)
        except Exception:
            pass
    return None


def _cutoff_date(months_ago: int | None):
    """Return a timezone-aware cutoff datetime, or None if months_ago is falsy."""
    if not months_ago:
        return None
    from datetime import datetime, timezone, timedelta
    return datetime.now(timezone.utc) - timedelta(days=months_ago * 30.44)


def _filter_attempts_by_date(attempts: list, cutoff) -> list:
    """Keep attempts on or after cutoff. Attempts with no parseable date are kept."""
    if cutoff is None:
        return attempts
    from datetime import timezone
    result = []
    for a in attempts:
        d = _attempt_date(a)
        if d is None:
            result.append(a)  # no date info — keep
            continue
        # Make both offset-aware for comparison
        if d.tzinfo is None:
            from datetime import timezone
            d = d.replace(tzinfo=timezone.utc)
        if d >= cutoff:
            result.append(a)
    return result


# Candidate field names that might carry a spec/topic reference on a question object
_SPEC_FIELDS = (
    "speccode", "spec_code", "spec", "specification", "topic_code", "topic",
    "category", "ref", "code", "question_code", "sub_topic",
    "learning_objective", "objective", "strand",
)


def _quiz_matches_spec(class_code: str, quiz_code: str, spec_code: str) -> bool:
    """Return True if >=50% of questions in this quiz contain spec_code
    in any recognised spec/topic field (case-insensitive substring match)."""
    try:
        data = fetch_grades(class_code, quiz_code, include_questions=True)
        attempts = data.get("attempts", [])
        if not attempts:
            return False
        first = attempts[0]
        questions = (
            first.get("questions") or first.get("question_list")
            or first.get("responses") or first.get("answers") or []
        )
        if not questions:
            return False
        needle = spec_code.strip().lower()
        matched = 0
        for q in questions:
            for field in _SPEC_FIELDS:
                val = str(q.get(field, "")).strip().lower()
                if val and needle in val:
                    matched += 1
                    break  # count each question at most once
        return (matched / len(questions)) >= 0.5
    except Exception:
        return False


def discover_quiz_summaries(
    class_code: str,
    manual_codes: str = "",
    months_ago: int | None = None,
    spec_code: str = "",
) -> tuple:
    """Return (quiz_summaries list, raw_attempts_by_quiz_code dict).
    If manual_codes is given (comma-separated), fetch each individually.
    Otherwise fetch all attempts at once and group by quiz_code field."""
    cutoff = _cutoff_date(months_ago)
    raw_by_quiz = {}  # quiz_code -> [attempt dicts]
    if manual_codes:
        codes = [c.strip() for c in manual_codes.split(",") if c.strip()]
        for qc in codes:
            try:
                data = fetch_grades(class_code, qc)
                filtered = _filter_attempts_by_date(data.get("attempts", []), cutoff)
                if filtered:
                    raw_by_quiz[qc] = filtered
            except Exception:
                continue
    else:
        all_attempts = fetch_all_attempts(class_code)
        for a in _filter_attempts_by_date(all_attempts, cutoff):
            qc = a.get("quiz_code") or a.get("quiz") or a.get("quiz_id") or a.get("quiz_name")
            if qc:
                raw_by_quiz.setdefault(str(qc), []).append(a)

    infos = _summaries_from_groups(raw_by_quiz)

    # Apply spec_code filter — requires a questions fetch per quiz
    if spec_code:
        valid = {q["quiz_code"] for q in infos if _quiz_matches_spec(class_code, q["quiz_code"], spec_code)}
        infos = [q for q in infos if q["quiz_code"] in valid]
        raw_by_quiz = {qc: v for qc, v in raw_by_quiz.items() if qc in valid}

    return infos, raw_by_quiz


def _summaries_from_groups(grouped: dict) -> list:
    result = []
    for qc, attempts in grouped.items():
        possible_values = [a.get("marks_possible") for a in attempts if a.get("marks_possible") is not None]
        pct_values = [a.get("percentage") for a in attempts if a.get("percentage") is not None]
        avg_possible = sum(possible_values) / len(possible_values) if possible_values else 0
        avg_pct = sum(pct_values) / len(pct_values) if pct_values else None
        dates = [_attempt_date(a) for a in attempts]
        dates = [d for d in dates if d is not None]
        latest = max(dates).strftime("%d %b %Y") if dates else None
        result.append({
            "quiz_code": qc,
            "est_minutes": round(avg_possible),
            "avg_marks_possible": avg_possible,
            "avg_percentage": avg_pct,
            "attempt_count": len(attempts),
            "latest_date": latest,
        })
    return result


def compute_per_student_evidence(
    raw_by_quiz: dict,
    target_min: int = 50,
    target_max: int = 70,
    top_n: int = 3,
) -> list:
    """Build per-student best evidence from {quiz_code: [attempts]} mapping.
    For each student uses their own percentage (best attempt per quiz)."""
    student_best = {}  # email -> quiz_code -> best quiz entry
    for qc, attempts in raw_by_quiz.items():
        for a in attempts:
            email = (a.get("student_email") or "").strip().lower()
            if not email:
                continue
            possible = a.get("marks_possible") or 0
            pct = a.get("percentage")
            prev = student_best.get(email, {}).get(qc)
            if prev is None or (pct or 0) > (prev.get("avg_percentage") or 0):
                student_best.setdefault(email, {})[qc] = {
                    "quiz_code": qc,
                    "est_minutes": round(possible) if possible else 0,
                    "avg_marks_possible": possible,
                    "avg_percentage": pct,
                    "attempt_count": 1,
                    "latest_date": None,
                }
    results = []
    for email, quiz_map in sorted(student_best.items()):
        evidence = find_best_evidence(list(quiz_map.values()), target_min, target_max, top_n)
        results.append({"email": email, "evidence": evidence})
    return results



def grade_suggestion(percentage: float | None) -> str:
    """Map average percentage to GCSE grade 1-9."""
    if percentage is None:
        return "?"
    thresholds = [
        (85, "9"), (75, "8"), (65, "7"), (55, "6"),
        (45, "5"), (35, "4"), (25, "3"), (15, "2"),
    ]
    for threshold, grade in thresholds:
        if percentage >= threshold:
            return grade
    return "1"


def find_best_evidence(quizzes_info: list, target_min: int = 50, target_max: int = 70, top_n: int = 3):
    """
    Given a list of quiz summary dicts (each with est_minutes, avg_percentage),
    find the top_n best single or paired quizzes that meet the time target.
    Returns a list of evidence dicts sorted by quality score.
    """
    candidates = []

    # Single quizzes
    for q in quizzes_info:
        mins = q["est_minutes"]
        if mins >= target_min:
            score = _evidence_score(mins, q["avg_percentage"], target_min, target_max)
            candidates.append({
                "type": "single",
                "quizzes": [q],
                "quiz_codes": [q["quiz_code"]],
                "total_minutes": mins,
                "avg_percentage": q["avg_percentage"],
                "grade": grade_suggestion(q["avg_percentage"]),
                "score": score,
                "label": q["quiz_code"],
            })

    # Pairs of quizzes
    for i in range(len(quizzes_info)):
        for j in range(i + 1, len(quizzes_info)):
            q1, q2 = quizzes_info[i], quizzes_info[j]
            total_mins = q1["est_minutes"] + q2["est_minutes"]
            if total_mins >= target_min:
                # Weighted average percentage
                w1 = q1["avg_marks_possible"]
                w2 = q2["avg_marks_possible"]
                total_w = w1 + w2
                if total_w > 0 and q1["avg_percentage"] is not None and q2["avg_percentage"] is not None:
                    combined_pct = (q1["avg_percentage"] * w1 + q2["avg_percentage"] * w2) / total_w
                else:
                    combined_pct = q1["avg_percentage"] or q2["avg_percentage"]
                score = _evidence_score(total_mins, combined_pct, target_min, target_max)
                candidates.append({
                    "type": "combined",
                    "quizzes": [q1, q2],
                    "quiz_codes": [q1["quiz_code"], q2["quiz_code"]],
                    "total_minutes": total_mins,
                    "avg_percentage": combined_pct,
                    "grade": grade_suggestion(combined_pct),
                    "score": score,
                    "label": f"{q1['quiz_code']} + {q2['quiz_code']}",
                })

    # Sort by score descending, take top_n
    candidates.sort(key=lambda x: x["score"], reverse=True)
    return candidates[:top_n]


def _evidence_score(total_mins: int, avg_pct: float | None, target_min: int, target_max: int) -> float:
    """Score an evidence candidate. Higher is better.
    Prefers items in the 50-70 min range; penalises far above target_max.
    Also weights by average percentage performance."""
    if total_mins < target_min:
        time_score = total_mins / target_min  # partial credit
    elif total_mins <= target_max:
        time_score = 1.0
    else:
        # Slight penalty for going very long, but still valid
        time_score = max(0.5, 1.0 - (total_mins - target_max) / 60)
    pct_score = (avg_pct or 50) / 100
    return time_score * 0.6 + pct_score * 0.4


def build_rows(attempts: list) -> list:
    rows = []
    for a in sorted(attempts, key=lambda x: x.get("student_email", "")):
        awarded  = a.get("marks_awarded")
        possible = a.get("marks_possible")
        fully    = a.get("fully_marked", False)
        unmarked = a.get("questions_unmarked", 0)

        if fully:
            status = "Marked"
        elif unmarked > 0:
            status = f"{unmarked} unmarked"
        else:
            status = "Partial"

        rows.append({
            "email":      a.get("student_email", "unknown"),
            "attempt_id": a.get("id") or a.get("attempt_id", ""),
            "marks_str":  f"{awarded}/{possible}" if awarded is not None else "—/—",
            "marks_possible": possible,
            "percentage": a.get("percentage"),
            "status":     status,
        })
    return rows


# ---------------------------------------------------------------------------
# HTML Templates
# ---------------------------------------------------------------------------

BASE_STYLE = """
<style>
  *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
  body { font-family: system-ui, sans-serif; background: #f0f2f5; color: #1a1a2e; padding: 2rem; }
  h1 { font-size: 1.6rem; margin-bottom: 1.5rem; color: #16213e; }
  h2 { font-size: 1.2rem; margin-bottom: 1rem; color: #16213e; }

  .card { background: #fff; border-radius: 10px; box-shadow: 0 2px 8px rgba(0,0,0,.1); padding: 1.5rem; margin-bottom: 1.5rem; }

  form { display: flex; gap: 1rem; flex-wrap: wrap; align-items: flex-end; }
  label { display: flex; flex-direction: column; gap: .3rem; font-size: .85rem; font-weight: 600; }
  input[type=text], input[type=number], select {
    padding: .5rem .75rem; border: 1px solid #ccc; border-radius: 6px;
    font-size: .95rem; width: 180px;
  }
  input[type=text]:focus, input[type=number]:focus, select:focus {
    outline: 2px solid #0f3460; border-color: transparent;
  }
  .btn { padding: .55rem 1.4rem; background: #0f3460; color: #fff; border: none;
         border-radius: 6px; font-size: 1rem; cursor: pointer; text-decoration: none;
         display: inline-block; }
  .btn:hover { background: #16213e; }
  .btn-sm { padding: .3rem .9rem; font-size: .85rem; }
  .btn-green { background: #065f46; }
  .btn-green:hover { background: #064e3b; }

  .meta { display: flex; gap: 2rem; flex-wrap: wrap; }
  .meta-item { display: flex; flex-direction: column; }
  .meta-item span:first-child { font-size: .75rem; font-weight: 700; text-transform: uppercase; color: #888; }
  .meta-item span:last-child { font-size: 1.1rem; font-weight: 600; }

  table { width: 100%; border-collapse: collapse; font-size: .9rem; }
  thead th { background: #0f3460; color: #fff; padding: .65rem 1rem; text-align: left; }
  tbody tr:nth-child(even) { background: #f7f8fc; }
  tbody td { padding: .6rem 1rem; border-bottom: 1px solid #e8e8e8; }
  tbody tr:hover { background: #eef1fb; }

  .badge { display: inline-block; padding: .2rem .6rem; border-radius: 999px; font-size: .8rem; font-weight: 600; }
  .badge-ok   { background: #d1fae5; color: #065f46; }
  .badge-warn { background: #fef9c3; color: #713f12; }
  .badge-part { background: #e0e7ff; color: #3730a3; }

  .bar-wrap { width: 120px; background: #e5e7eb; border-radius: 4px; height: 8px;
              display: inline-block; vertical-align: middle; margin-right: .4rem; }
  .bar-fill  { height: 8px; border-radius: 4px; background: #0f3460; }

  .error { background: #fee2e2; color: #991b1b; padding: .75rem 1rem; border-radius: 6px; }
  .no-data { color: #666; font-style: italic; }
  .info { color: #555; font-size: .9rem; }

  .pdf-options { display: grid; grid-template-columns: repeat(auto-fill, minmax(200px, 1fr)); gap: 1rem; }
  .checkbox-row { display: flex; gap: .5rem; align-items: center; font-size: .9rem; font-weight: 500; }
  input[type=checkbox] { width: 16px; height: 16px; cursor: pointer; }
  .section-title { font-size: .75rem; font-weight: 700; text-transform: uppercase;
                   color: #0f3460; margin-bottom: .5rem; letter-spacing: .05em; }
  .time-badge { background: #eff6ff; color: #1e40af; padding: .2rem .7rem;
                border-radius: 999px; font-size: .8rem; font-weight: 600; margin-left: .5rem; }

  .tabs { display: flex; gap: .25rem; margin-bottom: 1.5rem; border-bottom: 2px solid #e5e7eb; }
  .tab  { padding: .6rem 1.4rem; border-radius: 8px 8px 0 0; font-size: .95rem; font-weight: 600;
           text-decoration: none; color: #555; background: #e9ecef; border: 1px solid #ddd;
           border-bottom: none; position: relative; top: 2px; }
  .tab:hover  { background: #dde3f0; color: #0f3460; }
  .tab.active { background: #fff; color: #0f3460; border-color: #e5e7eb; z-index: 1; }

  .ev-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(340px, 1fr)); gap: 1.2rem; margin-bottom: 1.5rem; }
  .ev-card { background: #fff; border-radius: 10px; box-shadow: 0 2px 8px rgba(0,0,0,.1);
             border-left: 5px solid #0f3460; padding: 1.2rem; }
  .ev-card.rank-1 { border-left-color: #d97706; }
  .ev-card.rank-2 { border-left-color: #6b7280; }
  .ev-card.rank-3 { border-left-color: #92400e; }
  .ev-rank { font-size: .75rem; font-weight: 800; text-transform: uppercase; letter-spacing: .1em;
             color: #888; margin-bottom: .3rem; }
  .ev-label { font-size: 1.05rem; font-weight: 700; color: #0f3460; margin-bottom: .5rem; word-break: break-all; }
  .ev-meta { display: flex; gap: 1rem; flex-wrap: wrap; margin-bottom: .8rem; }
  .ev-pill { padding: .2rem .65rem; border-radius: 999px; font-size: .8rem; font-weight: 600; }
  .ev-pill-time { background: #eff6ff; color: #1e40af; }
  .ev-pill-pct  { background: #f0fdf4; color: #065f46; }
  .ev-grade { font-size: 2rem; font-weight: 900; color: #0f3460; margin-bottom: .8rem; }
  .ev-grade small { font-size: .85rem; font-weight: 500; color: #888; margin-left: .25rem; }
  .ev-component { background: #f8faff; border-radius: 6px; padding: .5rem .75rem;
                  font-size: .85rem; margin-bottom: .4rem; }
  .ev-component b { color: #16213e; }
  .ev-actions { margin-top: .8rem; display: flex; flex-wrap: wrap; gap: .5rem; }

  .grade-badge {
    display: inline-block; padding: .15rem .55rem; border-radius: 4px;
    font-weight: 800; font-size: .95rem; margin-left: .3rem;
  }
  .grade-9 { background: #1e3a5f; color: #fff; }
  .grade-8 { background: #1e40af; color: #fff; }
  .grade-7 { background: #0369a1; color: #fff; }
  .grade-6 { background: #0891b2; color: #fff; }
  .grade-5 { background: #059669; color: #fff; }
  .grade-4 { background: #65a30d; color: #fff; }
  .grade-3 { background: #ca8a04; color: #fff; }
  .grade-2 { background: #ea580c; color: #fff; }
  .grade-1 { background: #dc2626; color: #fff; }
  .grade-? { background: #9ca3af; color: #fff; }
</style>
"""

INDEX_TEMPLATE = BASE_STYLE + """
<h1>Grade Viewer</h1>

<nav class="tabs">
  <a class="tab active" href="/">Grades</a>
  <a class="tab" href="/evidence{% if class_code %}?class_code={{ class_code }}{% endif %}">Best Evidence</a>
</nav>

<div class="card">
  <form method="get" action="/">
    <label>Class Code
      <input type="text" name="class_code" value="{{ class_code }}" placeholder="e.g. CS101" required>
    </label>
    <label>Quiz Code
      <input type="text" name="quiz_code" value="{{ quiz_code }}" placeholder="e.g. QUIZ1" required>
    </label>
    <button type="submit" class="btn">View Grades</button>
  </form>
</div>

{% if error %}<div class="card error">{{ error }}</div>{% endif %}

{% if data %}
<div class="card">
  <div class="meta">
    <div class="meta-item"><span>Class</span><span>{{ data.class_code }}</span></div>
    <div class="meta-item"><span>Quiz</span><span>{{ quiz_code }}</span></div>
    <div class="meta-item"><span>Owner</span><span>{{ data.owner_email or "—" }}</span></div>
    <div class="meta-item"><span>Students in class</span><span>{{ data.student_count or "—" }}</span></div>
    <div class="meta-item"><span>Attempts</span><span>{{ data.attempt_count or attempts|length }}</span></div>
    {% if est_minutes %}
    <div class="meta-item"><span>Est. time</span>
      <span><span class="time-badge">~{{ est_minutes }} min</span></span>
    </div>
    {% endif %}
  </div>
</div>

<div class="card">
  <h2>Generate PDF Evidence</h2>
  <form method="get" action="/pdf">
    <input type="hidden" name="class_code" value="{{ class_code }}">
    <input type="hidden" name="quiz_code" value="{{ quiz_code }}">

    <div class="pdf-options">
      <div>
        <div class="section-title">Students</div>
        <label>Student (leave blank = all)
          <input type="text" name="student_email" value="" placeholder="email or blank">
        </label>
      </div>

      <div>
        <div class="section-title">Include in PDF</div>
        <div class="checkbox-row">
          <input type="checkbox" name="inc_marks" id="inc_marks" value="1" checked>
          <label for="inc_marks">Marks</label>
        </div>
        <div class="checkbox-row" style="margin-top:.4rem">
          <input type="checkbox" name="inc_comments" id="inc_comments" value="1" checked>
          <label for="inc_comments">Examiner comments</label>
        </div>
        <div class="checkbox-row" style="margin-top:.4rem">
          <input type="checkbox" name="inc_questions" id="inc_questions" value="1" checked>
          <label for="inc_questions">Questions</label>
        </div>
        <div class="checkbox-row" style="margin-top:.4rem">
          <input type="checkbox" name="inc_labels" id="inc_labels" value="1" checked>
          <label for="inc_labels">Section labels (e.g. "Student response:")</label>
        </div>
      </div>

      <div>
        <div class="section-title">Page margins (mm)</div>
        <label>Top / Bottom
          <input type="number" name="margin_tb" value="15" min="5" max="50">
        </label>
        <label style="margin-top:.5rem">Left / Right
          <input type="number" name="margin_lr" value="15" min="5" max="50">
        </label>
      </div>

      <div>
        <div class="section-title">Image-only responses</div>
        <label>Image width (% of page)
          <input type="number" name="img_pct" value="100" min="30" max="150">
        </label>
        <label style="margin-top:.5rem">Crop top of image
          <select name="img_crop_pct">
            <option value="0">None (0%)</option>
            <option value="2">2%</option>
            <option value="3" selected>3% (default)</option>
            <option value="5">5%</option>
            <option value="10">10%</option>
            <option value="15">15%</option>
          </select>
        </label>
        <label style="margin-top:.5rem">Page break between students?
          <select name="page_break">
            <option value="1" selected>Yes</option>
            <option value="0">No</option>
          </select>
        </label>
      </div>
    </div>

    <div style="margin-top:1.2rem">
      <button type="submit" class="btn btn-green">Download PDF</button>
    </div>
  </form>
</div>

<div class="card">
  {% if attempts %}
  <table>
    <thead>
      <tr>
        <th>Candidate #</th>
        <th>Student Name</th>
        <th>Student Email</th>
        <th>Marks</th>
        <th>Percentage</th>
        <th>Status</th>
      </tr>
    </thead>
    <tbody>
      {% for a in attempts %}
      <tr>
        <td>{{ a.candidate_no or "—" }}</td>
        <td>{{ a.full_name or "—" }}</td>
        <td>{{ a.email }}</td>
        <td>{{ a.marks_str }}</td>
        <td>
          {% if a.percentage is not none %}
            <div class="bar-wrap"><div class="bar-fill" style="width:{{ [a.percentage,100]|min }}%"></div></div>
            {{ "%.1f"|format(a.percentage) }}%
          {% else %}—{% endif %}
        </td>
        <td>
          {% if a.status == "Marked" %}<span class="badge badge-ok">Marked</span>
          {% elif "unmarked" in a.status %}<span class="badge badge-warn">{{ a.status }}</span>
          {% else %}<span class="badge badge-part">{{ a.status }}</span>{% endif %}
        </td>
      </tr>
      {% endfor %}
    </tbody>
  </table>
  {% else %}
  <p class="no-data">No attempts found for this class/quiz combination.</p>
  {% endif %}
</div>
{% endif %}
"""

# ---------------------------------------------------------------------------
# PDF options partial (reused in both templates)
# ---------------------------------------------------------------------------
PDF_OPTIONS_PARTIAL = """
<div class="pdf-options">
  <div>
    <div class="section-title">Include in PDF</div>
    <div class="checkbox-row">
      <input type="checkbox" name="inc_marks" id="pdf_inc_marks_{uid}" value="1" checked>
      <label for="pdf_inc_marks_{uid}">Marks</label>
    </div>
    <div class="checkbox-row" style="margin-top:.4rem">
      <input type="checkbox" name="inc_comments" id="pdf_inc_comments_{uid}" value="1" checked>
      <label for="pdf_inc_comments_{uid}">Examiner comments</label>
    </div>
    <div class="checkbox-row" style="margin-top:.4rem">
      <input type="checkbox" name="inc_questions" id="pdf_inc_questions_{uid}" value="1" checked>
      <label for="pdf_inc_questions_{uid}">Questions</label>
    </div>
    <div class="checkbox-row" style="margin-top:.4rem">
      <input type="checkbox" name="inc_labels" id="pdf_inc_labels_{uid}" value="1" checked>
      <label for="pdf_inc_labels_{uid}">Section labels</label>
    </div>
  </div>
  <div>
    <div class="section-title">Page margins (mm)</div>
    <label>Top / Bottom <input type="number" name="margin_tb" value="15" min="5" max="50"></label>
    <label style="margin-top:.5rem">Left / Right <input type="number" name="margin_lr" value="15" min="5" max="50"></label>
  </div>
  <div>
    <div class="section-title">Image-only responses</div>
    <label>Image width (% of page) <input type="number" name="img_pct" value="100" min="30" max="150"></label>
    <label style="margin-top:.5rem">Crop top of image
      <select name="img_crop_pct">
        <option value="0">None (0%)</option>
        <option value="2">2%</option>
        <option value="3" selected>3% (default)</option>
        <option value="5">5%</option>
        <option value="10">10%</option>
        <option value="15">15%</option>
      </select>
    </label>
    <label style="margin-top:.5rem">Page break between students?
      <select name="page_break">
        <option value="1" selected>Yes</option>
        <option value="0">No</option>
      </select>
    </label>
  </div>
</div>
"""

EVIDENCE_TEMPLATE = BASE_STYLE + """
<h1>Grade Viewer</h1>

<nav class="tabs">
  <a class="tab" href="/">Grades</a>
  <a class="tab active" href="/evidence{% if class_code %}?class_code={{ class_code }}{% endif %}">Best Evidence</a>
</nav>

<div class="card">
  <h2>Find Best Evidence</h2>
  <p class="info" style="margin-bottom:1rem">
    Enter a class code and click <strong>Find Evidence</strong> — quizzes are auto-detected from
    student attempts. You can also override by entering specific quiz codes (comma-separated).
  </p>
  <form method="get" action="/evidence">
    <label>Class Code
      <input type="text" name="class_code" value="{{ class_code }}" placeholder="e.g. oxaqa25" required>
    </label>
    <label>Quiz Codes <span style="font-weight:400;color:#888">(optional — auto-detected if blank)</span>
      <input type="text" name="quiz_codes" value="{{ quiz_codes }}" placeholder="leave blank to auto-detect" style="width:320px">
    </label>
    <label>Student email <span style="font-weight:400;color:#888">(blank = all)</span>
      <input type="text" name="student_email" value="{{ student_email }}" placeholder="leave blank for class">
    </label>
    <label>Min. minutes
      <input type="number" name="target_min" value="{{ target_min }}" min="20" max="120">
    </label>
    <label>Target max minutes
      <input type="number" name="target_max" value="{{ target_max }}" min="30" max="180">
    </label>
    <label>Up to how many months ago
      <select name="months_ago">
        <option value="" {% if not months_ago %}selected{% endif %}>Any time</option>
        <option value="1" {% if months_ago == '1' %}selected{% endif %}>Last 1 month</option>
        <option value="2" {% if months_ago == '2' %}selected{% endif %}>Last 2 months</option>
        <option value="3" {% if months_ago == '3' %}selected{% endif %}>Last 3 months</option>
        <option value="6" {% if months_ago == '6' %}selected{% endif %}>Last 6 months</option>
        <option value="12" {% if months_ago == '12' %}selected{% endif %}>Last 12 months</option>
        <option value="24" {% if months_ago == '24' %}selected{% endif %}>Last 24 months</option>
      </select>
    </label>
    <label>Spec code filter <span style="font-weight:400;color:#888">(optional)</span>
      <input type="text" name="spec_code" value="{{ spec_code }}" placeholder="e.g. 3.1.2 or Networks">
    </label>
    <button type="submit" class="btn">Find Evidence</button>
  </form>
</div>

{% if error %}<div class="card error">{{ error|safe }}</div>{% endif %}

{% if evidence or all_quizzes %}
<div class="card">
  <h2>Top {{ evidence|length }} Evidence Options
    <span class="time-badge">{{ quizzes_checked }} quiz{{ 'zes' if quizzes_checked != 1 else '' }} checked</span>
  </h2>
  <div class="ev-grid">
    {% for ev in evidence %}
    {% set rank = loop.index %}
    <div class="ev-card rank-{{ rank }}">
      <div class="ev-rank">
        {% if rank == 1 %}🥇 Top pick{% elif rank == 2 %}🥈 2nd{% else %}🥉 3rd{% endif %}
      </div>
      <div class="ev-label">{{ ev.label }}</div>
      <div class="ev-meta">
        <span class="ev-pill ev-pill-time">~{{ ev.total_minutes }} min</span>
        {% if ev.avg_percentage is not none %}
        <span class="ev-pill ev-pill-pct">{{ "%.1f"|format(ev.avg_percentage) }}% avg</span>
        {% endif %}
        {% if ev.type == "combined" %}<span class="ev-pill" style="background:#fef9c3;color:#713f12">Combined</span>{% endif %}
      </div>
      <div class="ev-grade">
        Grade <span class="grade-badge grade-{{ ev.grade }}">{{ ev.grade }}</span>
        <small>suggested</small>
      </div>

      {% for q in ev.quizzes %}
      <div class="ev-component">
        <b>{{ q.quiz_code }}</b> —
        ~{{ q.est_minutes }} min
        {% if q.avg_percentage is not none %} · {{ "%.1f"|format(q.avg_percentage) }}%{% endif %}
        · {{ q.attempt_count }} attempt{{ 's' if q.attempt_count != 1 else '' }}
      </div>
      {% endfor %}

      <div class="ev-actions">
        {% if ev.type == "single" %}
        <form method="get" action="/evidence/pdf" style="display:inline">
          <input type="hidden" name="class_code" value="{{ class_code }}">
          <input type="hidden" name="quiz_code" value="{{ ev.quiz_codes[0] }}">
          {% if student_email %}<input type="hidden" name="student_email" value="{{ student_email }}">{% endif %}
          {{ pdf_options_html|safe }}
          <button type="submit" class="btn btn-green btn-sm" style="margin-top:.5rem">⬇ Download PDF</button>
        </form>
        {% else %}
        {% for qc in ev.quiz_codes %}
        <form method="get" action="/evidence/pdf" style="display:inline">
          <input type="hidden" name="class_code" value="{{ class_code }}">
          <input type="hidden" name="quiz_code" value="{{ qc }}">
          {% if student_email %}<input type="hidden" name="student_email" value="{{ student_email }}">{% endif %}
          {{ pdf_options_html|safe }}
          <button type="submit" class="btn btn-green btn-sm" style="margin-top:.5rem">⬇ {{ qc }}</button>
        </form>
        {% endfor %}
        {% endif %}
      </div>
    </div>
    {% endfor %}
  </div>
</div>

<div class="card">
  <h2>All Quizzes Analysed</h2>
  <table>
    <thead>
      <tr>
        <th>Quiz Code</th>
        <th>Est. Time (min)</th>
        <th>Avg %</th>
        <th>Suggested Grade</th>
        <th>Attempts</th>
        <th>Latest Attempt</th>
        <th>Actions</th>
      </tr>
    </thead>
    <tbody>
      {% for q in all_quizzes %}
      <tr>
        <td>{{ q.quiz_code }}</td>
        <td>~{{ q.est_minutes }}</td>
        <td>
          {% if q.avg_percentage is not none %}
          <div class="bar-wrap"><div class="bar-fill" style="width:{{ [q.avg_percentage,100]|min }}%"></div></div>
          {{ "%.1f"|format(q.avg_percentage) }}%
          {% else %}—{% endif %}
        </td>
        <td><span class="grade-badge grade-{{ grade_of(q.avg_percentage) }}">{{ grade_of(q.avg_percentage) }}</span></td>
        <td>{{ q.attempt_count }}</td>
        <td>{{ q.latest_date or "—" }}</td>
        <td>
          <form method="get" action="/evidence/pdf" style="display:inline">
            <input type="hidden" name="class_code" value="{{ class_code }}">
            <input type="hidden" name="quiz_code" value="{{ q.quiz_code }}">
            {% if student_email %}<input type="hidden" name="student_email" value="{{ student_email }}">{% endif %}
            {{ pdf_options_html|safe }}
            <button type="submit" class="btn btn-sm btn-green">⬇ PDF</button>
          </form>
        </td>
      </tr>
      {% endfor %}
    </tbody>
  </table>
</div>

{% if student_evidence %}
<div class="card">
  <h2>Per-Student Best Evidence
    <span class="time-badge">{{ student_evidence|length }} students</span>
  </h2>
  <div style="overflow-x:auto">
  <table>
    <thead>
      <tr>
        <th>Cand #</th>
        <th>Student</th>
        <th>#1 Evidence</th>
        <th>#2 Evidence</th>
        <th>#3 Evidence</th>
      </tr>
    </thead>
    <tbody>
      {% for s in student_evidence %}
      <tr>
        <td style="white-space:nowrap">{{ s.candidate_no or "—" }}</td>
        <td style="white-space:nowrap">
          {{ s.full_name or s.email }}
          {% if s.full_name %}<br><small style="color:#888">{{ s.email }}</small>{% endif %}
        </td>
        {% for i in range(3) %}
          {% if i < s.evidence|length %}
          {% set ev = s.evidence[i] %}
          <td style="min-width:200px;vertical-align:top">
            <div style="font-weight:700;font-size:.85rem;color:#0f3460;margin-bottom:.2rem">{{ ev.label }}</div>
            <div style="font-size:.8rem;color:#555;margin-bottom:.3rem">
              ~{{ ev.total_minutes }} min
              {% if ev.avg_percentage is not none %} &middot; {{ "%.0f"|format(ev.avg_percentage) }}%{% endif %}
            </div>
            <span class="grade-badge grade-{{ ev.grade }}" style="font-size:.8rem;margin-bottom:.4rem;display:inline-block">Grade {{ ev.grade }}</span>
            <div style="margin-top:.35rem;display:flex;flex-wrap:wrap;gap:.3rem">
              {% for qc in ev.quiz_codes %}
              <a href="/evidence/pdf?class_code={{ class_code }}&quiz_code={{ qc }}&student_email={{ s.email }}&inc_marks=1&inc_comments=1&inc_questions=1&inc_labels=1&margin_tb=15&margin_lr=15&img_pct=100&img_crop_pct=3&page_break=1"
                 class="btn btn-green btn-sm">⬇ {{ qc }}</a>
              {% endfor %}
            </div>
          </td>
          {% else %}
          <td style="color:#ccc;text-align:center;vertical-align:middle">—</td>
          {% endif %}
        {% endfor %}
      </tr>
      {% endfor %}
    </tbody>
  </table>
  </div>
</div>
{% endif %}

{% endif %}
"""


# ---------------------------------------------------------------------------
# PDF generation
# ---------------------------------------------------------------------------

def _download_image(url: str) -> io.BytesIO | None:
    """Download image URL and return as BytesIO, or None on failure."""
    try:
        r = requests.get(url, timeout=20)
        r.raise_for_status()
        buf = io.BytesIO(r.content)
        buf.seek(0)
        return buf
    except Exception:
        return None


def _is_image_only_response(answer) -> bool:
    """
    Detect if the student response is image-only:
    - answer is a string URL/data-url pointing to an image, OR
    - answer is a dict with an image key but no text, OR
    - answer text equals the question text (image-copied response)
    """
    if answer is None:
        return False
    if isinstance(answer, str):
        low = answer.lower().strip()
        return low.startswith("http") and any(
            ext in low for ext in (".jpg", ".jpeg", ".png", ".gif", ".webp", "/image", "image/")
        )
    if isinstance(answer, dict):
        has_image = bool(answer.get("image_url") or answer.get("image"))
        has_text  = bool(str(answer.get("text", "")).strip())
        return has_image and not has_text
    return False


def _answer_image_url(answer) -> str | None:
    if isinstance(answer, str) and answer.lower().startswith("http"):
        return answer
    if isinstance(answer, dict):
        return answer.get("image_url") or answer.get("image")
    return None


def _answer_text(answer) -> str:
    if answer is None:
        return ""
    if isinstance(answer, str):
        return answer
    if isinstance(answer, dict):
        return answer.get("text", "") or ""
    return str(answer)


def generate_pdf(
    class_code: str,
    quiz_code: str,
    attempts_data: list,
    candidate_map: dict,
    *,
    inc_marks: bool = True,
    inc_comments: bool = True,
    inc_questions: bool = True,
    inc_labels: bool = True,
    margin_tb: float = 15,
    margin_lr: float = 15,
    img_pct: float = 100,
    img_crop_pct: float = 3.0,
    page_break_between: bool = True,
) -> io.BytesIO:
    buf = io.BytesIO()

    page_w, page_h = A4
    usable_w = page_w - 2 * margin_lr * mm

    doc = SimpleDocTemplate(
        buf,
        pagesize=A4,
        topMargin=margin_tb * mm,
        bottomMargin=margin_tb * mm,
        leftMargin=margin_lr * mm,
        rightMargin=margin_lr * mm,
    )

    styles = getSampleStyleSheet()
    style_h1    = ParagraphStyle("H1",    fontSize=14, fontName="Helvetica-Bold",   spaceAfter=4,  textColor=colors.HexColor("#0f3460"))
    style_h2    = ParagraphStyle("H2",    fontSize=11, fontName="Helvetica-Bold",   spaceAfter=3,  textColor=colors.HexColor("#16213e"))
    style_h3    = ParagraphStyle("H3",    fontSize=10, fontName="Helvetica-Bold",   spaceAfter=2,  textColor=colors.HexColor("#374151"))
    style_body  = ParagraphStyle("Body",  fontSize=9,  fontName="Helvetica",        spaceAfter=2,  leading=13)
    style_small = ParagraphStyle("Small", fontSize=8,  fontName="Helvetica",        textColor=colors.HexColor("#6b7280"), spaceAfter=2)
    style_label = ParagraphStyle("Label", fontSize=8,  fontName="Helvetica-Bold",   textColor=colors.HexColor("#0f3460"))
    style_comment = ParagraphStyle("Cmt", fontSize=8,  fontName="Helvetica-Oblique",textColor=colors.HexColor("#374151"), spaceAfter=2, leading=12)

    story = []

    # Cover / header
    story.append(Paragraph(f"Evidence Pack — {class_code} / {quiz_code}", style_h1))
    story.append(HRFlowable(width="100%", thickness=1, color=colors.HexColor("#0f3460"), spaceAfter=6))

    for idx, attempt in enumerate(attempts_data):
        email      = attempt.get("student_email", "")
        cand       = candidate_map.get(email.lower(), {})
        full_name  = f"{cand.get('forename','')} {cand.get('surname','')}".strip() or email
        cand_no    = cand.get("candidate_no", "—")
        form       = cand.get("form", "—")
        year       = cand.get("year_group", "—")
        uci        = cand.get("uci", "—")

        awarded    = attempt.get("marks_awarded")
        possible   = attempt.get("marks_possible")
        percentage = attempt.get("percentage")

        # Try multiple possible key names for the questions list
        questions = (
            attempt.get("questions")
            or attempt.get("question_list")
            or attempt.get("responses")
            or attempt.get("answers")
            or attempt.get("items")
            or attempt.get("quiz_responses")
            or []
        )

        # Student header block
        header_data = [
            [Paragraph("Name", style_label),        Paragraph(full_name, style_body),
             Paragraph("Candidate #", style_label),  Paragraph(cand_no, style_body)],
            [Paragraph("Email", style_label),        Paragraph(email, style_body),
             Paragraph("Form / Year", style_label),  Paragraph(f"{form} — {year}", style_body)],
            [Paragraph("UCI", style_label),          Paragraph(uci, style_body),
             Paragraph("Quiz", style_label),         Paragraph(quiz_code, style_body)],
        ]
        if inc_marks and awarded is not None:
            pct_str = f"{percentage:.1f}%" if percentage is not None else "—"
            header_data.append([
                Paragraph("Marks", style_label),
                Paragraph(f"{awarded} / {possible}", style_body),
                Paragraph("Percentage", style_label),
                Paragraph(pct_str, style_body),
            ])

        col_w = usable_w / 4
        tbl = Table(header_data, colWidths=[col_w * 0.7, col_w * 1.3, col_w * 0.7, col_w * 1.3])
        tbl.setStyle(TableStyle([
            ("BACKGROUND", (0, 0), (-1, -1), colors.HexColor("#f0f4ff")),
            ("BOX",        (0, 0), (-1, -1), 0.5, colors.HexColor("#c7d2fe")),
            ("INNERGRID",  (0, 0), (-1, -1), 0.3, colors.HexColor("#e0e7ff")),
            ("VALIGN",     (0, 0), (-1, -1), "MIDDLE"),
            ("TOPPADDING",    (0, 0), (-1, -1), 4),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
            ("LEFTPADDING",   (0, 0), (-1, -1), 6),
        ]))
        story.append(KeepTogether([tbl]))
        story.append(Spacer(1, 6 * mm))

        # Questions
        if not questions:
            story.append(Paragraph(
                "⚠ No question/answer data was returned by the API for this attempt. "
                "Visit /debug/attempt?class_code=…&quiz_code=… to inspect the raw response.",
                ParagraphStyle("Warn", fontSize=9, textColor=colors.HexColor("#991b1b"),
                               fontName="Helvetica-Oblique")
            ))
            story.append(Spacer(1, 4 * mm))

        for q_idx, q in enumerate(questions, 1):
            q_text     = q.get("question") or ""
            q_image    = q.get("question_image_url") or ""
            ans_text   = q.get("answer_text") or ""
            ans_image  = q.get("answer_image_url") or ""
            q_marks    = q.get("marks")           # marks awarded
            q_possible = q.get("maxmarks")        # max marks
            comment    = q.get("comment") or ""
            has_image  = q.get("has_image", False)

            # Image-only response: answer_image_url is set, or has_image=True with no answer_text
            is_img_ans = bool(ans_image) or (has_image and not ans_text.strip())

            # answer_raw kept for helper compatibility
            answer_raw = ans_image if is_img_ans else ans_text

            q_block = []

            # Question header
            q_label = f"Q{q_idx}"
            if inc_marks and q_possible is not None:
                q_label += f"  [{q_marks if q_marks is not None else '—'} / {q_possible} marks]"
            q_block.append(Paragraph(q_label, style_h3))

            # Question text / image
            if inc_questions:
                if q_text:
                    for line in q_text.split("\n"):
                        if line.strip():
                            q_block.append(Paragraph(line, style_body))
                if q_image:
                    img_buf = _download_image(q_image)
                    if img_buf:
                        try:
                            pil = PILImage.open(img_buf)
                            iw, ih = pil.size
                            img_buf.seek(0)
                            disp_w = min(usable_w * (img_pct / 100), usable_w)
                            disp_h = ih * (disp_w / iw)
                            q_block.append(RLImage(img_buf, width=disp_w, height=disp_h))
                        except Exception:
                            q_block.append(Paragraph("[Question image could not be loaded]", style_small))

            # Separator
            q_block.append(Paragraph("Student response:", style_label))

            # Student answer
            if is_img_ans:
                img_buf = _download_image(ans_image)
                if img_buf:
                    try:
                        pil = PILImage.open(img_buf)
                        iw, ih = pil.size
                        img_buf.seek(0)
                        disp_w = min(usable_w * (img_pct / 100), usable_w)
                        disp_h = ih * (disp_w / iw)
                        q_block.append(RLImage(img_buf, width=disp_w, height=disp_h))
                    except Exception:
                        q_block.append(Paragraph("[Response image could not be loaded]", style_small))
                else:
                    q_block.append(Paragraph("[Image response — could not download]", style_small))
            else:
                if ans_text:
                    for line in ans_text.split("\n"):
                        q_block.append(Paragraph(line or " ", style_body))
                else:
                    q_block.append(Paragraph("(no response)", style_small))

            # Examiner comment
            if inc_comments and comment:
                q_block.append(Spacer(1, 2 * mm))
                q_block.append(Paragraph(f"Examiner comment: {comment}", style_comment))

            q_block.append(HRFlowable(width="100%", thickness=0.4, color=colors.HexColor("#d1d5db"), spaceAfter=4))
            story.append(KeepTogether(q_block))

        # Page break between students
        if page_break_between and idx < len(attempts_data) - 1:
            from reportlab.platypus import PageBreak
            story.append(PageBreak())
        else:
            story.append(Spacer(1, 10 * mm))

    doc.build(story)
    buf.seek(0)
    return buf


# ---------------------------------------------------------------------------
# Flask routes
# ---------------------------------------------------------------------------

@app.route("/")
def index():
    class_code = request.args.get("class_code", "").strip()
    quiz_code  = request.args.get("quiz_code", "").strip()

    data      = None
    attempts  = []
    error     = None
    est_minutes = None

    if class_code and quiz_code:
        try:
            data = fetch_grades(class_code, quiz_code)
            raw  = data.get("attempts", [])

            # Enrich with candidate DB lookup
            rows = []
            for a in sorted(raw, key=lambda x: x.get("student_email", "")):
                email   = a.get("student_email", "unknown")
                cand    = lookup_candidate(email) or {}
                awarded = a.get("marks_awarded")
                possible = a.get("marks_possible")
                fully   = a.get("fully_marked", False)
                unmarked = a.get("questions_unmarked", 0)

                if fully:
                    status = "Marked"
                elif unmarked > 0:
                    status = f"{unmarked} unmarked"
                else:
                    status = "Partial"

                full_name = f"{cand.get('forename','')} {cand.get('surname','')}".strip()
                rows.append({
                    "email":        email,
                    "attempt_id":   a.get("id") or a.get("attempt_id", ""),
                    "candidate_no": cand.get("candidate_no", ""),
                    "full_name":    full_name,
                    "marks_str":    f"{awarded}/{possible}" if awarded is not None else "—/—",
                    "marks_possible": possible,
                    "percentage":   a.get("percentage"),
                    "status":       status,
                })
            attempts = rows

            # Estimate time: max marks possible for first attempt with data
            max_marks = next(
                (r["marks_possible"] for r in rows if r["marks_possible"] is not None), None
            )
            if max_marks is not None:
                est_minutes = max_marks  # 1 mark ≈ 1 minute

        except requests.HTTPError as e:
            body = {}
            try:
                body = e.response.json()
            except Exception:
                pass
            error = f"API error {e.response.status_code}: {body.get('error', str(e))}"
        except requests.RequestException as e:
            error = f"Request failed: {e}"

    return render_template_string(
        INDEX_TEMPLATE,
        class_code=class_code,
        quiz_code=quiz_code,
        data=data,
        attempts=attempts,
        error=error,
        est_minutes=est_minutes,
    )


@app.route("/pdf")
def pdf():
    class_code   = request.args.get("class_code", "").strip()
    quiz_code    = request.args.get("quiz_code", "").strip()
    student_email = request.args.get("student_email", "").strip().lower()

    inc_marks     = bool(request.args.get("inc_marks"))
    inc_comments  = bool(request.args.get("inc_comments"))
    inc_questions = bool(request.args.get("inc_questions"))
    inc_labels    = bool(request.args.get("inc_labels"))
    margin_tb     = float(request.args.get("margin_tb", 15))
    margin_lr     = float(request.args.get("margin_lr", 15))
    img_pct       = float(request.args.get("img_pct", 100))
    img_crop_pct  = float(request.args.get("img_crop_pct", 3))
    page_break    = request.args.get("page_break", "1") == "1"

    if not class_code or not quiz_code:
        return "Missing class_code or quiz_code", 400

    try:
        data = fetch_grades(class_code, quiz_code, include_questions=True)
    except requests.HTTPError as e:
        return f"API error: {e}", 502
    except requests.RequestException as e:
        return f"Request failed: {e}", 502

    attempts_raw = data.get("attempts", [])
    if student_email:
        attempts_raw = [a for a in attempts_raw if a.get("student_email", "").lower() == student_email]

    # Normalise question key — API may use different names
    enriched = []
    for a in attempts_raw:
        if not a.get("questions"):
            for alt in ("question_list", "responses", "answers", "items", "quiz_responses"):
                if a.get(alt):
                    a = {**a, "questions": a[alt]}
                    break
        enriched.append(a)

    print(f"[PDF] {len(enriched)} attempt(s). First has {len(enriched[0].get('questions', []))} questions." if enriched else "[PDF] No attempts.")

    # Build candidate lookup map
    emails = [a.get("student_email", "").lower() for a in enriched]
    db = get_db()
    candidate_map = {}
    for em in emails:
        row = db.execute("SELECT * FROM candidates WHERE email=?", (em,)).fetchone()
        if row:
            candidate_map[em] = dict(row)

    pdf_buf = generate_pdf(
        class_code, quiz_code, enriched, candidate_map,
        inc_marks=inc_marks,
        inc_comments=inc_comments,
        inc_questions=inc_questions,
        inc_labels=inc_labels,
        margin_tb=margin_tb,
        margin_lr=margin_lr,
        img_pct=img_pct,
        img_crop_pct=img_crop_pct,
        page_break_between=page_break,
    )

    filename = f"evidence_{class_code}_{quiz_code}.pdf".replace(" ", "_")
    return send_file(pdf_buf, mimetype="application/pdf",
                     as_attachment=True, download_name=filename)


@app.route("/admin/reimport-candidates")
def reimport_candidates():
    init_db()
    return "Candidates re-imported successfully.", 200


@app.route("/evidence")
def evidence():
    class_code    = request.args.get("class_code", "").strip()
    student_email = request.args.get("student_email", "").strip().lower()
    target_min    = int(request.args.get("target_min", 50))
    target_max    = int(request.args.get("target_max", 70))
    manual_codes  = request.args.get("quiz_codes", "").strip()
    months_ago_raw = request.args.get("months_ago", "").strip()
    months_ago    = int(months_ago_raw) if months_ago_raw.isdigit() else None
    spec_code     = request.args.get("spec_code", "").strip()

    ev_results      = []
    all_quizzes     = []
    student_evidence = []
    error           = None
    quizzes_checked = 0

    if class_code:
        try:
            infos, raw_by_quiz = discover_quiz_summaries(class_code, manual_codes, months_ago, spec_code)
            quizzes_checked = len(infos)
            all_quizzes = sorted(infos, key=lambda x: x["est_minutes"], reverse=True)
            ev_results = find_best_evidence(infos, target_min=target_min, target_max=target_max, top_n=3)
            student_evidence = compute_per_student_evidence(raw_by_quiz, target_min, target_max, top_n=3)
            # Enrich with candidate DB info
            db = get_db()
            for s in student_evidence:
                row = db.execute("SELECT * FROM candidates WHERE email=?", (s["email"],)).fetchone()
                if row:
                    row = dict(row)
                    s["candidate_no"] = row.get("candidate_no", "—")
                    s["full_name"] = f"{row.get('forename','')} {row.get('surname','')}".strip()
                else:
                    s["candidate_no"] = "—"
                    s["full_name"] = ""
        except requests.HTTPError as e:
            body = {}
            try: body = e.response.json()
            except Exception: pass
            error = f"API error {e.response.status_code}: {body.get('error', str(e))}"
        except requests.RequestException as e:
            error = f"Request failed: {e}"
        except Exception as e:
            error = f"Error: {e}"

        if class_code and not error and not all_quizzes:
            error = (
                "No quizzes were detected automatically. "
                "This usually means the attempt records don't include a quiz_code field. "
                f"Check <a href='/debug/attempt?class_code={class_code}&quiz_code=test'>the debug endpoint</a> "
                "to see the raw attempt structure, then enter quiz codes manually above."
            )

    # Build hidden PDF options HTML (no student-specific inputs here — added per-form in template)
    pdf_options_html = """
<input type="hidden" name="inc_marks" value="1">
<input type="hidden" name="inc_comments" value="1">
<input type="hidden" name="inc_questions" value="1">
<input type="hidden" name="inc_labels" value="1">
<input type="hidden" name="margin_tb" value="15">
<input type="hidden" name="margin_lr" value="15">
<input type="hidden" name="img_pct" value="100">
<input type="hidden" name="img_crop_pct" value="3">
<input type="hidden" name="page_break" value="1">
"""

    return render_template_string(
        EVIDENCE_TEMPLATE,
        class_code=class_code,
        student_email=student_email,
        target_min=target_min,
        target_max=target_max,
        quiz_codes=manual_codes,
        months_ago=months_ago_raw,
        spec_code=spec_code,
        evidence=ev_results,
        all_quizzes=all_quizzes,
        quizzes_checked=quizzes_checked,
        student_evidence=student_evidence,
        error=error,
        pdf_options_html=pdf_options_html,
        grade_of=grade_suggestion,
    )


@app.route("/evidence/pdf")
def evidence_pdf():
    """PDF download triggered from the evidence tab — proxies to /pdf logic."""
    # Reuse the same /pdf handler parameters
    class_code    = request.args.get("class_code", "").strip()
    quiz_code     = request.args.get("quiz_code", "").strip()
    student_email = request.args.get("student_email", "").strip().lower()

    inc_marks     = bool(request.args.get("inc_marks"))
    inc_comments  = bool(request.args.get("inc_comments"))
    inc_questions = bool(request.args.get("inc_questions"))
    inc_labels    = bool(request.args.get("inc_labels"))
    margin_tb     = float(request.args.get("margin_tb", 15))
    margin_lr     = float(request.args.get("margin_lr", 15))
    img_pct       = float(request.args.get("img_pct", 100))
    img_crop_pct  = float(request.args.get("img_crop_pct", 3))
    page_break    = request.args.get("page_break", "1") == "1"

    if not class_code or not quiz_code:
        return "Missing class_code or quiz_code", 400

    try:
        data = fetch_grades(class_code, quiz_code, include_questions=True)
    except requests.HTTPError as e:
        return f"API error: {e}", 502
    except requests.RequestException as e:
        return f"Request failed: {e}", 502

    attempts_raw = data.get("attempts", [])
    if student_email:
        attempts_raw = [a for a in attempts_raw if a.get("student_email", "").lower() == student_email]

    enriched = []
    for a in attempts_raw:
        if not a.get("questions"):
            for alt in ("question_list", "responses", "answers", "items", "quiz_responses"):
                if a.get(alt):
                    a = {**a, "questions": a[alt]}
                    break
        enriched.append(a)

    emails = [a.get("student_email", "").lower() for a in enriched]
    db = get_db()
    candidate_map = {}
    for em in emails:
        row = db.execute("SELECT * FROM candidates WHERE email=?", (em,)).fetchone()
        if row:
            candidate_map[em] = dict(row)

    pdf_buf = generate_pdf(
        class_code, quiz_code, enriched, candidate_map,
        inc_marks=inc_marks,
        inc_comments=inc_comments,
        inc_questions=inc_questions,
        inc_labels=inc_labels,
        margin_tb=margin_tb,
        margin_lr=margin_lr,
        img_pct=img_pct,
        img_crop_pct=img_crop_pct,
        page_break_between=page_break,
    )

    filename = f"evidence_{class_code}_{quiz_code}.pdf".replace(" ", "_")
    return send_file(pdf_buf, mimetype="application/pdf",
                     as_attachment=True, download_name=filename)


@app.route("/debug/all-attempts")
def debug_all_attempts():
    """Show raw keys from unfiltered attempts endpoint. Usage: /debug/all-attempts?class_code=X"""
    import json
    class_code = request.args.get("class_code", "").strip()
    if not class_code:
        return "Pass ?class_code=X", 400
    try:
        attempts = fetch_all_attempts(class_code)
        out = {
            "total_attempts": len(attempts),
            "first_attempt_keys": list(attempts[0].keys()) if attempts else [],
            "first_attempt_sample": attempts[0] if attempts else None,
            "unique_quiz_code_values": list({
                a.get("quiz_code") or a.get("quiz") or a.get("quiz_id") or a.get("quiz_name") or "(none)"
                for a in attempts[:50]
            }),
        }
        # Also show question spec fields from first attempt with questions
        try:
            first_qc = out["unique_quiz_code_values"][0] if out["unique_quiz_code_values"] else None
            if first_qc and first_qc != "(none)":
                qdata = fetch_grades(class_code, first_qc, include_questions=True)
                qattempts = qdata.get("attempts", [])
                if qattempts:
                    qs = (qattempts[0].get("questions") or [])
                    if qs:
                        out["sample_question_keys"] = list(qs[0].keys())
                        out["sample_question_spec_fields"] = {
                            k: qs[0][k] for k in _SPEC_FIELDS if k in qs[0]
                        }
        except Exception:
            pass
    except Exception as e:
        out = {"error": str(e)}
    return app.response_class(json.dumps(out, indent=2, default=str), mimetype="application/json")


@app.route("/debug/attempt")
def debug_attempt():
    """
    Diagnostic route — shows raw API responses so we can discover correct field names.
    Usage: /debug/attempt?class_code=X&quiz_code=Y
    """
    import json
    class_code = request.args.get("class_code", "").strip()
    quiz_code  = request.args.get("quiz_code", "").strip()
    if not class_code or not quiz_code:
        return "Pass ?class_code=X&quiz_code=Y", 400

    out = {}
    try:
        # Without questions
        grades_data = fetch_grades(class_code, quiz_code, include_questions=False)
        attempts    = grades_data.get("attempts", [])
        out["grades_response_keys"] = list(grades_data.keys())

        if attempts:
            first = attempts[0]
            out["first_attempt_keys"]   = list(first.keys())
            out["first_attempt_sample"] = first
        else:
            out["note"] = "No attempts found"
            return app.response_class(json.dumps(out, indent=2, default=str), mimetype="application/json")

        # With include_questions=true
        grades_with_q = fetch_grades(class_code, quiz_code, include_questions=True)
        attempts_with_q = grades_with_q.get("attempts", [])
        if attempts_with_q:
            first_q = attempts_with_q[0]
            out["first_attempt_with_questions_keys"]   = list(first_q.keys())
            out["questions_count"]                     = len(first_q.get("questions", []))
            # Show first question structure only
            qs = first_q.get("questions") or []
            out["first_question_sample"] = qs[0] if qs else None
            out["first_question_keys"]   = list(qs[0].keys()) if qs else []
        else:
            out["note_with_q"] = "No attempts returned when include_questions=true"
    except Exception as e:
        out["error"] = str(e)

    return app.response_class(
        json.dumps(out, indent=2, default=str),
        mimetype="application/json"
    )


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    if not os.path.exists(DB_PATH):
        init_db()
    app.run(debug=True)


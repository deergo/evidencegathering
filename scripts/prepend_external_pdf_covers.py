from __future__ import annotations

import argparse
import csv
import io
import os
import re
import subprocess
from pathlib import Path

from pypdf import PdfReader, PdfWriter
from reportlab.lib.colors import black
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.pdfgen import canvas


WORKSPACE_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EVIDENCE_ROOT = Path("/home/ashraf/Documents/worktodel/evidence 0984")
DEFAULT_CANDIDATES_CSV = WORKSPACE_ROOT / "candidates.csv"
DISPLAY_COMPONENT_FOLDERS = {
  "mocky11cs",
  "y10EOY",
  "interimnov2025",
  "schoolasessment",
}
FILE_PATTERN = re.compile(
  r"^June2026_0984_(?P<component>12|22)_BH010_(?P<candidate>\d+)_.+\.pdf$",
  re.IGNORECASE,
)
COVER_FONT_NAME = "EvidenceCoverFont"


def parse_args() -> argparse.Namespace:
  parser = argparse.ArgumentParser(description="Prepend cover pages to external evidence PDFs.")
  parser.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
  parser.add_argument("--candidates-csv", type=Path, default=DEFAULT_CANDIDATES_CSV)
  parser.add_argument("--candidate-no", action="append", default=[])
  parser.add_argument("--dry-run", action="store_true")
  parser.add_argument("--refresh-existing", action="store_true")
  return parser.parse_args()


def load_candidate_names(csv_path: Path) -> dict[str, str]:
  names: dict[str, str] = {}
  with csv_path.open(newline="", encoding="utf-8-sig") as handle:
    reader = csv.DictReader(handle)
    for row in reader:
      candidate_no = str(row.get("Candidate #") or "").strip()
      if not candidate_no:
        continue
      forename = str(row.get("Forename") or "").strip()
      surname = str(row.get("Surname") or "").strip()
      full_name = " ".join(part for part in [forename, surname] if part).strip()
      if full_name:
        names[candidate_no] = full_name
  return names


def iter_pdfs(evidence_root: Path) -> list[Path]:
  return sorted(path for path in evidence_root.rglob("*.pdf") if path.is_file())


def extract_file_info(pdf_path: Path) -> tuple[str, str]:
  match = FILE_PATTERN.match(pdf_path.name)
  if not match:
    raise ValueError(f"Filename does not match expected pattern: {pdf_path.name}")
  return match.group("component"), match.group("candidate")


def build_component_display(folder_name: str, component_code: str) -> str:
  if folder_name == "Paper2evidence":
    return "22"
  if component_code == "12" and folder_name in DISPLAY_COMPONENT_FOLDERS:
    return "12/22"
  return component_code


def locate_unicode_font() -> str | None:
  try:
    result = subprocess.run(
      ["fc-match", "-f", "%{file}\n", "DejaVu Sans"],
      check=True,
      capture_output=True,
      text=True,
    )
    font_path = result.stdout.strip()
    if font_path and Path(font_path).is_file():
      return font_path
  except Exception:
    pass

  fallback_paths = [
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    "/usr/local/share/fonts/DejaVuSans.ttf",
  ]
  for font_path in fallback_paths:
    if Path(font_path).is_file():
      return font_path
  return None


def get_cover_font_name() -> str:
  try:
    pdfmetrics.getFont(COVER_FONT_NAME)
    return COVER_FONT_NAME
  except KeyError:
    pass

  font_path = locate_unicode_font()
  if not font_path:
    return "Helvetica"

  pdfmetrics.registerFont(TTFont(COVER_FONT_NAME, font_path))
  return COVER_FONT_NAME


def build_cover_page(first_page_width: float, first_page_height: float, lines: list[str]) -> PdfReader:
  buffer = io.BytesIO()
  pdf = canvas.Canvas(buffer, pagesize=(first_page_width, first_page_height))
  pdf.setFillColor(black)
  pdf.setFont(get_cover_font_name(), 18)

  line_height = 30
  start_y = (first_page_height / 2) + (line_height * (len(lines) - 1) / 2)
  for index, line in enumerate(lines):
    pdf.drawCentredString(first_page_width / 2, start_y - (index * line_height), line)

  pdf.showPage()
  pdf.save()
  buffer.seek(0)
  return PdfReader(buffer)


def already_has_cover(first_page, expected_lines: list[str]) -> bool:
  try:
    text = (first_page.extract_text() or "").replace("\r", "")
  except Exception:
    return False
  return all(line in text for line in expected_lines)


def is_generated_cover_page(page, component_display: str, candidate_no: str) -> bool:
  try:
    text = (page.extract_text() or "").replace("\r", "")
  except Exception:
    return False
  markers = [
    "June2026",
    "BH010",
    "St Christopher's School Bahrain",
    f"0984/{component_display}",
    candidate_no,
  ]
  return all(marker in text for marker in markers)


def count_leading_cover_pages(reader: PdfReader, component_display: str, candidate_no: str) -> int:
  cover_count = 0
  for page in reader.pages:
    if not is_generated_cover_page(page, component_display, candidate_no):
      break
    cover_count += 1
  return cover_count


def prepend_cover_page(
  pdf_path: Path,
  candidate_name: str,
  component_display: str,
  candidate_no: str,
  dry_run: bool,
  refresh_existing: bool,
) -> str:
  with pdf_path.open("rb") as source_handle:
    reader = PdfReader(source_handle)
    if not reader.pages:
      raise ValueError(f"PDF has no pages: {pdf_path}")

    first_page = reader.pages[0]
    page_width = float(first_page.mediabox.width)
    page_height = float(first_page.mediabox.height)
    cover_lines = [
      "June2026",
      "BH010",
      "St Christopher's School Bahrain",
      f"0984/{component_display}",
      candidate_no,
      candidate_name,
    ]

    leading_cover_pages = count_leading_cover_pages(reader, component_display, candidate_no)
    has_cover_metadata = str((reader.metadata or {}).get("/EvidenceCoverPage") or "") == "June2026"
    if (leading_cover_pages or has_cover_metadata) and not refresh_existing:
      return "skipped-existing-cover"

    if dry_run:
      return "dry-run"

    cover_reader = build_cover_page(page_width, page_height, cover_lines)
    writer = PdfWriter()
    writer.append(cover_reader)
    start_index = leading_cover_pages if refresh_existing else 0
    for page in reader.pages[start_index:]:
      writer.add_page(page)
    if reader.metadata:
      writer.add_metadata({key: str(value) for key, value in reader.metadata.items() if value is not None})
    writer.add_metadata({"/EvidenceCoverPage": "June2026"})

    temp_path = pdf_path.with_suffix(pdf_path.suffix + ".tmp")
    with temp_path.open("wb") as output_handle:
      writer.write(output_handle)
    os.replace(temp_path, pdf_path)
    return "updated"


def main() -> int:
  args = parse_args()
  evidence_root = args.evidence_root.resolve()
  candidates_csv = args.candidates_csv.resolve()

  if not evidence_root.is_dir():
    raise SystemExit(f"Evidence root not found: {evidence_root}")
  if not candidates_csv.is_file():
    raise SystemExit(f"Candidates CSV not found: {candidates_csv}")

  candidate_names = load_candidate_names(candidates_csv)
  selected_candidates = {str(candidate_no).strip() for candidate_no in args.candidate_no if str(candidate_no).strip()}
  pdf_paths = iter_pdfs(evidence_root)
  updated = 0
  skipped = 0

  for pdf_path in pdf_paths:
    component_code, candidate_no = extract_file_info(pdf_path)
    if selected_candidates and candidate_no not in selected_candidates:
      continue
    candidate_name = candidate_names.get(candidate_no)
    if not candidate_name:
      raise SystemExit(f"No candidate name found for {candidate_no} in {pdf_path}")

    component_display = build_component_display(pdf_path.parent.name, component_code)
    result = prepend_cover_page(
      pdf_path=pdf_path,
      candidate_name=candidate_name,
      component_display=component_display,
      candidate_no=candidate_no,
      dry_run=args.dry_run,
      refresh_existing=args.refresh_existing,
    )
    if result == "updated":
      updated += 1
    elif result == "skipped-existing-cover":
      skipped += 1
    print(f"{result}: {pdf_path}")

  print(f"processed={len(pdf_paths)} updated={updated} skipped={skipped}")
  return 0


if __name__ == "__main__":
  raise SystemExit(main())
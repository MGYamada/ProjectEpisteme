"""Check the alg-d ledgers against the source index, the coverage report, and the Lean library.

    python3 checks/ledger.py           # check; exit status 1 if anything is wrong
    python3 checks/ledger.py --write   # regenerate the generated files, then check

`--write` regenerates the marked blocks of `docs/algd-coverage.md` and the Lean check
`checks/LedgerDeclarations.lean`. The check mode fails if either is out of date.

The checks follow `docs/Project_Episteme_Category_Strategy.md`, section 6:

* every ledger row has nine cells, a well-formed and unique ID, and a known kind and status;
* the numbered rows cover 1..max exactly, and the header counts match the rows;
* the header's date, pages, hash, numbering and `定義.` count match `docs/algd-source-index.md`;
* every verified row (`existing`, `bridged`, `new-proved`) names a fully qualified Lean
  declaration, and every `unreviewed` row names none;
* every source ID in a Lean docstring belongs to a verified row naming that declaration, and
  every verified row naming a `ProjectEpisteme` declaration has its ID in that docstring;
* relative links and their heading anchors in the Markdown files resolve.

Only the Python standard library is used.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
import re
import sys

KINDS = {
    "definition", "theorem", "proposition", "lemma", "corollary", "example", "remark",
    "equation", "prose-claim", "exercise",
}
STATUSES = {"unreviewed", "existing", "bridged", "new-proved", "blocked", "non-propositional"}
VERIFIED = ("existing", "bridged", "new-proved")
STATUS_ORDER = ("unreviewed", "existing", "bridged", "new-proved", "blocked", "non-propositional")

LEDGER_DIR = Path("docs/ledger/algd")
SOURCE_INDEX = Path("docs/algd-source-index.md")
COVERAGE = Path("docs/algd-coverage.md")
LEAN_CHECK = Path("checks/LedgerDeclarations.lean")
LEAN_ROOTS = (Path("ProjectEpisteme"),)
MARKDOWN = ("README.md", "AGENTS.md", "docs")

ID_RE = re.compile(r"^ALGD-C(\d)-([A-Z0-9]+)-(\d{2}|[DRE]\d{2})$")
CELL_SPLIT = re.compile(r"(?<!\\)\|")
NAME_RE = re.compile(r"`([^`\s]+)`")


@dataclass
class Row:
    cells: list[str]
    line: int

    @property
    def id(self) -> str:
        return self.cells[0]

    @property
    def kind(self) -> str:
        return self.cells[1].split(" ")[0]

    @property
    def status(self) -> str:
        return self.cells[6]

    @property
    def lean(self) -> str:
        return self.cells[5]

    @property
    def declaration(self) -> str | None:
        match = NAME_RE.search(self.lean)
        return match.group(1) if match else None

    @property
    def suffix(self) -> str:
        return self.id.rsplit("-", 1)[1]


@dataclass
class Ledger:
    path: Path
    chapter: int
    slug: str
    header: dict[str, str] = field(default_factory=dict)
    rows: list[Row] = field(default_factory=list)

    @property
    def name(self) -> str:
        return self.path.stem

    @property
    def prefix(self) -> str:
        return f"ALGD-C{self.chapter}-{self.slug}"

    def numbered(self) -> list[Row]:
        return [row for row in self.rows if row.suffix.isdigit()]

    def count(self, letter: str) -> int:
        return sum(1 for row in self.rows if row.suffix.startswith(letter))


@dataclass
class Source:
    chapter: str
    slug: str
    file: str
    date: str
    pages: int
    numbered: int
    definitions: int
    sha: str


def split_row(line: str) -> list[str]:
    return [cell.strip() for cell in CELL_SPLIT.split(line.strip())[1:-1]]


def leading_int(text: str) -> int | None:
    match = re.match(r"\s*(\d+)", text)
    return int(match.group(1)) if match else None


def read_ledger(root: Path, path: Path) -> tuple[Ledger | None, list[str]]:
    match = re.fullmatch(r"C(\d)-([A-Z0-9]+)", path.stem)
    where = path.relative_to(root)
    if not match:
        return None, [f"{where}: file name must be C<chapter>-<SLUG>.md"]
    ledger = Ledger(path=where, chapter=int(match.group(1)), slug=match.group(2))
    lines = path.read_text(encoding="utf-8").splitlines()
    errors = []
    if not lines or not lines[0].startswith(f"# {ledger.prefix} — "):
        errors.append(f"{where}:1: title must start with '# {ledger.prefix} — '")
    for number, line in enumerate(lines, start=1):
        if line.startswith("| ALGD-"):
            ledger.rows.append(Row(split_row(line), number))
        elif line.startswith("| ") and not line.startswith("| ---"):
            cells = split_row(line)
            if len(cells) == 2 and not ledger.rows:
                ledger.header[cells[0]] = cells[1]
    return ledger, errors


def read_sources(root: Path) -> tuple[dict[str, Source], list[str]]:
    sources: dict[str, Source] = {}
    errors = []
    chapter = None
    path = root / SOURCE_INDEX
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        heading = re.match(r"## (?:Chapter (\d)|(Supplementary))", line)
        if heading:
            chapter = heading.group(1) or "SUP"
            continue
        if line.startswith("## "):
            chapter = None
            continue
        if chapter is None or not line.startswith("| ") or line.startswith("| ---"):
            continue
        cells = split_row(line)
        if len(cells) != 10 or cells[0] == "Slug":
            continue
        file = re.match(r"\[([^\]]+)\]", cells[1])
        try:
            sources[cells[0]] = Source(
                chapter=chapter, slug=cells[0], file=file.group(1) if file else cells[1],
                date=cells[4], pages=int(cells[6]), numbered=int(cells[7]),
                definitions=int(cells[8]), sha=cells[9].strip("`"))
        except ValueError:
            errors.append(f"{SOURCE_INDEX}:{number}: malformed source row")
    return sources, errors


def check_ledger(ledger: Ledger, sources: dict[str, Source]) -> list[str]:
    errors = []
    where = ledger.path

    def error(row: Row | None, message: str) -> None:
        errors.append(f"{where}:{row.line if row else 1}: {message}")

    seen = Counter(row.id for row in ledger.rows)
    for row in ledger.rows:
        if len(row.cells) != 9:
            error(row, f"{row.cells[0] if row.cells else '?'} has {len(row.cells)} cells, not 9")
            continue
        match = ID_RE.match(row.id)
        if not match or not row.id.startswith(ledger.prefix + "-"):
            error(row, f"{row.id} is not a well-formed ID for {ledger.prefix}")
        if seen[row.id] > 1:
            error(row, f"{row.id} appears {seen[row.id]} times")
        if row.kind not in KINDS:
            error(row, f"{row.id} has unknown kind '{row.kind}'")
        if row.status not in STATUSES:
            error(row, f"{row.id} has unknown status '{row.status}'")
        elif row.status in VERIFIED:
            name = row.declaration
            if not name or "." not in name:
                error(row, f"{row.id} is {row.status} but names no fully qualified declaration")
        elif row.status == "unreviewed" and row.lean != "—":
            error(row, f"{row.id} is unreviewed, so its Lean cell must be '—'")
    if any(len(row.cells) != 9 for row in ledger.rows):
        return errors

    numbers = sorted(int(row.suffix) for row in ledger.numbered())
    header = ledger.header
    numbering = re.match(
        r"1[–-](\d+) \((\d+) items?, (\d+) equation labels?", header.get("Numbered items", ""))
    if not numbering:
        error(None, "header 'Numbered items' must read '1–N (k items, m equation labels…'")
    else:
        top, items, labels = (int(group) for group in numbering.groups())
        if numbers != list(range(1, top + 1)):
            missing = sorted(set(range(1, top + 1)) - set(numbers))
            extra = sorted(set(numbers) - set(range(1, top + 1)))
            error(None, f"numbered rows must be exactly 1..{top}; missing {missing}, extra {extra}")
        equations = sum(1 for row in ledger.numbered() if row.kind == "equation")
        if items + labels != top or labels != equations:
            error(None, f"header says {items} items and {labels} equation labels; "
                        f"rows have {len(numbers) - equations} and {equations}")
    for key, letter in (("Unnumbered definitions", "D"), ("Prose claims (R)", "R"),
                        ("Exercises", "E")):
        value = leading_int(header.get(key, ""))
        if value != ledger.count(letter):
            error(None, f"header '{key}' says {value}; there are {ledger.count(letter)} {letter} rows")

    source = sources.get(ledger.slug)
    if source is None:
        error(None, f"slug {ledger.slug} is not in {SOURCE_INDEX}")
        return errors
    if source.chapter != str(ledger.chapter):
        error(None, f"{SOURCE_INDEX} places {ledger.slug} in chapter {source.chapter}")
    expected = {
        "Printed date": source.date, "Pages": str(source.pages), "SHA-256": source.sha,
    }
    for key, value in expected.items():
        if header.get(key) != value:
            error(None, f"header '{key}' is '{header.get(key)}'; {SOURCE_INDEX} has '{value}'")
    if f"[{source.file}]" not in header.get("Source", ""):
        error(None, f"header 'Source' does not link {source.file}")
    if numbering and int(numbering.group(1)) != source.numbered:
        error(None, f"{SOURCE_INDEX} gives {source.numbered} numbers; the ledger has {numbering.group(1)}")
    blocks = re.search(r"\((\d+) `定義\.` blocks?", header.get("Unnumbered definitions", ""))
    if not blocks or int(blocks.group(1)) != source.definitions:
        error(None, f"header 'Unnumbered definitions' must give the `定義.` block count "
                    f"{source.definitions} from {SOURCE_INDEX}")
    return errors


def lean_ids(root: Path) -> tuple[dict[str, tuple[str, str]], list[str]]:
    """Map each source ID in a Lean docstring to its declaration and location."""
    found: dict[str, tuple[str, str]] = {}
    errors = []
    pattern = re.compile(
        r"/--\s*`(ALGD-[A-Z0-9-]+)`.*?-/\s*(?:@\[[^\]]*\]\s*)*"
        r"(?:(?:private|protected|noncomputable|nonrec)\s+)*"
        r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+([^\s:({\[]+)",
        re.DOTALL)
    for base in LEAN_ROOTS:
        for path in sorted((root / base).rglob("*.lean")):
            text = path.read_text(encoding="utf-8")
            scopes = [(m.start(), m.group(1), m.group(2))
                      for m in re.finditer(r"^(namespace|end)[ \t]+(\S+)", text, re.MULTILINE)]
            for match in pattern.finditer(text):
                stack: list[str] = []
                for position, word, name in scopes:
                    if position > match.start():
                        break
                    if word == "namespace":
                        stack.append(name)
                    elif stack and stack[-1] == name:
                        stack.pop()
                full = ".".join([*stack, match.group(2)])
                line = text.count("\n", 0, match.start()) + 1
                where = f"{path.relative_to(root)}:{line}"
                if match.group(1) in found:
                    errors.append(f"{where}: {match.group(1)} is also used at {found[match.group(1)][1]}")
                found[match.group(1)] = (full, where)
    return found, errors


def check_lean_links(ledgers: list[Ledger], ids: dict[str, tuple[str, str]]) -> list[str]:
    errors = []
    rows = {row.id: (ledger, row) for ledger in ledgers for row in ledger.rows}
    for source_id, (name, where) in sorted(ids.items()):
        if source_id not in rows:
            errors.append(f"{where}: {source_id} has no ledger row")
            continue
        ledger, row = rows[source_id]
        if row.status not in VERIFIED:
            errors.append(f"{where}: {source_id} is '{row.status}' in {ledger.path}; "
                          f"a declaration carrying the ID must be verified")
        elif row.declaration != name:
            errors.append(f"{ledger.path}:{row.line}: {source_id} names {row.declaration}, "
                          f"but the docstring at {where} is on {name}")
    for ledger in ledgers:
        for row in ledger.rows:
            name = row.declaration
            if row.status in VERIFIED and name and name.startswith("ProjectEpisteme."):
                if ids.get(row.id, (None,))[0] != name:
                    errors.append(f"{ledger.path}:{row.line}: {row.id} names {name}, whose "
                                  f"docstring must start with `{row.id}`")
    return errors


def anchors(path: Path) -> set[str]:
    result: set[str] = set()
    counts: Counter[str] = Counter()
    fenced = False
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("```"):
            fenced = not fenced
        if fenced or not line.startswith("#"):
            continue
        text = line.lstrip("#").strip().lower()
        slug = re.sub(r"[^\w\- ]", "", text).replace(" ", "-")
        result.add(slug if counts[slug] == 0 else f"{slug}-{counts[slug]}")
        counts[slug] += 1
    return result


def check_links(root: Path) -> list[str]:
    errors = []
    files: list[Path] = []
    for entry in MARKDOWN:
        target = root / entry
        files.extend(sorted(target.rglob("*.md")) if target.is_dir() else [target])
    link = re.compile(r"\]\(([^)\s]+)\)")
    for path in files:
        if not path.is_file():
            continue
        fenced = False
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if line.startswith("```"):
                fenced = not fenced
            if fenced:
                continue
            for match in link.finditer(line):
                href = match.group(1)
                if re.match(r"[a-z]+:", href):
                    continue
                file_part, _, anchor = href.partition("#")
                target = (path.parent / file_part).resolve() if file_part else path
                where = f"{path.relative_to(root)}:{number}"
                if not target.exists():
                    errors.append(f"{where}: broken link {href}")
                elif anchor and target.suffix == ".md" and anchor not in anchors(target):
                    errors.append(f"{where}: no heading for anchor #{anchor} in {file_part or path.name}")
    return errors


def verified(ledger: Ledger) -> int:
    return sum(1 for row in ledger.rows if row.status in VERIFIED)


def coverage_blocks(ledgers: list[Ledger], sources: dict[str, Source]) -> dict[str, str]:
    chapters = sorted({source.chapter for source in sources.values() if source.chapter != "SUP"})
    by_chapter = {chapter: [ledger for ledger in ledgers if str(ledger.chapter) == chapter]
                  for chapter in chapters}

    summary = ["| Scope | PDFs cataloged | Numbers 1..max with a row | Ledger rows | Verified | Exercises cataloged |",
               "| --- | --- | --- | --- | --- | --- |"]
    totals = [0, 0, 0, 0, 0, 0, 0]
    for chapter in chapters:
        in_index = [s for s in sources.values() if s.chapter == chapter]
        done = by_chapter[chapter]
        numbers = sum(len(ledger.numbered()) for ledger in done)
        available = sum(s.numbered for s in in_index)
        rows = sum(len(ledger.rows) for ledger in done)
        checked = sum(verified(ledger) for ledger in done)
        exercises = sum(ledger.count("E") for ledger in done)
        if done:
            summary.append(f"| Chapter {chapter} | {len(done)} / {len(in_index)} | {numbers} / {available} "
                           f"| {rows} | {checked} | {exercises} |")
        else:
            summary.append(f"| Chapter {chapter} | 0 / {len(in_index)} | 0 / {available} | — | — "
                           f"| not yet cataloged |")
        for i, value in enumerate((len(done), len(in_index), numbers, available, rows, checked, exercises)):
            totals[i] += value
    summary.append(f"| **Chapters {chapters[0]}–{chapters[-1]}** | **{totals[0]} / {totals[1]}** "
                   f"| **{totals[2]} / {totals[3]}** | **{totals[4]}** | **{totals[5]}** | **{totals[6]}** |")
    numbered_verified = sum(1 for ledger in ledgers for row in ledger.numbered() if row.status in VERIFIED)
    summary.append("")
    summary.append(f"Verified main-text items: **{totals[5]}** ({numbered_verified} numbered items and "
                   f"{totals[5] - numbered_verified} definitions or prose claims). "
                   f"Exercises cataloged: **{totals[6]}**.")

    head = ["| Ledger | Rows | Numbered (items + equations) | D | R | E | "
            + " | ".join(STATUS_ORDER) + " | Verified |",
            "| --- " * (7 + len(STATUS_ORDER)) + "|"]
    document = list(head)
    for chapter in chapters:
        done = by_chapter[chapter]
        if not done:
            continue
        sums = Counter()
        for ledger in done:
            statuses = Counter(row.status for row in ledger.rows)
            equations = sum(1 for row in ledger.numbered() if row.kind == "equation")
            values = {
                "rows": len(ledger.rows), "numbered": len(ledger.numbered()), "equations": equations,
                "D": ledger.count("D"), "R": ledger.count("R"), "E": ledger.count("E"),
                **{status: statuses[status] for status in STATUS_ORDER}, "verified": verified(ledger),
            }
            sums.update(values)
            document.append(_document_row(f"[{ledger.name}](ledger/algd/{ledger.path.name})", values, ""))
        document.append(_document_row(f"Chapter {chapter}", sums, "**"))

    declarations = ["| Ledger ID | Lean declaration | Status |", "| --- | --- | --- |"]
    for ledger in ledgers:
        for row in ledger.rows:
            if row.status in VERIFIED:
                declarations.append(f"| {row.id} | `{row.declaration}` | {row.status} |")
    return {"summary": "\n".join(summary), "by-document": "\n".join(document),
            "verified": "\n".join(declarations)}


def _document_row(label: str, values, bold: str) -> str:
    items = values["numbered"] - values["equations"]
    cells = [label, values["rows"], f"{values['numbered']} ({items} + {values['equations']})",
             values["D"], values["R"], values["E"], *(values[s] for s in STATUS_ORDER), values["verified"]]
    return "| " + " | ".join(f"{bold}{cell}{bold}" for cell in cells) + " |"


def render_coverage(text: str, blocks: dict[str, str]) -> tuple[str, list[str]]:
    errors = []
    for name, body in blocks.items():
        pattern = re.compile(
            rf"(<!-- BEGIN GENERATED: {name} -->\n)(?:.*?\n)?(<!-- END GENERATED: {name} -->)",
            re.DOTALL)
        if not pattern.search(text):
            errors.append(f"{COVERAGE}: missing generated block '{name}'")
            continue
        text = pattern.sub(lambda m: m.group(1) + body + "\n" + m.group(2), text)
    return text, errors


def render_lean_check(ledgers: list[Ledger]) -> str:
    entries = [(row.id, row.declaration) for ledger in ledgers for row in ledger.rows
               if row.status in VERIFIED and row.declaration]
    lines = [
        "import ProjectEpisteme",
        "",
        "/-!",
        "Every ledger row whose status is `existing`, `bridged`, or `new-proved` names a Lean",
        "declaration. This check fails if one of them does not exist in the built library.",
        "",
        "Generated by `python3 checks/ledger.py --write` from `docs/ledger/`. Do not edit it by hand.",
        "-/",
        "",
        "open Lean Elab Command",
        "",
        "private def ledgerDeclarations : List (String × Name) := [",
    ]
    lines += [f"  (\"{source_id}\", `{name}){',' if i < len(entries) - 1 else ''}"
              for i, (source_id, name) in enumerate(entries)]
    lines += [
        "]",
        "",
        "run_cmd do",
        "  let env ← getEnv",
        "  let missing := ledgerDeclarations.filter fun (_, name) => !env.contains name",
        "  unless missing.isEmpty do",
        "    throwError m!\"Ledger declarations not found: \\",
        "      {\", \".intercalate (missing.map fun (id, name) => s!\"{id} {name}\")}\"",
        "  logInfo m!\"All {ledgerDeclarations.length} ledger declarations exist.\"",
        "",
    ]
    return "\n".join(lines)


def run(root: Path, write: bool = False) -> list[str]:
    root = root.resolve()
    sources, errors = read_sources(root)
    ledgers = []
    for path in sorted((root / LEDGER_DIR).glob("*.md")):
        ledger, problems = read_ledger(root, path)
        errors += problems
        if ledger:
            ledgers.append(ledger)
            errors += check_ledger(ledger, sources)
    ids, problems = lean_ids(root)
    errors += problems
    errors += check_lean_links(ledgers, ids)

    coverage_path = root / COVERAGE
    current = coverage_path.read_text(encoding="utf-8")
    generated, problems = render_coverage(current, coverage_blocks(ledgers, sources))
    errors += problems
    lean_path = root / LEAN_CHECK
    lean = render_lean_check(ledgers)
    if write:
        coverage_path.write_text(generated, encoding="utf-8")
        lean_path.write_text(lean, encoding="utf-8")
    else:
        if generated != current:
            errors.append(f"{COVERAGE} is out of date; run `python3 checks/ledger.py --write`")
        if not lean_path.is_file() or lean_path.read_text(encoding="utf-8") != lean:
            errors.append(f"{LEAN_CHECK} is out of date; run `python3 checks/ledger.py --write`")
    errors += check_links(root)
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--write", action="store_true", help="regenerate the generated files first")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    errors = run(args.root, write=args.write)
    for error in errors:
        print(error)
    if errors:
        print(f"{len(errors)} ledger problem(s).")
        return 1
    print("Ledger checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

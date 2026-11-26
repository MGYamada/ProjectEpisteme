"""Tests for checks/ledger.py. Run with `python3 -m unittest discover -s checks/tests -v`."""

from __future__ import annotations

from pathlib import Path
import sys
from tempfile import TemporaryDirectory
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import ledger  # noqa: E402

REPOSITORY = Path(__file__).resolve().parents[2]

INDEX = """# Source index

## Chapter 1: test

| Slug | File | Title | English working title | Printed date | Index-page date | Pages | Numbered | Definitions | SHA-256 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| TEST | [test.pdf](https://example.test/test.pdf) | テスト | Test | 2026-01-01 | 2026-01-01 更新 | 3 | 2 | 1 | `abc123` |
"""

LEDGER = """# ALGD-C1-TEST — テスト (Test)

| Field | Value |
| --- | --- |
| Source | [test.pdf](https://example.test/test.pdf), Chapter 1 |
| Printed date | 2026-01-01 |
| Pages | 3 |
| SHA-256 | abc123 |
| Numbered items | 1–2 (1 item, 1 equation label: (2)) |
| Unnumbered definitions | 1 (1 `定義.` block, 0 introduced in prose) |
| Prose claims (R) | 0 |
| Exercises | 0 |

## Items

| ID | Kind | Location | Statement (paraphrase) | mathlib candidates | Lean | Status | Assumptions | Review |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| ALGD-C1-TEST-D01 | definition | 定義, p.1 | A thing | `Foo` | — | unreviewed | — | candidate only |
| ALGD-C1-TEST-01 | theorem | 定理 1, p.1 | True holds | `trivial` | `ProjectEpisteme.Test.thm` | existing | — | verified |
| ALGD-C1-TEST-02 | equation | (2), p.2 | Labels a diagram | — | — | non-propositional | — | label only |

## Notes

- See the [index](../../algd-source-index.md) and [the items](#items).
"""

COVERAGE = """# Coverage

<!-- BEGIN GENERATED: summary -->
<!-- END GENERATED: summary -->

<!-- BEGIN GENERATED: by-document -->
<!-- END GENERATED: by-document -->

<!-- BEGIN GENERATED: verified -->
<!-- END GENERATED: verified -->
"""

LEAN = """namespace ProjectEpisteme.Test

/-- `ALGD-C1-TEST-01` (定理 1, p.1). True holds. -/
theorem thm : True := trivial

end ProjectEpisteme.Test
"""


class LedgerCheckTests(unittest.TestCase):
    def setUp(self):
        self.directory = TemporaryDirectory()
        self.root = Path(self.directory.name)
        files = {
            "docs/algd-source-index.md": INDEX,
            "docs/ledger/algd/C1-TEST.md": LEDGER,
            "docs/algd-coverage.md": COVERAGE,
            "ProjectEpisteme/Test.lean": LEAN,
            "README.md": "# Readme\n\nSee [coverage](docs/algd-coverage.md#coverage).\n",
        }
        for name, text in files.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        (self.root / "checks").mkdir()
        self.assertEqual(ledger.run(self.root, write=True), [])

    def tearDown(self):
        self.directory.cleanup()

    def edit(self, name, old, new):
        path = self.root / name
        text = path.read_text(encoding="utf-8")
        self.assertIn(old, text)
        path.write_text(text.replace(old, new), encoding="utf-8")

    def assertProblem(self, fragment, write=True):
        errors = ledger.run(self.root, write=write)
        self.assertTrue(any(fragment in error for error in errors),
                        f"no problem containing {fragment!r} in {errors}")

    def test_fixture_passes(self):
        self.assertEqual(ledger.run(self.root), [])

    def test_generated_files(self):
        coverage = (self.root / "docs/algd-coverage.md").read_text(encoding="utf-8")
        self.assertIn("| Chapter 1 | 1 / 1 | 2 / 2 | 3 | 1 | 0 |", coverage)
        self.assertIn("| ALGD-C1-TEST-01 | `ProjectEpisteme.Test.thm` | existing |", coverage)
        lean = (self.root / "checks/LedgerDeclarations.lean").read_text(encoding="utf-8")
        self.assertIn('("ALGD-C1-TEST-01", `ProjectEpisteme.Test.thm)', lean)

    def test_gap_in_numbering(self):
        self.edit("docs/ledger/algd/C1-TEST.md",
                  "| ALGD-C1-TEST-02 | equation | (2), p.2 | Labels a diagram | — | — | non-propositional | — | label only |\n",
                  "")
        self.assertProblem("numbered rows must be exactly 1..2; missing [2]")

    def test_duplicate_id(self):
        self.edit("docs/ledger/algd/C1-TEST.md", "ALGD-C1-TEST-02 |", "ALGD-C1-TEST-01 |")
        self.assertProblem("ALGD-C1-TEST-01 appears 2 times")

    def test_wrong_cell_count(self):
        self.edit("docs/ledger/algd/C1-TEST.md", "| A thing |", "| A | thing |")
        self.assertProblem("ALGD-C1-TEST-D01 has 10 cells, not 9")

    def test_escaped_pipe_is_one_cell(self):
        self.edit("docs/ledger/algd/C1-TEST.md", "| A thing |", "| A \\| thing |")
        self.assertEqual(ledger.run(self.root, write=True), [])

    def test_unknown_kind_and_status(self):
        self.edit("docs/ledger/algd/C1-TEST.md", "| definition | 定義", "| defn | 定義")
        self.edit("docs/ledger/algd/C1-TEST.md", "| unreviewed |", "| done |")
        self.assertProblem("unknown kind 'defn'")
        self.assertProblem("unknown status 'done'")

    def test_header_counts(self):
        self.edit("docs/ledger/algd/C1-TEST.md", "| Prose claims (R) | 0 |", "| Prose claims (R) | 1 |")
        self.assertProblem("header 'Prose claims (R)' says 1; there are 0 R rows")

    def test_equation_label_count(self):
        self.edit("docs/ledger/algd/C1-TEST.md", "| ALGD-C1-TEST-02 | equation |",
                  "| ALGD-C1-TEST-02 | remark |")
        self.assertProblem("header says 1 items and 1 equation labels")

    def test_source_index_mismatch(self):
        self.edit("docs/algd-source-index.md", "`abc123`", "`def456`")
        self.assertProblem("header 'SHA-256' is 'abc123'")
        self.edit("docs/algd-source-index.md", "| 3 | 2 | 1 |", "| 3 | 2 | 2 |")
        self.assertProblem("`定義.` block count 2")

    def test_unreviewed_row_names_no_declaration(self):
        self.edit("docs/ledger/algd/C1-TEST.md", "| `Foo` | — | unreviewed |", "| `Foo` | `X.y` | unreviewed |")
        self.assertProblem("ALGD-C1-TEST-D01 is unreviewed, so its Lean cell must be '—'")

    def test_verified_row_needs_qualified_name(self):
        self.edit("docs/ledger/algd/C1-TEST.md", "`ProjectEpisteme.Test.thm`", "`thm`")
        self.assertProblem("ALGD-C1-TEST-01 is existing but names no fully qualified declaration")

    def test_docstring_must_match_ledger(self):
        self.edit("ProjectEpisteme/Test.lean", "theorem thm", "theorem thm'")
        self.assertProblem("but the docstring at ProjectEpisteme/Test.lean:3 is on ProjectEpisteme.Test.thm'")

    def test_verified_project_row_needs_docstring(self):
        self.edit("ProjectEpisteme/Test.lean", "`ALGD-C1-TEST-01` ", "")
        self.assertProblem("whose docstring must start with `ALGD-C1-TEST-01`")

    def test_docstring_id_must_be_verified(self):
        self.edit("docs/ledger/algd/C1-TEST.md", "`ProjectEpisteme.Test.thm` | existing", "— | unreviewed")
        self.assertProblem("ALGD-C1-TEST-01 is 'unreviewed'")

    def test_generated_files_out_of_date(self):
        self.edit("docs/ledger/algd/C1-TEST.md", "| non-propositional |", "| blocked |")
        errors = ledger.run(self.root)
        self.assertTrue(any("algd-coverage.md is out of date" in error for error in errors), errors)
        (self.root / "checks/LedgerDeclarations.lean").write_text("-- stale\n", encoding="utf-8")
        self.assertProblem("LedgerDeclarations.lean is out of date", write=False)

    def test_broken_link_and_anchor(self):
        self.edit("docs/ledger/algd/C1-TEST.md", "(#items)", "(#nowhere)")
        self.assertProblem("no heading for anchor #nowhere")
        self.edit("README.md", "docs/algd-coverage.md#coverage", "docs/missing.md")
        self.assertProblem("broken link docs/missing.md")


class RepositoryTests(unittest.TestCase):
    def test_repository_passes(self):
        self.assertEqual(ledger.run(REPOSITORY), [])


if __name__ == "__main__":
    unittest.main()

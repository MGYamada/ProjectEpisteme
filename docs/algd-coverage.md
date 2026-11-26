# alg-d coverage report

**As of:** 2026-11-26 · Lean v4.35.0 · mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`

This report counts the rows of the [alg-d ledgers](ledger/algd/) against the [source index](algd-source-index.md). Update it by hand whenever a ledger changes. The definitions follow the [Category strategy](Project_Episteme_Category_Strategy.md#6-ledger-and-verification-rules):

- **Mapped** means an item has a ledger row.
- **Verified** means the row's status is `existing`, `bridged`, or `new-proved`, it names a Lean declaration, `lake build` succeeds, the axiom audit is pinned, and the statement has been reviewed against the source.

`unreviewed` rows are mapped but not verified. Mathlib candidates in those rows have been checked to exist (`#check` on every cited name under the pin), but they have not been matched against the source statement.

## Summary

| Scope | PDFs cataloged | Numbers 1..max with a row | Ledger rows | Verified | Exercises cataloged |
| --- | --- | --- | --- | --- | --- |
| Chapter 0 | 8 / 8 | 120 / 120 | 189 | 0 | 2 |
| Chapter 1 | 5 / 5 | 121 / 121 | 175 | 12 | 0 |
| Chapter 2 | 0 / 10 | 0 / 201 | — | — | not yet checked |
| **Chapters 0–2** | **13 / 23** | **241 / 442** | **364** | **12** | **2** |

First progress report (AGENTS.md): **12 verified main-text items**, all in YONEDA: 10 numbered items and 2 definitions. **2 exercises cataloged**, ALGD-C0-CDIAG-E01 and -E02, to be proved in a later phase.

## By document

Numbered = numbers 1..max, split into statements and labelled displays (equations). D, R, and E are the unnumbered definitions, prose claims, and exercises. The status columns count rows.

| Ledger | Rows | Numbered (items + equations) | D | R | E | unreviewed | existing | bridged | new-proved | blocked | non-propositional | Verified |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| [C0-INTRO](ledger/algd/C0-INTRO.md) | 44 | 32 (32 + 0) | 8 | 4 | 0 | 44 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C0-CDIAG](ledger/algd/C0-CDIAG.md) | 9 | 3 (1 + 2) | 3 | 1 | 2 | 9 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C0-CONSTR](ledger/algd/C0-CONSTR.md) | 19 | 12 (12 + 0) | 7 | 0 | 0 | 19 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C0-UNIV](ledger/algd/C0-UNIV.md) | 23 | 14 (14 + 0) | 7 | 2 | 0 | 23 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C0-SHEAF](ledger/algd/C0-SHEAF.md) | 13 | 8 (7 + 1) | 4 | 1 | 0 | 13 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C0-DUAL](ledger/algd/C0-DUAL.md) | 29 | 20 (20 + 0) | 7 | 2 | 0 | 29 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C0-EQUIV](ledger/algd/C0-EQUIV.md) | 30 | 20 (20 + 0) | 7 | 3 | 0 | 30 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C0-FUNDGPD](ledger/algd/C0-FUNDGPD.md) | 22 | 11 (11 + 0) | 7 | 4 | 0 | 22 | 0 | 0 | 0 | 0 | 0 | 0 |
| **Chapter 0** | **189** | **120 (117 + 3)** | **50** | **17** | **2** | **189** | **0** | **0** | **0** | **0** | **0** | **0** |
| [C1-NAT](ledger/algd/C1-NAT.md) | 23 | 13 (13 + 0) | 8 | 2 | 0 | 23 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C1-YONEDA](ledger/algd/C1-YONEDA.md) | 19 | 11 (9 + 2) | 5 | 3 | 0 | 5 | 7 | 4 | 1 | 0 | 2 | 12 |
| [C1-COMMA](ledger/algd/C1-COMMA.md) | 10 | 8 (8 + 0) | 2 | 0 | 0 | 10 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C1-LIMIT](ledger/algd/C1-LIMIT.md) | 51 | 33 (30 + 3) | 14 | 4 | 0 | 51 | 0 | 0 | 0 | 0 | 0 | 0 |
| [C1-ADJOINT](ledger/algd/C1-ADJOINT.md) | 72 | 56 (55 + 1) | 9 | 7 | 0 | 72 | 0 | 0 | 0 | 0 | 0 | 0 |
| **Chapter 1** | **175** | **121 (115 + 6)** | **38** | **16** | **0** | **161** | **7** | **4** | **1** | **0** | **2** | **12** |

## Verified declarations

| Ledger IDs | Lean declaration | Status |
| --- | --- | --- |
| ALGD-C1-YONEDA-01 | `ProjectEpisteme.AlgD.Yoneda.yoneda_bijective` | existing |
| ALGD-C1-YONEDA-02 | `ProjectEpisteme.AlgD.Yoneda.yoneda_map_bijective` | existing |
| ALGD-C1-YONEDA-03 | `ProjectEpisteme.AlgD.Yoneda.isIso_iff_isIso_yonedaEquiv` | bridged |
| ALGD-C1-YONEDA-04 | `ProjectEpisteme.AlgD.Yoneda.nonempty_iso_of_yoneda_iso` | existing |
| ALGD-C1-YONEDA-05 | `ProjectEpisteme.AlgD.Yoneda.nonempty_iso_of_natural_equiv_hom_to` | bridged |
| ALGD-C1-YONEDA-06 | `ProjectEpisteme.AlgD.Yoneda.nonempty_iso_of_natural_equiv_hom_from` | bridged |
| ALGD-C1-YONEDA-07 | `ProjectEpisteme.AlgD.Yoneda.yonedaEquiv_symm_natural_iff_natural` | new-proved |
| ALGD-C1-YONEDA-09 | `ProjectEpisteme.AlgD.Yoneda.nonempty_iso_of_yoneda_comp_iso` | bridged |
| ALGD-C1-YONEDA-10 | `ProjectEpisteme.AlgD.Yoneda.yonedaEquiv_natural_in_object` | existing |
| ALGD-C1-YONEDA-11 | `ProjectEpisteme.AlgD.Yoneda.yonedaEquiv_natural_in_presheaf` | existing |
| ALGD-C1-YONEDA-D02, -D04 | `CategoryTheory.yoneda` (mathlib definition, read against the source) | existing |

Every declaration above depends only on `[propext, Classical.choice, Quot.sound]`, pinned with `#guard_msgs` in [`Yoneda.lean`](../ProjectEpisteme/Category/AlgD/C1/Yoneda.lean).

## Known gaps flagged during cataloging

These rows are expected to become `new-proved` or `blocked` rather than `existing`. Details are in each ledger's Notes.

- **Not in mathlib**
  - Isomorphism (not equivalence) of categories as a notion. Used by CONSTR-01 and -04–06, INTRO-19 and -28, and LIMIT-05, -07, -08.
  - General subcategories. Used by CONSTR-D06 and -08, -10, -11.
  - The universal property of `Comma` (COMMA-07).
  - Skeletons as full subcategories and their uniqueness (EQUIV-D07, -19, -20).
  - Idempotent adjunctions (ADJOINT-30 to -34).
  - Adjunctions with a parameter: 定理 41 and 系 42 (ADJOINT-41, -42). mathlib lists this as a TODO in `ParametrizedAdjunction`.
- **Topology and algebra prerequisites**
  - π₁ as a functor on pointed spaces (INTRO-10, CONSTR-07).
  - Seifert–van Kampen for groupoids (FUNDGPD-10, -11).
  - The p-adic integers as a limit in Set (UNIV-14, LIMIT-11).
  - Gelfand–Naimark as an equivalence (EQUIV-03).
  - Several algebraic examples in ADJOINT (例 50–53, 55, 56).
- **Source issues**
  - Typos in adjoint.pdf and limit.pdf.
  - A missing boundedness hypothesis in UNIV-13 and LIMIT-10.
  - A missing nonemptiness hypothesis in SHEAF 例 6.
  - A missing injectivity hypothesis in ADJOINT 例 51.

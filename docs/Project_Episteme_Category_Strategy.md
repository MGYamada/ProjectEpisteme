# Project Episteme — Category track strategy

**Status:** Adopted strategy, first pass (2026-11-26)\
**Track:** 1. Category (Mac Lane 2.0)\
**Environment:** Lean v4.35.0, mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` ([lean-toolchain](../lean-toolchain), [lake-manifest.json](../lake-manifest.json))

This document turns the Category track parts of the [design](Project_Episteme_Design.md) and the [Initial Plan](Project_Episteme_Initial_Plan.md) into a working order. It covers which source drives the work, how source items map to Lean, the conventions every module follows, and the order in which to verify the material.

## 1. Primary source

The Category track uses **alg-d, 「全ての概念はKan拡張である」, Chapters 0–2** as its primary source. CWM I–V and IX–X follow behind it.

[AGENTS.md](../AGENTS.md) and the [design](Project_Episteme_Design.md) ask for CWM's main text to be verified first. This track reverses that order for a practical reason: the CWM text is not available to the project at item level right now, while all 23 alg-d PDFs are public, dated, and machine-readable. The alg-d notes cover the same ground as CWM I–V and X. The basics, Yoneda, comma categories, limits, adjunctions, and Kan extensions all appear in both. Most CWM items will therefore point to declarations that the alg-d work has already verified. The other tracks keep the CWM-first order.

CWM enters in two steps:

1. Now: a chapter-level correspondence only, given in §7.
2. When the CWM text is available: an item-level catalog `docs/ledger/cwm/` with IDs `CWM2-<chapter>-<section>-<n>`. Each CWM item points to the same Lean declarations as the matching alg-d items. Its hypotheses are reviewed separately, as the design requires.

## 2. Source inventory

The [source index](algd-source-index.md) pins every document by printed date and SHA-256 hash. The table below summarizes it.

| Scope | PDFs | Pages | Numbered (max) | `定義.` blocks |
| --- | --- | --- | --- | --- |
| Chapter 0 | 8 | 78 | 120 | 37 |
| Chapter 1 | 5 | 94 | 121 | 10 |
| Chapter 2 | 10 | 212 | 201 | 45 |
| Total | 23 | 384 | 442 | 92 |

These facts about the source shape the ledger:

- **One counter per PDF.** 定理, 命題, 補題, 系, 例 and displayed equation labels share one counter. For example, yoneda.pdf numbers 定理 1, 系 2, equation (3), 系 4, …. Every number gets a ledger row, so IDs equal source numbers.
- **Unnumbered definitions.** `定義.` blocks have no number. Some definitions appear only in prose, such as the hom functor and the Yoneda embedding.
- **Almost no exercises.** Chapters 0–1 contain only two exercises: unnumbered 練習問題 at the end of commutative_diagram.pdf. They are cataloged and, as AGENTS.md requires, proved in a later phase. Chapter 2 is checked when it is cataloged. Most of the AGENTS.md exercise phase therefore concerns CWM.
- **Repeated results.** sheaf_kan_extension.pdf 定理 1–7 restate kan_extension.pdf results. Their rows point to the same Lean declarations.
- **Notation.** The notes use their own notation. §5 maps it to mathlib.

## 3. Two layers of Lean code

| Layer | Location | Contents | Rules |
| --- | --- | --- | --- |
| Source layer | `ProjectEpisteme/Category/AlgD/C<k>/<Slug>.lean`, namespace `ProjectEpisteme.AlgD.<Slug>` | One theorem per source item, stated in the source's formulation and proved from mathlib or from the library layer | The first line of each docstring is the source ID with the label and page. The module header records the PDF URL, printed date, and SHA-256. Each file ends with its axiom audit (§6). |
| Library layer | `ProjectEpisteme/Category/Basic/…`, namespace `CategoryTheory` | General results missing from mathlib, written in mathlib style | Uses no source numbering. Candidates for upstreaming to mathlib. |

The source layer imports only mathlib and the library layer. Source-layer theorems use descriptive names, for example `yoneda_map_bijective`. Source IDs stay in docstrings and ledgers, so several items can share one declaration, as the design requires. `ProjectEpisteme/Category.lean` imports every Category module, and the root module `ProjectEpisteme.lean` imports `ProjectEpisteme.Category`.

All files use the module system of the pinned toolchain. Each file starts with `module` and `public import …`, followed by `@[expose] public section`.

A source-layer theorem should state what the source states:

- When the source proves a property of an explicit map, the theorem keeps that map. For example, 米田の補題 asserts that `θ ↦ θ_a(id_a)` is bijective, not merely that some bijection exists.
- A natural bijection is either written out with its naturality equations or encoded as a natural isomorphism. The docstring says which encoding is used.
- Existence of an isomorphism (`a ≅ b` in the source) is `Nonempty (a ≅ b)`.
- A theorem should not carry stronger universe or size assumptions than the source needs. Hom universes of unrelated categories stay independent.

## 4. Source IDs

`ALGD-C<chapter>-<SLUG>-<nn>`:

- `nn` is the PDF's own number with two digits, for numbered items and labelled equations.
- `D<k>` marks the k-th definition in order of appearance, whether it is a `定義.` block or a definition in prose.
- `R<k>` marks the k-th prose claim that a formalization has to prove.
- `E<k>` marks the k-th unnumbered exercise (練習問題).

| Chapter | Slugs |
| --- | --- |
| 0 | INTRO, CDIAG, CONSTR, UNIV, SHEAF, DUAL, EQUIV, FUNDGPD |
| 1 | NAT, YONEDA, COMMA, LIMIT, ADJOINT |
| 2 | KAN, SIMPLEX, AFT, SHEAF2, LOG, FILTERED, END, COYONEDA, PROF, ISBELL |
| Supplementary | `ALGD-SUP-KANSHORT` |

## 5. Notation and size conventions

| alg-d | mathlib | Check |
| --- | --- | --- |
| `g ∘ f`, `GF` | `f ≫ g`, `F ⋙ G` | Reverse the order on every transcription. |
| `Set` | `Type v`, where `v` is the hom universe | — |
| locally small category (global assumption) | `C : Type u`, `[Category.{v} C]` | Objects and morphisms use separate universes. |
| small category | `SmallCategory C` (`Category.{u} C` with `C : Type u`) | — |
| (co)complete | `HasLimits C` / `HasColimits C` (`HasLimitsOfSize.{v, v}`) | Record the size of the diagrams. |
| `Ĉ = Set^{C^op}`, `y` | `Cᵒᵖ ⥤ Type v`, `yoneda` | `Ĉ` is not locally small for large `C`: its hom-types are in `Type (max u v)`. |
| `Hom_C(a, −)` | `coyoneda.obj (op a)` | — |
| `F ⊣ G : C → D`, unit `η : id ⇒ GF` | `F ⊣ G`, `adj.unit : 𝟭 C ⟶ F ⋙ G` | — |
| `c ↓ G`, `F ↓ d`, `F ↓ G` | `StructuredArrow c G`, `CostructuredArrow F d`, `Comma F G` | — |
| `F⁻¹ : U^D → U^C` (precomposition) | `(whiskeringLeft C D U).obj F` | alg-d uses `⁻¹` for precomposition, not for an inverse. |
| `F†E`, Kan extension of `E : C → U` along `F : C → D`, unit `η : E ⇒ (F†E)F` | `F.leftKanExtension E`, `F.leftKanExtensionUnit E : E ⟶ F ⋙ F.leftKanExtension E`, `Functor.IsLeftKanExtension` | alg-d's `F` is mathlib's `L`, the functor extended along. |
| `F‡E` | `F.rightKanExtension E`, `Functor.IsRightKanExtension` | — |
| pointwise (各点) left Kan extension | `LeftExtension.IsPointwiseLeftKanExtension`, colimits over `CostructuredArrow F d` | Keep general and pointwise Kan extensions apart (Initial Plan §5). |
| profunctor `C ⇸ D` | `Profunctor C D := C ⥤ Dᵒᵖ ⥤ Type w` | Check the variance against profunctor.pdf before reuse. |
| natural isomorphism (自然同型) | `IsIso` or `≅` in the functor category | `NatIso.isIso_iff_isIso_app` gives the componentwise form. |

## 6. Ledger and verification rules

**Ledger.** There is one Markdown file per PDF in `docs/ledger/algd/`, for example [`C1-YONEDA.md`](ledger/algd/C1-YONEDA.md). Each file has a header table (URL, printed date, pages, SHA-256, retrieval date, counts) and one item table with these columns:

`ID | Kind | Location | Statement (paraphrase) | mathlib candidates | Lean | Status | Assumptions | Review`

- **Kind** is one of: definition, theorem, proposition, lemma, corollary, example, remark, equation, prose-claim, exercise.
- **Status** uses the design's values: `unreviewed`, `existing`, `bridged`, `new-proved`, `blocked`, `non-propositional`.
- **Statements** are English paraphrases. Do not copy the Japanese text.
- A mathlib candidate becomes `existing` or `bridged` only after a Lean statement in the source's form compiles against it and the review column records how the hypotheses, direction, naturality, and universes were compared.

[algd-coverage.md](algd-coverage.md) holds the counts. It reports **mapped** (has a row) and **verified** (status `existing`, `bridged`, or `new-proved` with a reviewed Lean statement) separately, per PDF and per chapter.

**Verification.** A source-layer module counts as verified when all of the following hold:

1. `lake env lean <file>` succeeds while working, and `lake build` succeeds with no warnings before the work is called complete.
2. The axiom audit is part of the build. For each verified declaration:

   ```lean
   /-- info: '…' depends on axioms: [propext, Classical.choice, Quot.sound] -/
   #guard_msgs (whitespace := lax) in #print axioms decl
   ```

   Anything beyond these three axioms fails the build until it is reviewed.
3. `grep -rnE '\bsorry\b|\badmit\b|^\s*axiom ' ProjectEpisteme/` is empty.
4. The ledger row names the declaration, the review, and the status. The Lean docstring carries the same ID.

## 7. mathlib readiness by document

This forecast comes from searching the pinned checkout. The names are **candidates** until a ledger row verifies them.

| Document | Main candidates | Forecast |
| --- | --- | --- |
| Ch. 0 (INTRO … FUNDGPD) | `Category`, `Functor`, `Opposite`, `Over`/`Under`, product categories, `Limits.Shapes.*`, `Equivalence`, `Skeleton`, `TopCat.Presheaf.IsSheaf`, `FundamentalGroupoid` | mostly existing/bridged. Concrete example categories need instance checks. |
| NAT, YONEDA, COMMA | `NatTrans`, functor categories, whiskering, `yonedaEquiv`, `Yoneda.fullyFaithful`, `StructuredArrow`, `Comma` | existing/bridged. YONEDA is done (§9). |
| LIMIT | `Limits.Types`, `hasLimits_of_hasEqualizers_and_products`, `Limits/Fubini`, `ColimitLimit`, `RepresentableBy`, `IsRepresentable` | existing/bridged |
| ADJOINT | `Adjunction.mkOfHomEquiv`, `leftAdjointOfEquiv`, `Adjunction.leftAdjointUniq`, preservation of limits, `Reflective`, `conjugateEquiv`, cartesian closed | mostly existing. Idempotent adjunctions and the CCC identities need checking. |
| KAN | `Functor/KanExtension/{Basic, Pointwise, Adjunction, Preserves, AdjunctionPreserves, Dense, DenseAt}`, `overEquivPresheafCostructuredArrow` | core existing. Absolute Kan extensions and 定理 51 (presheaf categories via small projectives) may be new. |
| COYONEDA | `colimitOfRepresentable`, `isColimitTautologicalCocone` | existing |
| FILTERED | `IsFiltered`, `FilteredColimitCommutesFiniteLimit`, `RepresentablyFlat`, `TypeValuedFlat`, `IsSifted` | existing except sifted-flat functors |
| AFT | `Adjunction/AdjointFunctorTheorems` (`SolutionSetCondition`, `isRightAdjoint_of_preservesLimits_of_isCoseparating`), `Functor.Final`, Stone–Čech in `Topology/Category/CompHaus` | existing/bridged |
| END | `Limits/Shapes/End` (`end_`, `coend` as multi(co)equalizers), `Limits/Types/End` | definitions existing. Fubini for ends and the end formula for Kan extensions are likely new. |
| SIMPLEX | `AlgebraicTopology/SimplicialSet/*` (Horn, Boundary, Degenerate with `exists_nonDegenerate` and `unique_nonDegenerate_*`, Skeleton, Coskeletal, Nerve, KanComplex, TopAdj) | largely existing, but presentations differ, so expect many bridges |
| SHEAF2 | `Topology/Sheaves/{Stalks, Sheafify, LocalPredicate}` | stalks and sheafification existing. **Sh(X) ≃ Etale(X) not found: new, large.** |
| LOG | `conjugateEquiv` | **Adj(C, D) and `C ∗ D` not found: new, small.** |
| ISBELL | none found | **new, small**, depends on KAN |
| PROF | `CategoryTheory/Profunctor/*` | profunctor basics existing. **Cocomma categories, Span/Cospan categories, and the adjunctions Σ ⊣ Φ and Ψ ⊣ Λ: new.** |

CWM chapter-level correspondence (provisional):

| CWM | alg-d |
| --- | --- |
| I | INTRO, CONSTR, EQUIV, NAT |
| II | CONSTR, DUAL, COMMA |
| III | UNIV, YONEDA, LIMIT |
| IV | ADJOINT, AFT |
| V | LIMIT, AFT |
| IX | FILTERED, END |
| X | KAN, END, COYONEDA |

## 8. Order of work

| Stage | Scope | Acceptance gate |
| --- | --- | --- |
| **S0 Conventions** | This document, the source index, the ledger format | Done (2026-11-26) |
| **S1 Catalog** | Ledgers for Chapters 0–1 (13 PDFs): done on 2026-11-26 (364 rows, see [coverage](algd-coverage.md)). Next: Chapter 2 (10 PDFs) and KANSHORT. | Every number from 1 to max and every definition has a row, and the coverage counts match the source index. |
| **S2 Pilot** | YONEDA end to end | Done: see §9 |
| **S3 Chapters 0–1** | Verify the remaining 12 Chapter 0–1 ledgers, starting with NAT, COMMA, LIMIT, and ADJOINT, which Chapter 2 depends on | Each PDF reaches 100% mapped. Every propositional row is `existing`, `bridged`, or `new-proved`, or is `blocked` with a reason. |
| **S4 Kan extensions** | KAN (54 numbers). The SHEAF2 定理 1–7 and COYONEDA rows follow from it. | Universal-property direction, pointwise versus general, and density all verified as in Initial Plan §5 |
| **S5 Chapter 2 applications** | In order of mathlib readiness: COYONEDA → FILTERED → AFT → END → SIMPLEX → SHEAF2 → LOG → ISBELL → PROF | New constructions go in the library layer and are reviewed for upstreaming. |
| **S6 CWM** | Item-level CWM catalog when the text is available, linked to the existing declarations | Hypotheses reviewed per CWM item |

The stages are ordered by dependency, not by date. S3 and S4 may overlap, because KAN needs only NAT, COMMA, LIMIT, and ADJOINT from Chapter 1.

## 9. Pilot result: YONEDA

[`ProjectEpisteme/Category/AlgD/C1/Yoneda.lean`](../ProjectEpisteme/Category/AlgD/C1/Yoneda.lean) and its [ledger](ledger/algd/C1-YONEDA.md) take yoneda.pdf from source to audited Lean.

- 10 of the 11 numbers are verified: 01, 02, 04, 10, and 11 as `existing`; 03, 05, 06, and 09 as `bridged`; 07 as `new-proved`. Number 08 is a diagram label (`non-propositional`).
- Of the 5 definitions, 2 (D02, D04) were checked against mathlib's `yoneda`.
- Every verified declaration depends only on `[propext, Classical.choice, Quot.sound]`, and the build checks this.

The pilot gave four lessons that apply to the other ledgers:

1. Displayed equation labels take numbers.
2. Source statements often keep the explicit map built in the proof, and later items refer to it.
3. Bundled "即ち … 自然同型" restatements need their own decision. YONEDA keeps the componentwise equations and cites mathlib's bundled `yonedaLemma`.
4. Universe generality has to be checked: 命題 9 originally forced `C` and `D` to share a hom universe, and that was relaxed.

## 10. Risks and open questions

| Issue | Handling |
| --- | --- |
| New constructions: étalé spaces, cocomma categories, Isbell duality, Adj(C, D) | Library layer, each with its own design note before coding |
| PDFs change (the index page marks updates) | Pin by SHA-256, add new rows to the source index, and re-review the ledger rows whose statements changed |
| Large `Ĉ` and other size issues in KAN and ISBELL (for example `y†y` for small `C`) | Record `SmallCategory` versus `Category.{v}` per row. Use `ULift`/`shrinkYoneda` only with a recorded reason. |
| Profunctor variance and composition order | Check them with explicit examples before reusing `CategoryTheory.Profunctor`. |
| Catalog quality: paraphrases were drafted with help from automated extraction | A row's statement is re-read against the PDF when it is verified. `unreviewed` rows are not counted as verified. |
| Deviation from the "CWM first" rule | Recorded in §1. Revisit when the CWM text is available. |

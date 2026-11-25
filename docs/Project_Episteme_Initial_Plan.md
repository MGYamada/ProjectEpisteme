# Project Episteme — Initial Formalization Plan

**Target:** *All Concepts Are Kan Extensions* (すべての概念はKan拡張である), Chapters 0–2, as published on [alg-d.com](https://alg-d.com/math/kan_extension/)\
**Language:** Lean 4, with mathlib\
**Planning baseline:** November 15, 2026\
**Status:** Initial plan; implementation and theorem-level audit have not yet begun

## 1. Mission

Project Episteme will construct a traceable, machine-checked formalization of the mathematical content of Chapters 0, 1, and 2 of the category-theory notes hosted at alg-d.com. The central endpoint of this initial program is **Kan extension theory**, including the applications and related constructions that the source places in Chapter 2.

The objective is not merely to define a left or right Kan extension. It is to establish a **source-to-proof correspondence**: every mathematical definition, claim, theorem, substantial worked example, and exercise appearing in the in-scope primary written materials should be associated with a Lean declaration or with an explicit, reviewed explanation of its status. Existing mathlib proofs may be reused; the contribution is complete coverage, exact hypotheses, coherent dependencies, and a reproducible verification record.

The project is neither a fork of mathlib nor an attempt to reproduce pedagogical prose. It will build a small, auditable corpus on top of mathlib, contributing genuinely missing general results upstream when appropriate.

### Scope boundary

**In scope:** All mathematical content in the linked site's Chapter 0, Chapter 1, and Chapter 2, including the advanced Chapter 2 subtopics identified in Section 4 below. This includes material needed from earlier chapters and any mathematical claim in the written source that can be stated precisely.

**Out of scope for this initial program:** Chapters 3–9; an independent new foundation for category theory; formalization of the entire website's non-category-theory content; and systematic transcription of supplementary videos. Videos may be consulted to resolve ambiguity, but written source material controls the inventory. Any prerequisite from later chapters must be implemented only as a bounded dependency, with an explicit reference.

**Provisional limitation:** The section list below comes from the public chapter index, not a line-by-line audit of every linked PDF. It is a *coverage map*, not a claim that all definitions or theorems have already been extracted or matched to mathlib. The first milestone performs that extraction.

## 2. Foundations and formalization policy

### 2.1 Lean and mathematical assumptions

1. Use **Lean 4 and mathlib**, with reproducible, pinned versions (`lean-toolchain` and `lake-manifest.json`).
2. Use **universe-polymorphic categories**, generally with objects in `Type u` and morphisms in `Type v`, following `CategoryTheory.Category.{v, u}`.
3. **Do not add the Grothendieck universe axiom.** Lean's existing hierarchy of type universes and mathlib's size-management constructions are the default foundation. Explicit smallness, local smallness, accessibility, and existence assumptions must remain visible in theorems.
4. Never assume a single internal `Type` containing every universe level, or use an inconsistent `Type : Type` principle. Use appropriate universe lifting or shrinking constructs only when justified.
5. The source notes normally assume locally small categories and use the axiom of choice. Preserve these as explicit mathematical or library-level assumptions as applicable. Do not silently strengthen a statement's hypotheses.
6. **No project-specific mathematical axioms, `sorry`, or `admit` in a verified result.** A necessary additional principle would require a separately reviewed foundational decision and a clear axiom-dependency audit.
7. Write source-facing statements as generally as reasonable, while avoiding gratuitous universe parameters or typeclass inference complexity.

The ambient Lean foundations and mathlib's ordinary logical principles are not a claim of being free of metatheoretical set-theoretic strength. The rule above is specifically *no additional Grothendieck universe postulate*.

### 2.2 Reuse before reimplementation

For each source claim, test the following options in order:

1. **Existing:** A mathlib declaration is precisely equivalent to the source claim, including quantifiers and hypotheses.
2. **Bridge:** A short theorem or equivalence translates the source formulation into an existing mathlib result.
3. **New:** A missing result requires an independent Lean proof or a reusable new construction.
4. **Blocked:** A mathematically important prerequisite, universe constraint, or missing formal interface has been identified and recorded.
5. **Non-propositional:** The source item is purely explanatory or motivational, with no standalone formal proposition; its classification is reviewed and documented.

Do **not** mark a claim “Existing” on the basis of a similar declaration name alone. Compare its statement, implicit assumptions, universe levels, naturality conditions, and the direction of every universal property.

### 2.3 Proof quality and review

- All in-scope Lean files must pass `lake build` under the pinned toolchain.
- New theorem statements and proof assumptions must receive mathematical review in addition to kernel checking.
- For important milestones, inspect dependencies using `#print axioms` (or an equivalent automated check).
- Record uses of classical choice, noncomputability, universe lifting, and any strong existence theorem where they matter to mathematical interpretation.
- Prefer canonical mathlib categories, functors, natural transformations, and limits. Avoid duplicate structures that make interoperability harder.
- Separate mathematical equivalence from definitional equality: an equivalence or natural isomorphism is not automatically an equality of Lean objects.

## 3. Source catalog and traceability

The authoritative entry point is [the alg-d.com category-theory index](https://alg-d.com/math/kan_extension/). The publicly visible index organizes the initial target as Chapter 0 (introduction), Chapter 1 (category theory), and Chapter 2 (*All Concepts Are Kan Extensions*). It states that categories are locally small unless otherwise specified, that the exposition is intended to be read in order, and that choice is used without repeated warnings.

### 3.1 Before formalizing any theorem

1. Enumerate **every written PDF/section link** belonging to Chapters 0–2. Record its title in Japanese and a concise English working title.
2. Record the original URL, publication or update date when available, retrieval date, file identifier or checksum for each source version, and page/section numbering.
3. Extract and classify definitions, propositions, theorems, corollaries, exercises, and worked examples. Assign a stable source ID to each item; do not treat the index page as a complete theorem inventory.
4. Translate the mathematical statements into precise English, preserving original hypotheses and direction conventions. For ambiguous statements, record the ambiguity rather than guessing.
5. Search mathlib's current source and API; enter candidate declarations and verify equivalence or create bridge obligations.
6. Only then mark the item as formally covered.

Keep **references and paraphrases**, not unauthorized wholesale copies of copyrighted PDF text. Future revisions of the site should be compared against the recorded baseline, with new or changed items tracked explicitly.

### 3.2 Proposed corpus record

For every formalizable item, maintain an auditable record with at least:

| Field | Purpose |
| --- | --- |
| `id` | Stable identifier, e.g. `ALGD-C2-KAN-001` |
| `source` | PDF URL, document version, page/section and original local numbering |
| `kind` | Definition, theorem, corollary, exercise, example, or note |
| `statement` | Concise mathematical paraphrase with quantified hypotheses |
| `mathlib` | Candidate or confirmed mathlib declaration and commit/version |
| `lean` | Full name of Episteme's verified declaration or bridge theorem |
| `status` | `unreviewed`, `existing`, `bridged`, `new-proved`, `blocked`, or `non-propositional` |
| `assumptions` | Choice, smallness, completeness, universe levels, etc. |
| `review` | Statement reviewed? Proof compiled? Axioms checked? |

**Coverage rule:** “Mapped” means a source item has a record. “Verified” means the corresponding Lean statement has been checked and source equivalence reviewed. The two must not be conflated.

## 4. Mathematical coverage map

The following is the **provisional top-level section inventory** from the public chapter index. Subsections, numbered statements, and examples within the PDFs are to be expanded in the catalog created in Milestone M0.

### Chapter 0 — Introduction to category theory

| Workstream | Content to cover | Representative verification obligations |
| --- | --- | --- |
| C0.1 Basic language | Categories, objects, morphisms, identity, composition, examples, functors, contravariance | Category laws; functor laws; opposite categories; instances for types, preorders, and groups where the text calls for them |
| C0.2 Commutative diagrams | Diagrammatic notation and commutativity | Equations corresponding to diagrammatic assertions |
| C0.3 Category constructions | Product, coproduct/disjoint union where applicable, slice and coslice categories, subcategories | Category instances and universal properties of constructions |
| C0.4 Universal properties | Introductory universal constructions and uniqueness | Existence/uniqueness up to unique isomorphism under correct assumptions |
| C0.5 Sheaves: first example | Introductory sheaves on topological spaces | Precise source-level definitions and basic examples; full sheaf-theoretic development is coordinated with C2.4 |
| C0.6 Duality | Opposite categories, dual statements about limits, monomorphisms/epimorphisms | Formally stated duality principles and selected instances |
| C0.7 Natural transformations and equivalence | Natural transformations, full/faithful/essentially surjective functors, equivalences | Naturality, functoriality, characterizations of equivalence |
| C0.8 Fundamental groupoid example | Groupoid viewpoint on fundamental groups | Definitions and examples needed by the written source; record any topology prerequisites |

**Gate C0:** Every mathematical item in the written Chapter 0 materials is cataloged and its status resolved. Core examples compile and reuse canonical mathlib interfaces. Potentially substantial topology prerequisites have explicit, reviewed dependency records.

### Chapter 1 — Category-theoretic infrastructure

| Workstream | Content to cover | Representative verification obligations |
| --- | --- | --- |
| C1.1 Natural transformations and functor categories | Vertical composition, whiskering, functor categories, induced functors between them | Category laws for functor categories; naturality and composition |
| C1.2 Yoneda lemma | Covariant/contravariant representables, Yoneda embedding, naturality, applications | Yoneda equivalence and natural isomorphism; full faithfulness; carefully stated applications |
| C1.3 Comma categories | Comma objects/categories and their universal constructions | Category structure and universal properties |
| C1.4 Limits and colimits | Cones/cocones, completeness, existence criteria, limits in types/sets, representability, preservation and interchange | Equivalence of universal properties; product/equalizer generation where assumed; preservation results |
| C1.5 Adjunctions | Hom-set adjunctions, units/counits, universal arrows, relation to equivalences, preservation of limits, Cartesian closure and idempotent adjunctions | Equivalence of common definitions; triangle identities; preservation assertions |

**Gate C1:** The Yoneda, comma-category, (co)limit, and adjunction interfaces needed for Kan extensions are verified and their source correspondences reviewed. Mathematical claims about size, existence, or representability have no implicit gap.

### Chapter 2 — All Concepts Are Kan Extensions

**Important:** Chapter 2 is much broader than the single introductory PDF on Kan extensions. The target includes all of the following indexed sections.

| Workstream | Indexed section | Scope and key obligations |
| --- | --- | --- |
| C2.1 | **Kan extensions** | Universal definitions of left/right Kan extensions; universal arrows; uniqueness up to canonical isomorphism; existence under explicit hypotheses; pointwise constructions; universal adjunction; relationships to adjunctions, generators and dense functors |
| C2.2 | **Simplicial sets** | Simplicial indexing, simplicial sets, explicit examples, horns, spheres, degeneracy, Eilenberg–Zilber lemma, skeleton/coskeleton, and the universal-adjunction applications actually present in the source |
| C2.3 | **Adjoint functor theorems** | Solution-set condition, initial/terminal/cofinal functor constructions, applicable adjoint functor theorems, and the source's Stone–Čech application |
| C2.4 | **Sheaves on topological spaces, part 2** | Presheaves, stalks, étalé spaces, sheafification, and the relevant adjunctions/equivalences |
| C2.5 | **“Logarithm” of a category** | The section's specific categorical construction and claims, to be extracted from its PDF before assigning mathematical names |
| C2.6 | **Filtered categories** | Filtered/sifted categories, filtered colimits, flat functors, and equivalence statements actually proved in the source |
| C2.7 | **Ends and coends** | End/coend definitions, universal properties, end formulas and pointwise Kan extension via coends, with necessary smallness assumptions |
| C2.8 | **Co-Yoneda lemma** | Variants of the co-Yoneda lemma and relation to Kan extensions |
| C2.9 | **Cocomma categories and profunctors** | Cocomma constructions, profunctor interpretation, and the source's example isomorphisms |
| C2.10 | **Isbell duality** | Relevant Isbell conjugacy/duality constructions and comparison theorems stated in the source |

The Chapter 2 source also uses supplementary examples (including presheaf inverse images, effect algebras, differential spaces, and choice). Such examples must enter the ledger if they contain substantive mathematical claims in the **primary written material**. Items appearing only in optional videos are supplemental, not automatic release blockers.

**Gate C2:** Every mathematical statement and example in all written Chapter 2 sections is audited and accounted for. The universal-property and adjunction-based Kan extension infrastructure is verified, and every claim relying on pointwise formulas, density, or completeness has its assumptions made explicit. Advanced sections such as simplicial sets and sheafification cannot be silently omitted from a claim of complete Chapter 2 coverage.

## 5. Kan extension: central mathematical specification

Let `K : C ⥤ D` and `F : C ⥤ E` be functors. A left Kan extension `Lan_K F : D ⥤ E`, when it exists, is characterized by a universal comparison natural transformation `F ⟶ K ⋙ Lan_K F` (in mathlib's diagrammatic composition convention). For any `G : D ⥤ E`, the universal property takes the form

\[
\operatorname{Nat}(\operatorname{Lan}_K F,G)
\cong
\operatorname{Nat}(F,G\circ K).
\]

For a right Kan extension the dual property is

\[
\operatorname{Nat}(G,\operatorname{Ran}_K F)
\cong
\operatorname{Nat}(G\circ K,F).
\]

With the relevant extensions existing functorially for all `F`, precomposition `K^* : [D,E] ⟶ [C,E]` has the expected adjoints:

\[
\operatorname{Lan}_K\dashv K^*\dashv\operatorname{Ran}_K.
\]

### Core verification obligations

1. State and check the left and right **universal properties**, including naturality of the hom-equivalences.
2. Check **uniqueness up to canonical isomorphism** and invariance under replacing data by isomorphic data.
3. Distinguish **general Kan extensions** from **pointwise Kan extensions**; do not identify them without the appropriate theorem.
4. Formalize the **comma/cocomma-category limit and colimit expressions** only under the actual diagram-size and completeness conditions.
5. Check the **precomposition adjunctions**, including unit/counit compatibility and triangle identities.
6. Verify the source's examples and derived uses: ordinary adjunctions, dense functors, Yoneda/co-Yoneda, and relevant pointwise formulas.
7. Trace the precise hypotheses when the source applies Kan extensions to sheaves, simplicial sets, filtered colimits, ends/coends, and Isbell duality.

### Relevant existing mathlib entry points (candidates for the source audit)

- [Category and universe conventions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Basic.html)
- [Functor categories](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/Category.html)
- [Yoneda](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Yoneda.html)
- [Kan extension: basic universal properties](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/KanExtension/Basic.html)
- [Kan extension: pointwise theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/KanExtension/Pointwise.html)
- [Kan extension and adjunctions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/KanExtension/Adjunction.html)
- [Kan extension preservation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/KanExtension/Preserves.html)
- [Kan extensions in bicategories](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Bicategory/Kan/HasKan.html)

These are **verified library entry points**, not verified one-to-one correspondences for every alg-d.com theorem. For example, mathlib already exposes `CategoryTheory.Functor.IsLeftKanExtension`, pointwise Kan extension constructions, and `CategoryTheory.Functor.lanAdjunction`. Each claim still requires a statement-level match against the source.

## 6. Proposed repository organization

The following is a suggested layout, **not an assertion that the files already exist**:

```text
ProjectEpisteme/
  Category/
    Chapter0/
      Basics.lean
      Constructions.lean
      UniversalProperties.lean
      Examples.lean
    Chapter1/
      FunctorCategories.lean
      Yoneda.lean
      Comma.lean
      Limits.lean
      Adjunctions.lean
    Chapter2/
      KanExtension.lean
      KanAdjunction.lean
      Pointwise.lean
      Simplicial.lean
      AdjointFunctorTheorems.lean
      Sheaves.lean
      CategoryLogarithm.lean
      Filtered.lean
      EndsCoends.lean
      CoYoneda.lean
      Profunctors.lean
      Isbell.lean
  Category.lean
docs/
  algd-source-index.md
  algd-coverage.md
  algd-axiom-audit.md
  algd-open-questions.md
```

Module boundaries may be refined to match mathlib's organization. The `docs` catalog is essential: it is the authoritative proof-coverage ledger, not a decorative afterthought.

## 7. Implementation sequence and release gates

The milestones are **dependency-based**, without arbitrary version numbers or calendar deadlines.

| Milestone | Deliverable | Acceptance gate |
| --- | --- | --- |
| **M0 — Source inventory** | Frozen source list, statement IDs, PDF-level provenance, initial mathlib candidate map | Every in-scope PDF and index section enumerated; all claims have an inventory entry or a documented extraction task |
| **M1 — Chapter 0** | Basic-category proofs/bridges and examples | C0 coverage ledger complete; all targeted Lean declarations compile; axiom and size assumptions reviewed |
| **M2 — Chapter 1** | Yoneda, comma, (co)limit, adjunction interfaces | C1 coverage ledger complete and suitable for use by the Kan extension workstreams |
| **M3 — Core Kan extensions** | Left/right Kan extension properties; pointwise theory; Kan/precomposition adjunctions; principal applications | C2.1 complete, with correct universal-property direction and naturality, and no unresolved core blockers |
| **M4 — Chapter 2 applications** | Simplicial sets, adjoint functor theorems, sheaves, filtered categories, ends/coends, co-Yoneda, profunctors, Isbell duality, and category logarithm | C2.2–C2.10 complete; all advanced prerequisites documented and compiled |
| **M5 — Complete audit** | Source-to-Lean coverage report and independently reviewed dependency summary | Every mathematical item in Chapters 0–2 is `existing`, `bridged`, or `new-proved`; no unreviewed/blocked proof obligations remain; all tests pass |

### First actionable tasks

1. Pin the Lean/mathlib versions and create an empty, compiling Episteme package.
2. Build `docs/algd-source-index.md`, listing all Chapter 0–2 written sources in index order.
3. Extract the statements of the Chapter 0 PDFs, preserving assumptions and original numbering.
4. Produce a mathlib correspondence table for the category/functor/universal-property basics, then the Chapter 1 prerequisites.
5. Prototype one complete **source → Lean statement → mathlib bridge → verification** record, ideally for a basic category/adjunction property.
6. Independently map the Chapter 2 Kan extension PDF to `IsLeftKanExtension`, `IsRightKanExtension`, pointwise variants, and `lanAdjunction` before defining new abstractions.

## 8. Verification, CI, and reporting

- **Build:** `lake build` on the pinned toolchain and mathlib commit for every pull request.
- **No holes:** Fail review if new verified modules contain `sorry`, `admit`, unexplained new `axiom`, or a proof hidden behind an unreviewed assumption.
- **Statement review:** Every source-facing theorem gets a mathematical equivalence check between the original statement and Lean's elaborated theorem type.
- **Dependency audit:** Record the theorem's universe parameters, smallness assumptions, classical principles, and axiom dependencies. Treat additional foundational axioms as change-controlled exceptions.
- **Duality tests:** Where the source states a dual result, verify that the formal statement is genuinely dual, including variance and direction of unit/counit maps.
- **Coverage report:** Generate counts by chapter and workstream for `unreviewed`, `existing`, `bridged`, `new-proved`, `blocked`, and `non-propositional`. Publish both **mapped** and **verified** percentages, with denominators fixed by the source catalog.
- **Regression:** When mathlib upgrades or the original PDFs change, rerun the build and revalidate affected source-to-statement mappings.

### Completion definition

The initial program is complete only when **every mathematical obligation in the written source for Chapters 0–2** has a verified Lean representation, an independently reviewed equivalence to the source claim, and a reproducible audit trail. Merely importing mathlib's Kan extension modules does not satisfy this criterion.

## 9. Risks and decisions to record

| Issue | Default resolution |
| --- | --- |
| Evolving source PDFs | Pin a baseline, compare later revisions, and add changed statements as explicit work items |
| Hidden assumptions in informal mathematics | Record the strongest mathematically necessary explicit assumptions, then determine whether the statement can be weakened |
| General versus pointwise Kan extensions | Keep separate declarations and prove their relationship only under explicit hypotheses |
| Universe-level elaboration failures | Refine universe parameters, use mathlib's size and lift interfaces, and document genuine size restrictions; do not add a blanket universe axiom |
| Overlap with mathlib | Prefer bridge theorems and upstreamable general results over parallel incompatible implementations |
| Deep Chapter 2 dependencies | Maintain dedicated workstreams for simplicial sets, topology/sheaves, and profunctors rather than treating them as optional notes |
| Incomplete catalog from index alone | Do not publish completion percentages until each linked PDF has been read and its claims inventoried |
| Copyright and attribution | Link to the original author and sources; paraphrase mathematical statements as needed and avoid reproducing the full PDFs |

## 10. References

### Primary source

- [alg-d.com — Category Theory / All Concepts Are Kan Extensions](https://alg-d.com/math/kan_extension/), Chapters 0–2 (index inspected November 15, 2026). The original index and linked PDFs, not this plan, determine final theorem-level scope.

### Formalization foundations

- [Lean 4 Language Reference: Universes](https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/)
- [mathlib: Category Basics](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Basic.html)
- [mathlib: Kan Extension Basics](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/KanExtension/Basic.html)
- [mathlib: Pointwise Kan Extensions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/KanExtension/Pointwise.html)
- [mathlib: Kan Extension Adjunctions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/KanExtension/Adjunction.html)

---

**Project principle:** Formalize the *content and logical dependency structure* of the text, not just its terminology. The destination is a complete, universe-disciplined, axiom-audited pathway from elementary categories to Kan extensions and all of the Chapter 2 applications.

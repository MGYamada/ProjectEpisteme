# Project Episteme contributor instructions

## Sources and scope

- Read the [README](README.md) and the [design](docs/Project_Episteme_Design.md) before working on a track. See the [Initial Plan](docs/Project_Episteme_Initial_Plan.md) for the Category track’s supplementary sources and the [Joyal–Street Roadmap](docs/Project_Episteme_Joyal_Street_Coherence_Roadmap.md) for the coherence proof plan.
- Record the edition, chapter, section, page, and original theorem number when available. Paraphrase the mathematical content and link to the source. Keep separate source IDs for CWM, alg-d.com, Joyal–Street, and Tôhoku. Multiple source items may point to the same Lean declaration.
- Verify the definitions, theorems, and representative examples in the main text of CWM first. Record each exercise’s source and statement in the ledger alongside the main text. Prove the exercises in a later phase. Report the counts of verified main-text items and cataloged exercises in the first progress report.
- Exception for the Category track: the CWM text is not available at item level, so alg-d.com Chapters 0–2 take CWM’s place as the main text to verify first. Report that track’s counts against the alg-d ledgers. Once CWM is cataloged item by item, map its items to the same Lean declarations and review their hypotheses separately. The other tracks keep the CWM-first order. See the [Category strategy](docs/Project_Episteme_Category_Strategy.md).
- Treat declarations found in public API documentation as candidates. Compare them with the source in the pinned mathlib revision, checking the hypotheses, direction, naturality, and universe levels. Record any differences and identify a bridging result, a change in hypotheses, or an unresolved prerequisite.

## Working in Lean

- Use the Lean toolchain and package revisions recorded in `lean-toolchain` and `lake-manifest.json`. Update dependencies as part of a change that explicitly addresses the dependency pins.
- Reuse mathlib types, type classes, and theorems. When the source uses a different formulation, consider a bridging lemma. Add definitions and proofs for obligations the existing declarations do not cover. Use the narrowest imports needed and consider contributing generally useful results to mathlib.
- Follow mathlib notation, including `X ⟶ Y`, `f ≫ g`, and `Cᵒᵖ`. Separate object and morphism universes when needed. Record relevant smallness assumptions, uses of choice or classical logic, and noncomputability. Distinguish natural isomorphism from definitional equality. Use Lean’s existing universe hierarchy and foundations.
- Check morphism direction and composition order with examples when working with braidings, permutation actions, duality, or complexes. Use the hypotheses each theorem needs, such as `Abelian`, the Grothendieck condition, left exactness, or enough injectives.

## Verification and reporting

Check the changed modules with `lake env lean <file.lean>` while working. Run `lake build` before calling the work complete. Use `#print axioms` on key declarations and check their types and imports under the same pins. Verified results must be free of `sorry`, `admit`, and additional mathematical axioms, including a Grothendieck universe axiom.

For each verified item, record the corresponding Lean declaration and the review of its hypotheses and conclusion against the source. Identify candidates, unresolved prerequisites, and any verification that could not run. Report progress against the scope and the actual state of verification.

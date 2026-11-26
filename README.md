# M⊗AI (Project Episteme)

M⊗AI (pronounced /moai/) is a *proof of artificial intelligence* project that starts with category theory and aims toward **Bourbaki 2.0**. People and AI work from mathematical sources, make the hypotheses explicit, and formalize the results in Lean 4 with mathlib. People check AI-proposed statements against the sources, and the Lean kernel checks their proofs.

The first goal is to formalize the second edition of Saunders Mac Lane’s *Categories for the Working Mathematician* (CWM). Each definition, theorem, and example should be traceable from the source to its Lean declaration and verification record. [CWM, second edition](https://link.springer.com/book/10.1007/978-1-4757-4721-8)

## Formalization plan

| Track | Initial scope |
| --- | --- |
| **1. Category (Mac Lane 2.0)** | Categories, functors, natural transformations, the Yoneda lemma, limits, and adjunctions lead to CWM’s Kan extensions. Chapters 0–2 of the notes on alg-d.com supply additional examples and applications. |
| **2. Monoidal category (Mac Lane 2.0)** | Start with CWM’s monoidal categories, prove braided coherence using Joyal–Street’s free braid categories, and derive symmetric coherence through the braid group quotient. |
| **3. Abelian category (Grothendieck’s Tôhoku 2.0)** | Start with CWM’s abelian categories and work toward exact sequences, Grothendieck categories, enough injectives, and right-derived functors as developed in the Tôhoku paper. |

Verify the definitions, theorems, and representative examples in the main text of CWM first. Record the exercises in the ledger as each chapter is cataloged and prove them in a later phase. The Category track is the exception: the CWM text is not available at item level, so alg-d.com Chapters 0–2 lead that track until CWM can be cataloged item by item.

The first formalization milestone is to take one theorem from source review through a Lean build and an axiom audit. The Yoneda lemma is the example. The Category track did this with alg-d’s 米田の補題, the counterpart of CWM III §2.

- [Design and verification criteria](docs/Project_Episteme_Design.md)
- [Category track strategy](docs/Project_Episteme_Category_Strategy.md), with the [alg-d source index](docs/algd-source-index.md) and [coverage](docs/algd-coverage.md)
- [Notes on alg-d.com, Chapters 0–2, and the Kan extension plan](docs/Project_Episteme_Initial_Plan.md)
- [Joyal–Street coherence roadmap](docs/Project_Episteme_Joyal_Street_Coherence_Roadmap.md)
- [Contributor instructions](AGENTS.md)

## Build

The project uses the same dependency pins as Project Ainos. The toolchain selects Lean 4.35.0. The Lake manifest locks mathlib v4.35.0 at `56a005855ea17e0b0958f73ec801ae140b0a1679` and records the transitive package revisions. [Lean toolchain](lean-toolchain) [Lake manifest](lake-manifest.json)

Run the build from the repository root.

```sh
lake build
```

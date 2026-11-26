# ALGD-C1-YONEDA — 米田の補題 (The Yoneda lemma)

| Field | Value |
| --- | --- |
| Source | [yoneda.pdf](https://alg-d.com/math/kan_extension/yoneda.pdf), alg-d, 「全ての概念はKan拡張である」, Chapter 1 |
| Printed date | 2026-05-14 |
| Pages | 8 |
| SHA-256 | 277839b95dbff53e75197c012d304eea500f6944ca34786dbf3951937f10f586 |
| Retrieved | 2026-11-26 |
| Numbered items | 1–11 (9 items, 2 equation labels: (3), (8)) |
| Unnumbered definitions | 5 (all introduced in prose) |
| Prose claims (R) | 3 |
| Exercises | 0 |
| Lean module | [`ProjectEpisteme/Category/AlgD/C1/Yoneda.lean`](../../../ProjectEpisteme/Category/AlgD/C1/Yoneda.lean), namespace `ProjectEpisteme.AlgD.Yoneda` |
| Environment | Lean v4.35.0, mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; `lake build` passed on 2026-11-26 |

This is the pilot ledger of the Category track. In the Lean column, the first name is the source-layer theorem that states the item in the source's own formulation, and the name after "via" is the mathlib declaration it uses. The universe conventions for every row are `C : Type u` with `[Category.{v} C]` and `Set = Type v`. The axiom audit for every verified row is `[propext, Classical.choice, Quot.sound]`, pinned with `#guard_msgs` in the module.

## Items

| ID | Kind | Location | Statement (paraphrase) | mathlib candidates | Lean | Status | Assumptions | Review |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| ALGD-C1-YONEDA-D01 | definition | prose, p.1 | For a fixed object a, the hom functor Hom_C(a, −) : C → Set sends b to Hom_C(a, b) and g : b → b′ to g ∘ − | `CategoryTheory.coyoneda` (`coyoneda.obj (op a)`), Mathlib/CategoryTheory/Yoneda.lean | — | unreviewed | locally small | candidate only |
| ALGD-C1-YONEDA-R01 | prose-claim | prose box, p.1 | Hom_C(a, −) preserves identities and composition, so it is a functor | built into `CategoryTheory.coyoneda` | — | unreviewed | locally small | candidate only |
| ALGD-C1-YONEDA-D02 | definition | prose, p.2 | Hom_C(−, a) := Hom_{C^op}(a, −) : C^op → Set; for f : b′ → b it sends h to h ∘ f | `CategoryTheory.yoneda` (`yoneda.obj a`), Mathlib/CategoryTheory/Yoneda.lean | `CategoryTheory.yoneda` | existing | locally small | definition read: `(yoneda.obj a).map f h = f.unop ≫ h`, which is h ∘ f |
| ALGD-C1-YONEDA-D03 | definition | prose, p.2 | The two-variable hom functor Hom_C : C^op × C → Set, with Hom_C(f, g)(h) = g ∘ h ∘ f for f : a′ → a, g : b → b′ | `CategoryTheory.Functor.hom`, Mathlib/CategoryTheory/Functor/Hom.lean | — | unreviewed | locally small | candidate only |
| ALGD-C1-YONEDA-R02 | prose-claim | prose, p.2 | Hom_C : C^op × C → Set is a functor (stated as easy) | built into `CategoryTheory.Functor.hom` | — | unreviewed | locally small | candidate only |
| ALGD-C1-YONEDA-D04 | definition | prose and box, p.2 | The Yoneda embedding y : C → Set^{C^op} is obtained from Hom_C by currying: y(a) = Hom_C(−, a), and for f : a → b, y(f) : y(a) ⇒ y(b) has components y(f)_s = f ∘ − | `CategoryTheory.yoneda`, Mathlib/CategoryTheory/Yoneda.lean | `CategoryTheory.yoneda` | existing | locally small; currying uses the 「自然変換・関手圏」 PDF | definition read: `(yoneda.map f).app s g = g ≫ f`, which is f ∘ g |
| ALGD-C1-YONEDA-D05 | definition | prose, p.2 | Notation Ĉ := Set^{C^op}, so y : C → Ĉ | `Cᵒᵖ ⥤ Type v` | — | non-propositional | locally small; Ĉ has hom-sets in `Type (max u v)` | notation only |
| ALGD-C1-YONEDA-01 | theorem (米田の補題) | 定理 1, p.2 | For a category C, an object a, and a functor P : C^op → Set, the map φ_{a,P} : Hom_Ĉ(y(a), P) → P(a), θ ↦ θ_a(id_a), is a bijection (the map is the one defined in the proof) | `CategoryTheory.yonedaEquiv` | `yoneda_bijective` via `yonedaEquiv.bijective` | existing | locally small; P valued in `Type v` | verified: `yonedaEquiv θ = θ.app (op a) (𝟙 a)` is `yonedaEquiv_apply` (rfl); statement keeps the explicit map so 定理 10/11 refer to the same φ |
| ALGD-C1-YONEDA-R03 | prose-claim | prose, p.4 | Dually, for P : C → Set, Hom_{Set^C}(Hom_C(a, −), P) ≅ P(a) | `CategoryTheory.coyonedaEquiv` | — | unreviewed | locally small | candidate only |
| ALGD-C1-YONEDA-02 | corollary | 系 2, p.4 | y : C → Ĉ is fully faithful, i.e. for all a, b the map Hom_C(a, b) → Hom_Ĉ(y(a), y(b)), f ↦ y(f), is bijective | `CategoryTheory.Yoneda.fullyFaithful`, `Functor.FullyFaithful.map_bijective` | `yoneda_map_bijective` via `Yoneda.fullyFaithful.map_bijective` | existing | locally small | verified: source's 忠実充満 is bijectivity on hom-sets, matching `map_bijective` |
| ALGD-C1-YONEDA-03 | equation | (3), p.5 | For θ : y(a) ⇒ y(b) and the morphism f : a → b corresponding to θ under the Yoneda lemma, θ is a natural isomorphism iff f is an isomorphism | `Yoneda.fullyFaithful.map_preimage`, `CategoryTheory.isIso_iff_of_reflects_iso` | `isIso_iff_isIso_yonedaEquiv` | bridged | locally small; uses the 「自然変換・圏同値」 PDF (fully faithful functors reflect isomorphisms) | verified: f is taken as `yonedaEquiv θ`, as in the source; natural isomorphism is `IsIso` in the functor category |
| ALGD-C1-YONEDA-04 | corollary | 系 4, p.5 | If y(a) ≅ y(b) then a ≅ b | `Functor.FullyFaithful.preimageIso` | `nonempty_iso_of_yoneda_iso` via `Yoneda.fullyFaithful.preimageIso` | existing | locally small | verified: ≅ read as existence of an isomorphism (`Nonempty`) |
| ALGD-C1-YONEDA-05 | theorem | 定理 5, p.5 | If there are bijections Hom_C(x, a) ≅ Hom_C(x, b) natural in x ∈ C, then a ≅ b | `CategoryTheory.Yoneda.ext` | `nonempty_iso_of_natural_equiv_hom_to` via `Yoneda.ext` | bridged | locally small | verified: naturality written out as `e (g ≫ h) = g ≫ e h` for g : x′ → x, which is the source's explicit form of the natural isomorphism y(a) ≅ y(b) |
| ALGD-C1-YONEDA-06 | theorem | 定理 6, p.5 | Dually, if there are bijections Hom_C(a, x) ≅ Hom_C(b, x) natural in x ∈ C, then a ≅ b | `CategoryTheory.Coyoneda.ext` | `nonempty_iso_of_natural_equiv_hom_from` via `Coyoneda.ext` | bridged | locally small | verified: naturality `e (h ≫ g) = e h ≫ g`; `Coyoneda.ext` asks for naturality of the inverse, derived in the proof |
| ALGD-C1-YONEDA-07 | lemma | 補題 7, p.6 | For F : A → B, G : A → E, K : B → E and θ_a : K(F a) → G a, let θ̃_a : y(F a) ⇒ Hom_E(K−, G a) correspond to θ_a under the Yoneda lemma; then θ̃ is natural in a iff θ is natural in a | none found as a single lemma; built from `yonedaEquiv_naturality`, `yonedaEquiv_comp` | `yonedaEquiv_symm_natural_iff_natural` | new-proved | B and E share the hom universe (`Category.{v}`), so Hom_E(K−, G a) is a presheaf on B in `Type v`; A arbitrary | verified: θ̃ naturality is diagram (8), `y(F f) ≫ θ̃_{a'} = θ̃_a ≫ (G f ∘ −)`; θ naturality is `K (F f) ≫ θ_{a'} = θ_a ≫ G f` |
| ALGD-C1-YONEDA-08 | equation | (8), p.6 | Labels the naturality square of θ̃ used in the statement and proof of 補題 7 | — | encoded in `yonedaEquiv_symm_natural_iff_natural` | non-propositional | — | diagram label only |
| ALGD-C1-YONEDA-09 | proposition | 命題 9, p.7 | For functors F, G : C → D, if there are bijections Hom_D(d, F c) ≅ Hom_D(d, G c) natural in c ∈ C and d ∈ D, then F ≅ G | `Functor.FullyFaithful.whiskeringRight`, `Yoneda.fullyFaithful` | `nonempty_iso_of_yoneda_comp_iso` | bridged | C and D locally small with independent hom universes | verified: the doubly natural bijection is encoded as an isomorphism `F ⋙ yoneda ≅ G ⋙ yoneda` (component at c is natural in d; naturality square is naturality in c); a follow-up could add the unbundled form |
| ALGD-C1-YONEDA-10 | theorem | 定理 10, p.7 | φ_{a,P} is natural in a: for f : a → b and θ : y(b) ⇒ P, P f (φ_{b,P} θ) = φ_{a,P}(θ ∘ y(f)); hence a natural isomorphism Hom_Ĉ(y(−), P) ⇒ P | `CategoryTheory.yonedaEquiv_naturality`; bundled: `CategoryTheory.yonedaLemma` | `yonedaEquiv_natural_in_object` via `yonedaEquiv_naturality` | existing | locally small; the bundled iso lands in `Type (max u v)` | verified: `θ ∘ y(f)` is `yoneda.map f ≫ θ`; the bundled natural isomorphism is not restated |
| ALGD-C1-YONEDA-11 | theorem | 定理 11, p.8 | φ_{a,P} is natural in P: for σ : P ⇒ Q and θ : y(a) ⇒ P, σ_a(φ_{a,P} θ) = φ_{a,Q}(σ ∘ θ); hence a natural isomorphism Hom_Ĉ(y(a), −) ⇒ ev_a | `CategoryTheory.yonedaEquiv_comp`; bundled: `CategoryTheory.yonedaLemma` | `yonedaEquiv_natural_in_presheaf` via `yonedaEquiv_comp` | existing | locally small | verified: `σ ∘ θ` is `θ ≫ σ`; the bundled natural isomorphism is not restated |

## Notes

- The shared counter also numbers displayed equations: (3) on p.5 and (8) on p.6 take numbers 3 and 8. They are rows 03 and 08 so that IDs match the source numbers.
- 定理 10 and 定理 11 each end with a bundled restatement ("即ち … 自然同型"). The Lean rows verify the componentwise naturality equations that the source proves. The bundled forms are mathlib's `yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C`, which uses `ULift` because `Hom_Ĉ(y(a), P)` lives in `Type (max u v)`. A follow-up can state the two one-variable bundled isomorphisms separately.
- `Classical.choice` appears in every axiom list through mathlib's category-theory library. None of the source statements needs choice beyond that.
- Cross-references: the hyphen notation and currying refer to 「自然変換・関手圏」 (ALGD-C1-NAT). The fact that fully faithful functors reflect isomorphisms, used for (3), refers to 「自然変換・圏同値」 (ALGD-C0-EQUIV).
- CWM: 定理 1, 定理 10, and 定理 11 correspond to CWM2 III §2. Item-level CWM IDs wait for the CWM catalog.

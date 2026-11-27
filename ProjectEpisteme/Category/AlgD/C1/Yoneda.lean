/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Yoneda

/-!
# alg-d, Chapter 1: 米田の補題 (The Yoneda lemma)

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 1, `yoneda.pdf`
(<https://alg-d.com/math/kan_extension/yoneda.pdf>), printed date 2026-05-14,
SHA-256 `277839b95dbff53e75197c012d304eea500f6944ca34786dbf3951937f10f586`,
retrieved 2026-11-26. Ledger: `docs/ledger/algd/C1-YONEDA.md`.

This is the source layer of the Category track. Each declaration states one numbered
item of the PDF in the source's own formulation and proves it from mathlib. The first
line of each docstring is the source ID.

## Conventions

* alg-d writes `C` for a locally small category. Here `C : Type u` with
  `[Category.{v} C]`, and `Set` is `Type v`.
* alg-d's `Ĉ = Set^{C^op}` is `Cᵒᵖ ⥤ Type v`, and `y` is `CategoryTheory.yoneda`.
  `Ĉ` is not locally small in general: its hom-types live in `Type (max u v)`.
* alg-d composes as `g ∘ f`; mathlib writes `f ≫ g`. In particular the source's
  `θ ∘ y(f)` is `yoneda.map f ≫ θ`, and `σ ∘ θ` is `θ ≫ σ`.
* The bijection `φ_{a,P}(θ) = θ_a(id_a)` constructed in the proof of 定理 1 is
  mathlib's `CategoryTheory.yonedaEquiv` (definitionally, see `yonedaEquiv_apply`).
* A natural isomorphism in the source ("自然同型") is an isomorphism in the functor
  category; mathlib's `NatIso.isIso_iff_isIso_app` relates it to componentwise
  isomorphisms.
-/

@[expose] public section

namespace ProjectEpisteme.AlgD.Yoneda

open CategoryTheory Opposite

universe w v u

variable {C : Type u} [Category.{v} C]

/-- `ALGD-C1-YONEDA-01` (定理 1, 米田の補題, p.2).
For an object `a` and a presheaf `P : Cᵒᵖ ⥤ Type v`, the map
`Hom_Ĉ(y(a), P) → P(a)`, `θ ↦ θ_a(id_a)`, is a bijection. -/
theorem yoneda_bijective (a : C) (P : Cᵒᵖ ⥤ Type v) :
    Function.Bijective (fun θ : yoneda.obj a ⟶ P ↦ θ.app (op a) (𝟙 a)) :=
  yonedaEquiv.bijective

/-- `ALGD-C1-YONEDA-02` (系 2, p.4).
The Yoneda embedding `y : C → Ĉ` is fully faithful: for all `a b : C`, the map
`Hom_C(a, b) → Hom_Ĉ(y(a), y(b))` is a bijection. -/
theorem yoneda_map_bijective (a b : C) :
    Function.Bijective (yoneda.map : (a ⟶ b) → (yoneda.obj a ⟶ yoneda.obj b)) :=
  Yoneda.fullyFaithful.map_bijective a b

/-- `ALGD-C1-YONEDA-03` (displayed equivalence (3), p.5).
Let `θ : y(a) ⇒ y(b)` and let `f : a → b` be the morphism corresponding to `θ`
under the Yoneda lemma. Then `θ` is a natural isomorphism if and only if `f` is
an isomorphism. -/
theorem isIso_iff_isIso_yonedaEquiv {a b : C} (θ : yoneda.obj a ⟶ yoneda.obj b) :
    IsIso θ ↔ IsIso (yonedaEquiv θ : a ⟶ b) := by
  have h : yoneda.map (yonedaEquiv θ : a ⟶ b) = θ := Yoneda.fullyFaithful.map_preimage θ
  conv_lhs => rw [← h]
  exact (isIso_iff_of_reflects_iso _ yoneda)

/-- `ALGD-C1-YONEDA-04` (系 4, p.5).
If `y(a) ≅ y(b)` then `a ≅ b`. -/
theorem nonempty_iso_of_yoneda_iso {a b : C} (h : Nonempty (yoneda.obj a ≅ yoneda.obj b)) :
    Nonempty (a ≅ b) :=
  h.map Yoneda.fullyFaithful.preimageIso

/-- `ALGD-C1-YONEDA-05` (定理 5, p.5).
If there are bijections `Hom_C(x, a) ≅ Hom_C(x, b)` natural in `x ∈ C`, then `a ≅ b`.
Naturality in `x` is stated as `e (g ∘ h) = (e h) ∘ g` for `g : x' → x`, that is,
`e (g ≫ h) = g ≫ e h`. -/
theorem nonempty_iso_of_natural_equiv_hom_to {a b : C} (e : ∀ x : C, (x ⟶ a) ≃ (x ⟶ b))
    (he : ∀ {x x' : C} (g : x' ⟶ x) (h : x ⟶ a), e x' (g ≫ h) = g ≫ e x h) :
    Nonempty (a ≅ b) :=
  ⟨Yoneda.ext a b (fun {x} ↦ e x) (fun {x} ↦ (e x).symm) (fun _ ↦ (e _).symm_apply_apply _)
    (fun _ ↦ (e _).apply_symm_apply _) he⟩

/-- `ALGD-C1-YONEDA-06` (定理 6, p.5).
If there are bijections `Hom_C(a, x) ≅ Hom_C(b, x)` natural in `x ∈ C`, then `a ≅ b`.
Naturality in `x` is stated as `e (h ≫ g) = e h ≫ g` for `g : x → x'`. -/
theorem nonempty_iso_of_natural_equiv_hom_from {a b : C} (e : ∀ x : C, (a ⟶ x) ≃ (b ⟶ x))
    (he : ∀ {x x' : C} (h : a ⟶ x) (g : x ⟶ x'), e x' (h ≫ g) = e x h ≫ g) :
    Nonempty (a ≅ b) := by
  refine ⟨Coyoneda.ext a b (fun {x} ↦ e x) (fun {x} ↦ (e x).symm)
    (fun _ ↦ (e _).symm_apply_apply _) (fun _ ↦ (e _).apply_symm_apply _) ?_⟩
  intro x x' f g
  apply (e x').injective
  rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]

/-- `ALGD-C1-YONEDA-07` (補題 7, p.6).
Let `F : A → B`, `G : A → E`, `K : B → E`, and let `θ_a : K(F a) → G a` for each
`a ∈ A`. Write `θ̃_a : y(F a) ⇒ Hom_E(K−, G a)` for the natural transformation that
corresponds to `θ_a` under the Yoneda lemma, with `P := Hom_E(K−, G a)`. Then the
family `θ̃` is natural in `a` if and only if `θ` is natural in `a`.

In Lean, `Hom_E(K−, G a)` is `K.op ⋙ yoneda.obj (G.obj a)`, and `θ̃_a` is
`yonedaEquiv.symm (θ a)`. Naturality of `θ̃` is the commutativity of the source's
diagram (8): `y(F f)` followed by `θ̃_{a'}` equals `θ̃_a` followed by `G f ∘ −`.
`B` and `E` share the hom universe `v`, so that `Hom_E(K−, G a)` is a presheaf on
`B` with values in `Type v`. -/
theorem yonedaEquiv_symm_natural_iff_natural {A B E : Type*} [Category A] [Category.{v} B]
    [Category.{v} E] (F : A ⥤ B) (G : A ⥤ E) (K : B ⥤ E)
    (θ : ∀ a : A, K.obj (F.obj a) ⟶ G.obj a) :
    (∀ ⦃a a' : A⦄ (f : a ⟶ a'),
        yoneda.map (F.map f) ≫ (yonedaEquiv (F := K.op ⋙ yoneda.obj (G.obj a'))).symm (θ a') =
          (yonedaEquiv (F := K.op ⋙ yoneda.obj (G.obj a))).symm (θ a) ≫
            Functor.whiskerLeft K.op (yoneda.map (G.map f))) ↔
      ∀ ⦃a a' : A⦄ (f : a ⟶ a'), K.map (F.map f) ≫ θ a' = θ a ≫ G.map f := by
  have key : ∀ ⦃a a' : A⦄ (f : a ⟶ a'),
      (yoneda.map (F.map f) ≫ (yonedaEquiv (F := K.op ⋙ yoneda.obj (G.obj a'))).symm (θ a') =
          (yonedaEquiv (F := K.op ⋙ yoneda.obj (G.obj a))).symm (θ a) ≫
            Functor.whiskerLeft K.op (yoneda.map (G.map f))) ↔
        K.map (F.map f) ≫ θ a' = θ a ≫ G.map f := by
    intro a a' f
    rw [← yonedaEquiv.injective.eq_iff, ← yonedaEquiv_naturality, yonedaEquiv_comp]
    simp
  exact ⟨fun h _ _ f ↦ (key f).1 (h f), fun h _ _ f ↦ (key f).2 (h f)⟩

/-- `ALGD-C1-YONEDA-09` (命題 9, p.7).
Let `F G : C → D`. If there are bijections `Hom_D(d, F c) ≅ Hom_D(d, G c)` natural in
`c ∈ C` and `d ∈ D`, then `F ≅ G`.

A family of bijections natural in both variables is encoded as a natural isomorphism
`F ⋙ yoneda ≅ G ⋙ yoneda` of functors `C ⥤ Dᵒᵖ ⥤ Type v`: its component at `c` is a
natural isomorphism in `d`, and its naturality square is naturality in `c`. The hom
universes of `C` and `D` are independent. -/
theorem nonempty_iso_of_yoneda_comp_iso {D : Type*} [Category.{w} D] {F G : C ⥤ D}
    (h : Nonempty (F ⋙ yoneda ≅ G ⋙ yoneda)) : Nonempty (F ≅ G) :=
  h.map (Functor.FullyFaithful.whiskeringRight Yoneda.fullyFaithful C).preimageIso

/-- `ALGD-C1-YONEDA-10` (定理 10, p.7).
The bijection `φ_{a,P}` of 定理 1 is natural in `a`: for `f : a → b` and
`θ : y(b) ⇒ P`, `P f (φ_{b,P} θ) = φ_{a,P} (θ ∘ y(f))`.

The bundled form, a natural isomorphism in both variables, is mathlib's
`CategoryTheory.yonedaLemma`. -/
theorem yonedaEquiv_natural_in_object {a b : C} (P : Cᵒᵖ ⥤ Type v) (f : a ⟶ b)
    (θ : yoneda.obj b ⟶ P) :
    P.map f.op (yonedaEquiv θ) = yonedaEquiv (yoneda.map f ≫ θ) :=
  yonedaEquiv_naturality θ f

/-- `ALGD-C1-YONEDA-11` (定理 11, p.8).
The bijection `φ_{a,P}` of 定理 1 is natural in `P`: for `σ : P ⇒ Q` and
`θ : y(a) ⇒ P`, `σ_a (φ_{a,P} θ) = φ_{a,Q} (σ ∘ θ)`. -/
theorem yonedaEquiv_natural_in_presheaf (a : C) {P Q : Cᵒᵖ ⥤ Type v} (σ : P ⟶ Q)
    (θ : yoneda.obj a ⟶ P) :
    σ.app (op a) (yonedaEquiv θ) = yonedaEquiv (θ ≫ σ) :=
  (yonedaEquiv_comp θ σ).symm

/-! ## Axiom audit

Each verified declaration must depend only on Lean's standard axioms. The expected
output is pinned with `#guard_msgs`, so `lake build` fails if it changes. -/

/-- info: 'ProjectEpisteme.AlgD.Yoneda.yoneda_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms yoneda_bijective

/-- info: 'ProjectEpisteme.AlgD.Yoneda.yoneda_map_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms yoneda_map_bijective

/-- info: 'ProjectEpisteme.AlgD.Yoneda.isIso_iff_isIso_yonedaEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isIso_iff_isIso_yonedaEquiv

/-- info: 'ProjectEpisteme.AlgD.Yoneda.nonempty_iso_of_yoneda_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_iso_of_yoneda_iso

/-- info: 'ProjectEpisteme.AlgD.Yoneda.nonempty_iso_of_natural_equiv_hom_to' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_iso_of_natural_equiv_hom_to

/-- info: 'ProjectEpisteme.AlgD.Yoneda.nonempty_iso_of_natural_equiv_hom_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_iso_of_natural_equiv_hom_from

/-- info: 'ProjectEpisteme.AlgD.Yoneda.yonedaEquiv_symm_natural_iff_natural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms yonedaEquiv_symm_natural_iff_natural

/-- info: 'ProjectEpisteme.AlgD.Yoneda.nonempty_iso_of_yoneda_comp_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_iso_of_yoneda_comp_iso

/-- info: 'ProjectEpisteme.AlgD.Yoneda.yonedaEquiv_natural_in_object' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms yonedaEquiv_natural_in_object

/-- info: 'ProjectEpisteme.AlgD.Yoneda.yonedaEquiv_natural_in_presheaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms yonedaEquiv_natural_in_presheaf

end ProjectEpisteme.AlgD.Yoneda

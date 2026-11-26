module

public import Mathlib.CategoryTheory.IsoCat
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# alg-d, Chapter 1: 極限 (Limits)

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 1, `limit.pdf`
(<https://alg-d.com/math/kan_extension/limit.pdf>), printed date 2026-06-27,
SHA-256 `ee08a3577452cbb06886c7b0c513844a18cc5ba7af517ee5ee2b93bd87c5cca2`,
retrieved 2026-11-26. Ledger: `docs/ledger/algd/C1-LIMIT.md`.

## Conventions

* The source composes as `g ∘ f`; mathlib writes `f ≫ g`.
* §1 defines the categories `P_ab`, `Q_fg` and `R_fg` of triples and pairs directly. They are
  `CoproductTriple a b`, `PushoutTriple f g` and `CoequalizerPair f g` below. "Is a coproduct",
  "is a pushout" and "is a coequalizer" are mathlib's `IsColimit` for `BinaryCofan`,
  `PushoutCocone` and `Cofork`.
* `T ↓ ∆` for `T : 1 → C^J` and the diagonal `∆ : C → C^J` is mathlib's
  `StructuredArrow T (Functor.const J)`. The source's `≅` between categories is an isomorphism
  of categories, stated with `Functor.IsIso`.
-/

@[expose] public section

namespace ProjectEpisteme.AlgD.Limit

open CategoryTheory Limits

universe w v u

variable {C : Type u} [Category.{v} C]

/-! ## §1 Coproducts, pushouts and coequalizers as initial objects -/

/-- `ALGD-C1-LIMIT-D01` (§1.1, p.2).
For objects `a, b`, the category `P_ab`: an object is a triple `⟨u, p₀ : a → u, p₁ : b → u⟩`,
and a morphism `⟨u, p₀, p₁⟩ → ⟨v, q₀, q₁⟩` is `h : u → v` with `h ∘ p₀ = q₀` and
`h ∘ p₁ = q₁`. -/
structure CoproductTriple (a b : C) where
  /-- The vertex `u`. -/
  u : C
  /-- The map `p₀ : a → u`. -/
  p₀ : a ⟶ u
  /-- The map `p₁ : b → u`. -/
  p₁ : b ⟶ u

namespace CoproductTriple

variable {a b : C}

/-- A morphism of `P_ab`. -/
@[ext]
structure Hom (X Y : CoproductTriple a b) where
  /-- The underlying morphism `h : u → v`. -/
  h : X.u ⟶ Y.u
  w₀ : X.p₀ ≫ h = Y.p₀ := by cat_disch
  w₁ : X.p₁ ≫ h = Y.p₁ := by cat_disch

attribute [reassoc (attr := simp)] Hom.w₀ Hom.w₁

instance : Category (CoproductTriple a b) where
  Hom := Hom
  id X := { h := 𝟙 X.u }
  comp f g := { h := f.h ≫ g.h }

@[ext]
lemma hom_ext {X Y : CoproductTriple a b} {f g : X ⟶ Y} (e : f.h = g.h) : f = g :=
  Hom.ext e

@[simp] lemma id_h (X : CoproductTriple a b) : (𝟙 X : X ⟶ X).h = 𝟙 X.u := rfl

@[simp] lemma comp_h {X Y Z : CoproductTriple a b} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).h = f.h ≫ g.h := rfl

/-- An object of `P_ab` is initial if and only if it has the unique-factorization property. -/
theorem isInitial_iff (X : CoproductTriple a b) :
    Nonempty (IsInitial X) ↔
      ∀ Y : CoproductTriple a b, ∃! h : X.u ⟶ Y.u, X.p₀ ≫ h = Y.p₀ ∧ X.p₁ ≫ h = Y.p₁ := by
  constructor
  · rintro ⟨t⟩ Y
    refine ⟨(t.to Y).h, ⟨(t.to Y).w₀, (t.to Y).w₁⟩, fun h' ⟨w₀, w₁⟩ ↦ ?_⟩
    exact congrArg Hom.h (t.hom_ext (⟨h', w₀, w₁⟩ : X ⟶ Y) (t.to Y))
  · intro H
    choose h hw huniq using H
    exact ⟨IsInitial.ofUniqueHom (fun Y ↦ ⟨h Y, (hw Y).1, (hw Y).2⟩)
      fun Y m ↦ hom_ext (huniq Y m.h ⟨m.w₀, m.w₁⟩)⟩

end CoproductTriple

/-- `BinaryCofan.mk p₀ p₁` is a colimit if and only if every pair `q₀ : a → v`, `q₁ : b → v`
factors uniquely through it. -/
theorem binaryCofan_isColimit_iff {a b u : C} (p₀ : a ⟶ u) (p₁ : b ⟶ u) :
    Nonempty (IsColimit (BinaryCofan.mk p₀ p₁)) ↔
      ∀ (v : C) (q₀ : a ⟶ v) (q₁ : b ⟶ v), ∃! h : u ⟶ v, p₀ ≫ h = q₀ ∧ p₁ ≫ h = q₁ := by
  constructor
  · rintro ⟨t⟩ v q₀ q₁
    refine ⟨t.desc (BinaryCofan.mk q₀ q₁), ⟨t.fac _ ⟨.left⟩, t.fac _ ⟨.right⟩⟩, ?_⟩
    rintro h ⟨w₀, w₁⟩
    exact BinaryCofan.IsColimit.hom_ext t
      (w₀.trans (t.fac (BinaryCofan.mk q₀ q₁) ⟨.left⟩).symm)
      (w₁.trans (t.fac (BinaryCofan.mk q₀ q₁) ⟨.right⟩).symm)
  · intro H
    choose h hw huniq using H
    exact ⟨BinaryCofan.IsColimit.mk _ (fun q₀ q₁ ↦ h _ q₀ q₁) (fun q₀ q₁ ↦ (hw _ q₀ q₁).1)
      (fun q₀ q₁ ↦ (hw _ q₀ q₁).2) fun q₀ q₁ m w₀ w₁ ↦ huniq _ q₀ q₁ m ⟨w₀, w₁⟩⟩

/-- `ALGD-C1-LIMIT-01` (命題 1, p.2).
`a →p₀ u ←p₁ b` is a coproduct of `a` and `b` if and only if `⟨u, p₀, p₁⟩` is an initial object
of `P_ab`. -/
theorem coproduct_iff_isInitial {a b u : C} (p₀ : a ⟶ u) (p₁ : b ⟶ u) :
    Nonempty (IsColimit (BinaryCofan.mk p₀ p₁)) ↔
      Nonempty (IsInitial (⟨u, p₀, p₁⟩ : CoproductTriple a b)) := by
  rw [binaryCofan_isColimit_iff, CoproductTriple.isInitial_iff]
  exact ⟨fun H Y ↦ H Y.u Y.p₀ Y.p₁, fun H v q₀ q₁ ↦ H ⟨v, q₀, q₁⟩⟩

/-- `ALGD-C1-LIMIT-D02` (§1.2, pp.2–3).
For a span `a ←f c →g b`, the category `Q_fg`: an object is a triple `⟨u, p₀, p₁⟩` with
`p₀ ∘ f = p₁ ∘ g`, and a morphism is `h : u → v` with `h ∘ p₀ = q₀` and `h ∘ p₁ = q₁`. -/
structure PushoutTriple {a b c : C} (f : c ⟶ a) (g : c ⟶ b) where
  /-- The vertex `u`. -/
  u : C
  /-- The map `p₀ : a → u`. -/
  p₀ : a ⟶ u
  /-- The map `p₁ : b → u`. -/
  p₁ : b ⟶ u
  /-- The square (2) commutes: `p₀ ∘ f = p₁ ∘ g`. -/
  w : f ≫ p₀ = g ≫ p₁

namespace PushoutTriple

variable {a b c : C} {f : c ⟶ a} {g : c ⟶ b}

/-- A morphism of `Q_fg`. -/
@[ext]
structure Hom (X Y : PushoutTriple f g) where
  /-- The underlying morphism `h : u → v`. -/
  h : X.u ⟶ Y.u
  w₀ : X.p₀ ≫ h = Y.p₀ := by cat_disch
  w₁ : X.p₁ ≫ h = Y.p₁ := by cat_disch

attribute [reassoc (attr := simp)] Hom.w₀ Hom.w₁

instance : Category (PushoutTriple f g) where
  Hom := Hom
  id X := { h := 𝟙 X.u }
  comp f g := { h := f.h ≫ g.h }

@[ext]
lemma hom_ext {X Y : PushoutTriple f g} {φ ψ : X ⟶ Y} (e : φ.h = ψ.h) : φ = ψ :=
  Hom.ext e

@[simp] lemma id_h (X : PushoutTriple f g) : (𝟙 X : X ⟶ X).h = 𝟙 X.u := rfl

@[simp] lemma comp_h {X Y Z : PushoutTriple f g} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).h = φ.h ≫ ψ.h := rfl

/-- An object of `Q_fg` is initial if and only if it has the unique-factorization property. -/
theorem isInitial_iff (X : PushoutTriple f g) :
    Nonempty (IsInitial X) ↔
      ∀ Y : PushoutTriple f g, ∃! h : X.u ⟶ Y.u, X.p₀ ≫ h = Y.p₀ ∧ X.p₁ ≫ h = Y.p₁ := by
  constructor
  · rintro ⟨t⟩ Y
    refine ⟨(t.to Y).h, ⟨(t.to Y).w₀, (t.to Y).w₁⟩, fun h' ⟨w₀, w₁⟩ ↦ ?_⟩
    exact congrArg Hom.h (t.hom_ext (⟨h', w₀, w₁⟩ : X ⟶ Y) (t.to Y))
  · intro H
    choose h hw huniq using H
    exact ⟨IsInitial.ofUniqueHom (fun Y ↦ ⟨h Y, (hw Y).1, (hw Y).2⟩)
      fun Y m ↦ hom_ext (huniq Y m.h ⟨m.w₀, m.w₁⟩)⟩

end PushoutTriple

/-- `PushoutCocone.mk p₀ p₁ w` is a colimit if and only if every commuting pair factors
uniquely through it. -/
theorem pushoutCocone_isColimit_iff {a b c u : C} {f : c ⟶ a} {g : c ⟶ b} (p₀ : a ⟶ u)
    (p₁ : b ⟶ u) (w : f ≫ p₀ = g ≫ p₁) :
    Nonempty (IsColimit (PushoutCocone.mk p₀ p₁ w)) ↔
      ∀ (v : C) (q₀ : a ⟶ v) (q₁ : b ⟶ v), f ≫ q₀ = g ≫ q₁ →
        ∃! h : u ⟶ v, p₀ ≫ h = q₀ ∧ p₁ ≫ h = q₁ := by
  constructor
  · rintro ⟨t⟩ v q₀ q₁ wq
    refine ⟨PushoutCocone.IsColimit.desc t q₀ q₁ wq,
      ⟨PushoutCocone.IsColimit.inl_desc t _ _ wq, PushoutCocone.IsColimit.inr_desc t _ _ wq⟩, ?_⟩
    rintro h ⟨w₀, w₁⟩
    exact PushoutCocone.IsColimit.hom_ext t
      (w₀.trans (PushoutCocone.IsColimit.inl_desc t q₀ q₁ wq).symm)
      (w₁.trans (PushoutCocone.IsColimit.inr_desc t q₀ q₁ wq).symm)
  · intro H
    choose h hw huniq using H
    exact ⟨PushoutCocone.IsColimit.mk _ (fun s ↦ h _ s.inl s.inr s.condition)
      (fun s ↦ (hw _ _ _ s.condition).1) (fun s ↦ (hw _ _ _ s.condition).2)
      fun s m w₀ w₁ ↦ huniq _ _ _ s.condition m ⟨w₀, w₁⟩⟩

/-- `ALGD-C1-LIMIT-03` (命題 3, p.3).
`a →p₀ u ←p₁ b` is a pushout of `a ←f c →g b` if and only if `⟨u, p₀, p₁⟩` is an initial
object of `Q_fg`. -/
theorem pushout_iff_isInitial {a b c u : C} {f : c ⟶ a} {g : c ⟶ b} (p₀ : a ⟶ u)
    (p₁ : b ⟶ u) (w : f ≫ p₀ = g ≫ p₁) :
    Nonempty (IsColimit (PushoutCocone.mk p₀ p₁ w)) ↔
      Nonempty (IsInitial (⟨u, p₀, p₁, w⟩ : PushoutTriple f g)) := by
  rw [pushoutCocone_isColimit_iff, PushoutTriple.isInitial_iff]
  exact ⟨fun H Y ↦ H Y.u Y.p₀ Y.p₁ Y.w, fun H v q₀ q₁ wq ↦ H ⟨v, q₀, q₁, wq⟩⟩

/-- `ALGD-C1-LIMIT-D03` (§1.3, p.3).
For `f, g : a → b`, the category `R_fg`: an object is a pair `⟨u, p : b → u⟩` with
`p ∘ f = p ∘ g`, and a morphism `⟨u, p⟩ → ⟨v, q⟩` is `h : u → v` with `h ∘ p = q`. -/
structure CoequalizerPair {a b : C} (f g : a ⟶ b) where
  /-- The vertex `u`. -/
  u : C
  /-- The map `p : b → u`. -/
  p : b ⟶ u
  /-- `p ∘ f = p ∘ g`. -/
  w : f ≫ p = g ≫ p

namespace CoequalizerPair

variable {a b : C} {f g : a ⟶ b}

/-- A morphism of `R_fg`. -/
@[ext]
structure Hom (X Y : CoequalizerPair f g) where
  /-- The underlying morphism `h : u → v`. -/
  h : X.u ⟶ Y.u
  w : X.p ≫ h = Y.p := by cat_disch

attribute [reassoc (attr := simp)] Hom.w

instance : Category (CoequalizerPair f g) where
  Hom := Hom
  id X := { h := 𝟙 X.u }
  comp φ ψ := { h := φ.h ≫ ψ.h }

@[ext]
lemma hom_ext {X Y : CoequalizerPair f g} {φ ψ : X ⟶ Y} (e : φ.h = ψ.h) : φ = ψ :=
  Hom.ext e

@[simp] lemma id_h (X : CoequalizerPair f g) : (𝟙 X : X ⟶ X).h = 𝟙 X.u := rfl

@[simp] lemma comp_h {X Y Z : CoequalizerPair f g} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).h = φ.h ≫ ψ.h := rfl

/-- An object of `R_fg` is initial if and only if it has the unique-factorization property. -/
theorem isInitial_iff (X : CoequalizerPair f g) :
    Nonempty (IsInitial X) ↔ ∀ Y : CoequalizerPair f g, ∃! h : X.u ⟶ Y.u, X.p ≫ h = Y.p := by
  constructor
  · rintro ⟨t⟩ Y
    refine ⟨(t.to Y).h, (t.to Y).w, fun h' w ↦ ?_⟩
    exact congrArg Hom.h (t.hom_ext (⟨h', w⟩ : X ⟶ Y) (t.to Y))
  · intro H
    choose h hw huniq using H
    exact ⟨IsInitial.ofUniqueHom (fun Y ↦ ⟨h Y, hw Y⟩) fun Y m ↦ hom_ext (huniq Y m.h m.w)⟩

end CoequalizerPair

/-- `Cofork.ofπ p w` is a colimit if and only if every `q : b → v` with `q ∘ f = q ∘ g`
factors uniquely through it. -/
theorem cofork_isColimit_iff {a b u : C} {f g : a ⟶ b} (p : b ⟶ u) (w : f ≫ p = g ≫ p) :
    Nonempty (IsColimit (Cofork.ofπ p w)) ↔
      ∀ (v : C) (q : b ⟶ v), f ≫ q = g ≫ q → ∃! h : u ⟶ v, p ≫ h = q := by
  constructor
  · rintro ⟨t⟩ v q wq
    refine ⟨Cofork.IsColimit.desc t q wq, Cofork.IsColimit.π_desc' t q wq, ?_⟩
    rintro h hh
    exact Cofork.IsColimit.hom_ext t (hh.trans (Cofork.IsColimit.π_desc' t q wq).symm)
  · intro H
    choose h hw huniq using H
    exact ⟨Cofork.IsColimit.mk _ (fun s ↦ h _ s.π s.condition) (fun s ↦ hw _ _ s.condition)
      fun s m hm ↦ huniq _ _ s.condition m hm⟩

/-- `ALGD-C1-LIMIT-04` (命題 4, p.3).
`p : b → u` is a coequalizer of `f, g : a → b` if and only if `⟨u, p⟩` is an initial object of
`R_fg`. -/
theorem coequalizer_iff_isInitial {a b u : C} {f g : a ⟶ b} (p : b ⟶ u) (w : f ≫ p = g ≫ p) :
    Nonempty (IsColimit (Cofork.ofπ p w)) ↔
      Nonempty (IsInitial (⟨u, p, w⟩ : CoequalizerPair f g)) := by
  rw [cofork_isColimit_iff, CoequalizerPair.isInitial_iff]
  exact ⟨fun H Y ↦ H Y.u Y.p Y.w, fun H v q wq ↦ H ⟨v, q, wq⟩⟩

/-! ## §2 The categories of §1 as comma categories `T ↓ ∆` -/

/-- The comparison functor `T ↓ ∆ → Q_fg` for the span `T = (a ←f c →g b)`: an object
`⟨∗, u, θ : T ⇒ ∆u⟩` goes to `⟨u, θ_{j₀}, θ_{j₁}⟩`. -/
@[implicit_reducible]
def spanCommaToPushoutTriple {a b c : C} (f : c ⟶ a) (g : c ⟶ b) :
    StructuredArrow (span f g) (Functor.const WalkingSpan) ⥤ PushoutTriple f g where
  obj X :=
    { u := X.right
      p₀ := X.hom.app WalkingSpan.left
      p₁ := X.hom.app WalkingSpan.right
      w := by
        have h₁ := X.hom.naturality WalkingSpan.Hom.fst
        have h₂ := X.hom.naturality WalkingSpan.Hom.snd
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h₁ h₂
        exact h₁.trans h₂.symm }
  map {X Y} φ :=
    { h := φ.right
      w₀ := by
        have := congr_app (StructuredArrow.w φ) WalkingSpan.left
        simp only [NatTrans.comp_app, Functor.const_map_app] at this
        exact this
      w₁ := by
        have := congr_app (StructuredArrow.w φ) WalkingSpan.right
        simp only [NatTrans.comp_app, Functor.const_map_app] at this
        exact this }

instance isIso_spanCommaToPushoutTriple {a b c : C} (f : c ⟶ a) (g : c ⟶ b) :
    (spanCommaToPushoutTriple f g).IsIso where
  faithful := ⟨fun {_ _} _ _ e ↦ StructuredArrow.hom_ext _ _ (congrArg PushoutTriple.Hom.h e)⟩
  full := ⟨fun {X Y} ψ ↦ ⟨StructuredArrow.homMk ψ.h (by
    ext j
    have hX := X.hom.naturality WalkingSpan.Hom.fst
    have hY := Y.hom.naturality WalkingSpan.Hom.fst
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hX hY
    cases j with
    | none =>
      show X.hom.app WalkingSpan.zero ≫ ψ.h = Y.hom.app WalkingSpan.zero
      rw [← hX, ← hY, Category.assoc]
      exact congrArg _ ψ.w₀
    | some j => cases j; exacts [ψ.w₀, ψ.w₁]), rfl⟩⟩
  bijective_obj := by
    refine ⟨fun X Y e ↦ ?_, fun Y ↦ ⟨StructuredArrow.mk (PushoutCocone.mk Y.p₀ Y.p₁ Y.w).ι, rfl⟩⟩
    obtain ⟨⟨⟨⟩⟩, u, θ⟩ := X
    obtain ⟨⟨⟨⟩⟩, u', θ'⟩ := Y
    simp only [spanCommaToPushoutTriple, PushoutTriple.mk.injEq] at e
    obtain ⟨rfl, e₀, e₁⟩ := e
    have e₀' := eq_of_heq e₀
    have e₁' := eq_of_heq e₁
    have : θ = θ' := by
      ext j
      have h := θ.naturality WalkingSpan.Hom.fst
      have h' := θ'.naturality WalkingSpan.Hom.fst
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h h'
      cases j with
      | none => exact h.symm.trans ((congrArg _ e₀').trans h')
      | some j => cases j; exacts [e₀', e₁']
    subst this
    rfl

/-- `ALGD-C1-LIMIT-05` (命題 5, p.4).
For the span `T = (a ←f c →g b)`, viewed as `T : 1 → C^J` with `J = (j₀ ← i → j₁)`, there is
an isomorphism of categories `T ↓ ∆ ≅ Q_fg`. -/
theorem spanComma_iso_pushoutTriple {a b c : C} (f : c ⟶ a) (g : c ⟶ b) :
    (spanCommaToPushoutTriple f g).IsIso :=
  inferInstance

/-- The comparison functor `T ↓ ∆ → R_fg` for the parallel pair `T = (f, g : a ⇉ b)`. -/
@[implicit_reducible]
def parallelPairCommaToCoequalizerPair {a b : C} (f g : a ⟶ b) :
    StructuredArrow (parallelPair f g) (Functor.const WalkingParallelPair) ⥤
      CoequalizerPair f g where
  obj X :=
    { u := X.right
      p := X.hom.app WalkingParallelPair.one
      w := by
        have h₁ := X.hom.naturality WalkingParallelPairHom.left
        have h₂ := X.hom.naturality WalkingParallelPairHom.right
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h₁ h₂
        exact h₁.trans h₂.symm }
  map {X Y} φ :=
    { h := φ.right
      w := by
        have := congr_app (StructuredArrow.w φ) WalkingParallelPair.one
        simp only [NatTrans.comp_app, Functor.const_map_app] at this
        exact this }

instance isIso_parallelPairCommaToCoequalizerPair {a b : C} (f g : a ⟶ b) :
    (parallelPairCommaToCoequalizerPair f g).IsIso where
  faithful := ⟨fun {_ _} _ _ e ↦
    StructuredArrow.hom_ext _ _ (congrArg CoequalizerPair.Hom.h e)⟩
  full := ⟨fun {X Y} ψ ↦ ⟨StructuredArrow.homMk ψ.h (by
    ext j
    have hX := X.hom.naturality WalkingParallelPairHom.left
    have hY := Y.hom.naturality WalkingParallelPairHom.left
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at hX hY
    cases j
    · show X.hom.app WalkingParallelPair.zero ≫ ψ.h = Y.hom.app WalkingParallelPair.zero
      rw [← hX, ← hY, Category.assoc]
      exact congrArg _ ψ.w
    · exact ψ.w), rfl⟩⟩
  bijective_obj := by
    refine ⟨fun X Y e ↦ ?_, fun Y ↦ ⟨StructuredArrow.mk (Cofork.ofπ Y.p Y.w).ι, rfl⟩⟩
    obtain ⟨⟨⟨⟩⟩, u, θ⟩ := X
    obtain ⟨⟨⟨⟩⟩, u', θ'⟩ := Y
    simp only [parallelPairCommaToCoequalizerPair, CoequalizerPair.mk.injEq] at e
    obtain ⟨rfl, e₁⟩ := e
    have e₁' := eq_of_heq e₁
    have : θ = θ' := by
      ext j
      have h := θ.naturality WalkingParallelPairHom.left
      have h' := θ'.naturality WalkingParallelPairHom.left
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h h'
      cases j
      · exact h.symm.trans ((congrArg _ e₁').trans h')
      · exact e₁'
    subst this
    rfl

/-- `ALGD-C1-LIMIT-07` (命題 7, p.5).
For the parallel pair `T = (f, g : a ⇉ b)`, viewed as `T : 1 → C^J` with `J = (i ⇉ j)`, there
is an isomorphism of categories `T ↓ ∆ ≅ R_fg`. -/
theorem parallelPairComma_iso_coequalizerPair {a b : C} (f g : a ⟶ b) :
    (parallelPairCommaToCoequalizerPair f g).IsIso :=
  inferInstance

/-- The comparison functor `T ↓ ∆ → P_ab` for the pair `T = ⟨a, b⟩` on the two-object discrete
category. -/
@[implicit_reducible]
def pairCommaToCoproductTriple (a b : C) :
    StructuredArrow (pair a b) (Functor.const (Discrete WalkingPair)) ⥤ CoproductTriple a b where
  obj X :=
    { u := X.right
      p₀ := X.hom.app ⟨WalkingPair.left⟩
      p₁ := X.hom.app ⟨WalkingPair.right⟩ }
  map {X Y} φ :=
    { h := φ.right
      w₀ := by
        have := congr_app (StructuredArrow.w φ) ⟨WalkingPair.left⟩
        simp only [NatTrans.comp_app, Functor.const_map_app] at this
        exact this
      w₁ := by
        have := congr_app (StructuredArrow.w φ) ⟨WalkingPair.right⟩
        simp only [NatTrans.comp_app, Functor.const_map_app] at this
        exact this }

instance isIso_pairCommaToCoproductTriple (a b : C) :
    (pairCommaToCoproductTriple a b).IsIso where
  faithful := ⟨fun {_ _} _ _ e ↦
    StructuredArrow.hom_ext _ _ (congrArg CoproductTriple.Hom.h e)⟩
  full := ⟨fun {X Y} ψ ↦ ⟨StructuredArrow.homMk ψ.h (by
    ext ⟨j⟩
    cases j
    · exact ψ.w₀
    · exact ψ.w₁), rfl⟩⟩
  bijective_obj := by
    refine ⟨fun X Y e ↦ ?_, fun Y ↦ ⟨StructuredArrow.mk (BinaryCofan.mk Y.p₀ Y.p₁).ι, rfl⟩⟩
    obtain ⟨⟨⟨⟩⟩, u, θ⟩ := X
    obtain ⟨⟨⟨⟩⟩, u', θ'⟩ := Y
    simp only [pairCommaToCoproductTriple, CoproductTriple.mk.injEq] at e
    obtain ⟨rfl, e₀, e₁⟩ := e
    have : θ = θ' := by
      ext ⟨j⟩
      cases j
      · exact eq_of_heq e₀
      · exact eq_of_heq e₁
    subst this
    rfl

/-- `ALGD-C1-LIMIT-08` (命題 8, p.6).
For the discrete category `J` with two objects and the pair `T = ⟨a, b⟩` viewed as
`T : 1 → C^J`, there is an isomorphism of categories `T ↓ ∆ ≅ P_ab`. -/
theorem pairComma_iso_coproductTriple (a b : C) : (pairCommaToCoproductTriple a b).IsIso :=
  inferInstance

/-! ## §3 Limits and colimits in general -/

/-- `ALGD-C1-LIMIT-D07` (定義 (普遍射), p.6).
For `G : D → C` and `c ∈ C`, a universal arrow from `c` to `G` is an initial object `⟨d, f⟩` of
`c ↓ G`: for every `d'` and `f' : c → G d'` there is a unique `h : d → d'` with `G h ∘ f = f'`.
Dually, a universal arrow from `G` to `c` is a terminal object `⟨d, f : G d → c⟩` of `G ↓ c`. -/
theorem universalArrow_iff {D : Type*} [Category D] (G : D ⥤ C) (c : C) (d : D) :
    (∀ f : c ⟶ G.obj d, Nonempty (IsInitial (StructuredArrow.mk f : StructuredArrow c G)) ↔
      ∀ (d' : D) (f' : c ⟶ G.obj d'), ∃! h : d ⟶ d', f ≫ G.map h = f') ∧
    ∀ f : G.obj d ⟶ c, Nonempty (IsTerminal (CostructuredArrow.mk f : CostructuredArrow G c)) ↔
      ∀ (d' : D) (f' : G.obj d' ⟶ c), ∃! h : d' ⟶ d, G.map h ≫ f = f' := by
  refine ⟨fun f ↦ ⟨?_, ?_⟩, fun f ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨t⟩ d' f'
    refine ⟨(t.to (StructuredArrow.mk f')).right, StructuredArrow.w (t.to (StructuredArrow.mk f')),
      fun h hh ↦ ?_⟩
    exact congrArg CommaMorphism.right
      (t.hom_ext (StructuredArrow.homMk h hh : StructuredArrow.mk f ⟶ StructuredArrow.mk f') _)
  · intro H
    choose h hw huniq using H
    exact ⟨IsInitial.ofUniqueHom (fun Y ↦ StructuredArrow.homMk (h Y.right Y.hom) (hw _ _))
      fun Y m ↦ StructuredArrow.hom_ext _ _ (huniq _ _ m.right (StructuredArrow.w m))⟩
  · rintro ⟨t⟩ d' f'
    refine ⟨(t.from (CostructuredArrow.mk f')).left,
      CostructuredArrow.w (t.from (CostructuredArrow.mk f')), fun h hh ↦ ?_⟩
    exact congrArg CommaMorphism.left
      (t.hom_ext (CostructuredArrow.homMk h hh : CostructuredArrow.mk f' ⟶ CostructuredArrow.mk f)
        _)
  · intro H
    choose h hw huniq using H
    exact ⟨IsTerminal.ofUniqueHom (fun Y ↦ CostructuredArrow.homMk (h Y.left Y.hom) (hw _ _))
      fun Y m ↦ CostructuredArrow.hom_ext _ _ (huniq _ _ m.left (CostructuredArrow.w m))⟩

/-- `ALGD-C1-LIMIT-D08` (定義 (図式・極限・余極限), p.7).
For a diagram `T : J → C`, a limit of `T` is a terminal object of `∆ ↓ T` and a colimit is an
initial object of `T ↓ ∆`. mathlib defines (co)limits by `IsLimit`/`IsColimit` of (co)cones;
this states that the two definitions agree, through mathlib's identifications of cones with
`∆ ↓ T` and cocones with `T ↓ ∆`. -/
theorem limit_iff_terminal_colimit_iff_initial {J : Type*} [Category J] (T : J ⥤ C) :
    (∀ c : Cone T, Nonempty (IsLimit c) ↔
      Nonempty (IsTerminal ((Cone.equivCostructuredArrow T).functor.obj c))) ∧
    ∀ c : Cocone T, Nonempty (IsColimit c) ↔
      Nonempty (IsInitial ((Cocone.equivStructuredArrow T).functor.obj c)) := by
  refine ⟨fun c ↦ ?_, fun c ↦ ?_⟩
  · refine ⟨fun ⟨h⟩ ↦ ⟨IsTerminal.isTerminalObj _ _ (Cone.isLimitEquivIsTerminal c h)⟩,
      fun ⟨h⟩ ↦ ⟨(Cone.isLimitEquivIsTerminal c).symm (IsTerminal.isTerminalOfObj _ _ h)⟩⟩
  · refine ⟨fun ⟨h⟩ ↦ ⟨IsInitial.isInitialObj _ _ (Cocone.isColimitEquivIsInitial c h)⟩,
      fun ⟨h⟩ ↦ ⟨(Cocone.isColimitEquivIsInitial c).symm (IsInitial.isInitialOfObj _ _ h)⟩⟩

/-- `ALGD-C1-LIMIT-09` (例 9, pp.7–8).
For a family `a : ι → C`, viewed as a diagram on the discrete category, a cone is a family
`θ_j : c → a_j`, and a cone `π` is a limit exactly when every such family factors uniquely as
`π_j ∘ h = θ_j`: the limit is the product `∏ a_j` with its projections. -/
theorem fan_isLimit_iff {ι : Type w} (a : ι → C) (t : Fan a) :
    Nonempty (IsLimit t) ↔ ∀ (c : C) (θ : ∀ j, c ⟶ a j), ∃! h : c ⟶ t.pt, ∀ j, h ≫ t.proj j = θ j := by
  constructor
  · rintro ⟨ht⟩ c θ
    refine ⟨ht.lift (Fan.mk c θ), fun j ↦ ht.fac (Fan.mk c θ) ⟨j⟩, fun h hh ↦ ?_⟩
    exact Fan.IsLimit.hom_ext ht _ _ fun j ↦ (hh j).trans (ht.fac (Fan.mk c θ) ⟨j⟩).symm
  · intro H
    choose h hw huniq using H
    exact ⟨Fan.IsLimit.mk t (fun s ↦ h s.pt s.proj) (fun s j ↦ hw s.pt s.proj j)
      fun s m hm ↦ huniq s.pt s.proj m hm⟩

/-- `ALGD-C1-LIMIT-10` (例 10, pp.8–9).
A decreasing sequence `x₀ ≥ x₁ ≥ ⋯` of reals is a diagram `ℕ^op → ℝ` in the preorder category
`ℝ`. If it is bounded below, its limit is `inf_n x_n`. The source omits the boundedness
hypothesis; without it the infimum does not exist in `ℝ`. -/
theorem decreasing_sequence_limit (x : ℕ → ℝ) (hx : Antitone x) (hb : BddBelow (Set.range x)) :
    ∃ c : Cone (Functor.ofOpSequence fun n ↦ homOfLE (hx (Nat.le_succ n))),
      c.pt = ⨅ n, x n ∧ Nonempty (IsLimit c) := by
  let F := Functor.ofOpSequence fun n ↦ homOfLE (hx (Nat.le_succ n))
  have hrange : Set.range F.obj = Set.range x := by
    ext y
    exact ⟨fun ⟨n, hn⟩ ↦ ⟨n.unop, hn⟩, fun ⟨n, hn⟩ ↦ ⟨Opposite.op n, hn⟩⟩
  let c : Cone F :=
    { pt := ⨅ n, x n
      π := { app := fun n ↦ homOfLE (ciInf_le hb n.unop) } }
  exact ⟨c, rfl, ⟨Preorder.isLimitOfIsGLB F c (hrange ▸ isGLB_ciInf hb)⟩⟩

/-- `ALGD-C1-LIMIT-D10` (定義 (有限・小・完備 等), pp.10–11).
"Small" means small relative to the hom universe `v` of `C`, so `C` is complete when it has
limits of all `J` with `SmallCategory J` and `J : Type v`, and cocomplete dually. Finitely
complete and cocomplete quantify over finite categories (`FinCategory`), and products and
coproducts are limits and colimits over discrete categories. -/
theorem completeness_definitions :
    (HasLimits C ↔ ∀ (J : Type v) [SmallCategory J], HasLimitsOfShape J C) ∧
      (HasColimits C ↔ ∀ (J : Type v) [SmallCategory J], HasColimitsOfShape J C) ∧
      (HasFiniteLimits C ↔ ∀ (J : Type) [SmallCategory J] [FinCategory J],
        HasLimitsOfShape J C) ∧
      (HasFiniteColimits C ↔ ∀ (J : Type) [SmallCategory J] [FinCategory J],
        HasColimitsOfShape J C) ∧
      (HasProducts.{v} C ↔ ∀ J : Type v, HasLimitsOfShape (Discrete J) C) ∧
      (HasCoproducts.{v} C ↔ ∀ J : Type v, HasColimitsOfShape (Discrete J) C) :=
  ⟨⟨fun h ↦ h.has_limits_of_shape, fun h ↦ ⟨h⟩⟩, ⟨fun h ↦ h.has_colimits_of_shape, fun h ↦ ⟨h⟩⟩,
    ⟨fun h ↦ h.out, fun h ↦ ⟨h⟩⟩, ⟨fun h ↦ h.out, fun h ↦ ⟨h⟩⟩, Iff.rfl, Iff.rfl⟩

/-- The cone of 命題 12: its vertex is `Hom_{Set^J}(∆1, T)` and `π_j(β) = β_j(∗)`. -/
def unitHomCone {J : Type v} [SmallCategory J] (T : J ⥤ Type v) : Cone T where
  pt := (Functor.const J).obj PUnit.{v + 1} ⟶ T
  π :=
    { app := fun j ↦ ↾fun β ↦ β.app j PUnit.unit
      naturality := fun j j' f ↦ by
        ext β
        exact NatTrans.naturality_apply β f PUnit.unit }

/-- `ALGD-C1-LIMIT-12` (命題 12, pp.11–12).
For a small category `J` and `T : J → Set`, a limit of `T` exists: it is
`Hom_{Set^J}(∆1, T)` with `π_j(β) = β_j(∗)`. Hence `Set` is complete. -/
theorem types_limit {J : Type v} [SmallCategory J] (T : J ⥤ Type v) :
    HasLimitsOfSize.{v, v} (Type v) ∧
      (∀ (j : J) (β : (Functor.const J).obj PUnit.{v + 1} ⟶ T),
        (unitHomCone T).π.app j β = β.app j PUnit.unit) ∧
      Nonempty (IsLimit (unitHomCone T)) := by
  refine ⟨inferInstance, fun _ _ ↦ rfl, ?_⟩
  rw [Types.isLimit_iff]
  intro s hs
  refine ⟨{ app := fun j ↦ ↾fun _ ↦ s j
            naturality := fun j j' f ↦ by ext; simpa using (hs f).symm }, fun j ↦ rfl, ?_⟩
  intro β hβ
  apply NatTrans.ext
  funext j
  ext u
  cases u
  exact hβ j

/-- `ALGD-C1-LIMIT-13` (命題 13, pp.12–13).
`Set` is cocomplete. For small `J` and `T : J → Set`, the quotient `x/∼` of the disjoint union
`x = ∐_j T j` by the equivalence relation generated by `a ∼ (T f)(a)`, with the maps
`η_j : T j → x/∼`, is a colimit of `T`. mathlib's `Functor.ColimitType` is the quotient by
this generating relation. -/
theorem types_colimit {J : Type v} [SmallCategory J] (T : J ⥤ Type v) :
    HasColimitsOfSize.{v, v} (Type v) ∧
      (∀ x y : (j : J) × T.obj j, T.ColimitTypeRel x y ↔ ∃ f : x.1 ⟶ y.1, y.2 = T.map f x.2) ∧
      (∀ (j : J) (a : T.obj j), T.ιColimitType j a = Quot.mk T.ColimitTypeRel ⟨j, a⟩) ∧
      Nonempty (IsColimit (T.coconeTypesEquiv T.coconeTypes)) :=
  ⟨inferInstance, fun _ _ ↦ Iff.rfl, fun _ _ ↦ rfl, ⟨Types.TypeMax.colimitCoconeIsColimit T⟩⟩

/-- `ALGD-C1-LIMIT-15` (定理 15, pp.13–15).
A category with small coproducts and coequalizers is cocomplete. mathlib's proof builds the
colimit as the source does, as a coequalizer of two maps between coproducts
(`colimitCoconeOfCoequalizerAndCoproduct`). -/
theorem cocomplete_of_coproducts_coequalizers [HasCoproducts.{v} C] [HasCoequalizers C] :
    HasColimits C :=
  has_colimits_of_hasCoequalizers_and_coproducts

/-- `ALGD-C1-LIMIT-16` (定理 16, p.15).
A category with small products and equalizers is complete. -/
theorem complete_of_products_equalizers [HasProducts.{v} C] [HasEqualizers C] : HasLimits C :=
  has_limits_of_hasEqualizers_and_products

/-- `ALGD-C1-LIMIT-17` (定理 17, p.15).
A category with finite products and equalizers is finitely complete, and a category with finite
coproducts and coequalizers is finitely cocomplete. -/
theorem finitelyComplete_finitelyCocomplete :
    ([HasFiniteProducts C] → [HasEqualizers C] → HasFiniteLimits C) ∧
      ([HasFiniteCoproducts C] → [HasCoequalizers C] → HasFiniteColimits C) :=
  ⟨@fun _ _ ↦ hasFiniteLimits_of_hasEqualizers_and_finite_products,
    @fun _ _ ↦ hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts⟩

/-! ## §4 Colimits of functors of two variables -/

/-- `ALGD-C1-LIMIT-18` (定理 18, pp.16–17).
Let `T : I × J → C`, and suppose that for each `j` a colimit `⟨colim T(−, j), µ_j⟩` of
`T(−, j) : I → C` is given. Then there is a unique functor `F : J → C` such that
(1) `F(j) = colim T(−, j)`, and (2) for each `i`, the maps `(µ_j)_i : T(i, j) → F(j)` are natural
in `j`. Condition (2) is stated through the equalities of (1) with `eqToHom`. -/
theorem colimit_functor_unique {I : Type*} [Category I] {J : Type*} [Category J] (T : I × J ⥤ C)
    (c : ∀ j, ColimitCocone ((Functor.curry.obj T).flip.obj j)) :
    ∃! F : J ⥤ C, ∃ hF : ∀ j, F.obj j = (c j).cocone.pt,
      ∀ (i : I) {j j' : J} (f : j ⟶ j'),
        (c j).cocone.ι.app i ≫ eqToHom (hF j).symm ≫ F.map f =
          T.map (X := (i, j)) (Y := (i, j')) (𝟙 i, f) ≫ (c j').cocone.ι.app i ≫
            eqToHom (hF j').symm := by
  refine ⟨(combineCocones (Functor.curry.obj T) c).pt, ⟨fun _ ↦ rfl, fun i j j' f ↦ ?_⟩, ?_⟩
  · show (c j).cocone.ι.app i ≫ 𝟙 (c j).cocone.pt ≫ _ =
      T.map (X := (i, j)) (Y := (i, j')) (𝟙 i, f) ≫ (c j').cocone.ι.app i ≫ 𝟙 (c j').cocone.pt
    erw [Category.id_comp, Category.comp_id]
    exact (((combineCocones (Functor.curry.obj T) c).ι.app i).naturality f).symm
  · rintro F ⟨hF, hnat⟩
    have key : ∀ {j j' : J} (f : j ⟶ j'), eqToHom (hF j).symm ≫ F.map f ≫ eqToHom (hF j') =
        (combineCocones (Functor.curry.obj T) c).pt.map f := by
      intro j j' f
      apply (c j).isColimit.hom_ext
      intro i
      rw [reassoc_of% hnat i f]
      simp only [eqToHom_trans, eqToHom_refl, Category.comp_id]
      exact (((combineCocones (Functor.curry.obj T) c).ι.app i).naturality f)
    have aux : ∀ {X X' Y Y' : C} (h : X = X') (h' : Y = Y') (g : X ⟶ Y),
        g = eqToHom h ≫ (eqToHom h.symm ≫ g ≫ eqToHom h') ≫ eqToHom h'.symm := by
      intros; subst_vars; simp
    refine CategoryTheory.Functor.ext hF fun j j' f ↦ ?_
    calc F.map f = eqToHom (hF j) ≫ (eqToHom (hF j).symm ≫ F.map f ≫ eqToHom (hF j')) ≫
          eqToHom (hF j').symm := aux _ _ _
      _ = _ := by rw [key f]; rfl

/-- `ALGD-C1-LIMIT-20` (定理 20, pp.19–21).
With `T : I × J → C` and colimits `⟨colim_i T(i, j), µ_j⟩` for all `j`, let `F` be the functor of
定理 18 and `T̃ : I → C^J` the curried functor. Then `F`, with `ν : T̃ ⇒ ∆F` given by
`(ν_i)_j = (µ_j)_i`, is a colimit of `T̃` in `C^J`: colimits in `C^J` are computed
pointwise. -/
theorem functorCategory_colimit_pointwise {I : Type*} [Category I] {J : Type*} [Category J]
    (T : I × J ⥤ C) (c : ∀ j, ColimitCocone ((Functor.curry.obj T).flip.obj j)) :
    (∀ j, (combineCocones (Functor.curry.obj T) c).pt.obj j = (c j).cocone.pt) ∧
      (∀ i j, ((combineCocones (Functor.curry.obj T) c).ι.app i).app j = (c j).cocone.ι.app i) ∧
      Nonempty (IsColimit (combineCocones (Functor.curry.obj T) c)) :=
  ⟨fun _ ↦ rfl, fun _ _ ↦ rfl, ⟨combinedIsColimit _ c⟩⟩

/-- `ALGD-C1-LIMIT-21` (系 21, p.21).
If `J` is small and `C` is cocomplete, then `C^J` is cocomplete; dually for completeness. -/
theorem functorCategory_cocomplete_complete (J : Type v) [SmallCategory J] :
    (HasColimits C → HasColimits (J ⥤ C)) ∧ (HasLimits C → HasLimits (J ⥤ C)) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

/-- `ALGD-C1-LIMIT-22` (例 22, p.21).
For a small category `D`, the presheaf category `D̂ = Set^{D^op}` is complete and cocomplete. -/
theorem presheaf_complete_cocomplete (D : Type v) [SmallCategory D] :
    HasLimits (Dᵒᵖ ⥤ Type v) ∧ HasColimits (Dᵒᵖ ⥤ Type v) :=
  ⟨inferInstance, inferInstance⟩

/-! ## §5 Representable functors and preservation of limits -/

/-- `ALGD-C1-LIMIT-D12` (定義 (表現可能関手), p.22).
`F : C → Set` is representable iff `F ≅ Hom_C(a, −)` for some `a`; a contravariant
`G : C^op → Set` is representable iff `G ≅ Hom_C(−, a)`. mathlib calls the covariant notion
`IsCorepresentable` and the contravariant one `IsRepresentable`. -/
theorem representable_iff (F : C ⥤ Type v) (G : Cᵒᵖ ⥤ Type v) :
    (F.IsCorepresentable ↔ ∃ a : C, Nonempty (coyoneda.obj (Opposite.op a) ≅ F)) ∧
      (G.IsRepresentable ↔ ∃ a : C, Nonempty (yoneda.obj a ≅ G)) :=
  ⟨⟨fun ⟨⟨a, ⟨e⟩⟩⟩ ↦ ⟨a, ⟨Functor.corepresentableByEquiv e⟩⟩,
      fun ⟨a, ⟨e⟩⟩ ↦ ⟨⟨a, ⟨Functor.corepresentableByEquiv.symm e⟩⟩⟩⟩,
    ⟨fun ⟨⟨a, ⟨e⟩⟩⟩ ↦ ⟨a, ⟨Functor.representableByEquiv e⟩⟩,
      fun ⟨a, ⟨e⟩⟩ ↦ ⟨⟨a, ⟨Functor.representableByEquiv.symm e⟩⟩⟩⟩⟩

/-- `ALGD-C1-LIMIT-24` (命題 24, p.22).
An object representing a functor is unique up to isomorphism. -/
theorem representing_object_unique {F : C ⥤ Type v} {a b : C}
    (e₁ : coyoneda.obj (Opposite.op a) ≅ F) (e₂ : coyoneda.obj (Opposite.op b) ≅ F) :
    Nonempty (a ≅ b) :=
  ⟨Functor.CorepresentableBy.uniqueUpToIso (Functor.corepresentableByEquiv.symm e₁)
    (Functor.corepresentableByEquiv.symm e₂)⟩

/-- `ALGD-C1-LIMIT-25` (定理 25, pp.22–23).
Let `β : Hom_C(a, −) ⇒ F` correspond to `x ∈ F a` under the Yoneda lemma. Then `β` is a
natural isomorphism iff for every `b` and `u ∈ F b` there is a unique `h : a → b` with
`F h(x) = u`. -/
theorem isIso_iff_unique_factorization {F : C ⥤ Type v} {a : C}
    (β : coyoneda.obj (Opposite.op a) ⟶ F) :
    IsIso β ↔ ∀ (b : C) (u : F.obj b), ∃! h : a ⟶ b, F.map h (coyonedaEquiv β) = u := by
  rw [NatTrans.isIso_iff_isIso_app]
  refine forall_congr' fun b ↦ ?_
  rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
  simp only [map_coyonedaEquiv]

/-- The contravariant form of 定理 25, through `yonedaEquiv`. -/
theorem isIso_iff_unique_factorization_op {G : Cᵒᵖ ⥤ Type v} {a : C}
    (β : yoneda.obj a ⟶ G) :
    IsIso β ↔ ∀ (b : C) (u : G.obj (Opposite.op b)), ∃! h : b ⟶ a, G.map h.op (yonedaEquiv β) = u := by
  rw [NatTrans.isIso_iff_isIso_app]
  constructor
  · intro H b
    have := ((isIso_iff_bijective _).1 (H (Opposite.op b)))
    rw [Function.bijective_iff_existsUnique] at this
    simpa only [map_yonedaEquiv] using this
  · intro H b
    rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
    simpa only [map_yonedaEquiv] using H b.unop

/-- A functor `F : C → Set` is representable iff some `x ∈ F a` has the unique-factorization
property of 定理 25. -/
theorem isCorepresentable_iff_exists (F : C ⥤ Type v) :
    F.IsCorepresentable ↔ ∃ (a : C) (x : F.obj a), ∀ (b : C) (u : F.obj b),
      ∃! h : a ⟶ b, F.map h x = u := by
  rw [(representable_iff F (Functor.const _ |>.obj PUnit)).1]
  constructor
  · rintro ⟨a, ⟨e⟩⟩
    exact ⟨a, coyonedaEquiv e.hom, (isIso_iff_unique_factorization e.hom).1 inferInstance⟩
  · rintro ⟨a, x, H⟩
    have : IsIso (coyonedaEquiv.symm x) :=
      (isIso_iff_unique_factorization _).2 (by simpa using H)
    exact ⟨a, ⟨asIso (coyonedaEquiv.symm x)⟩⟩

/-- A presheaf `G : C^op → Set` is representable iff some `x ∈ G a` has the
unique-factorization property. -/
theorem isRepresentable_iff_exists (G : Cᵒᵖ ⥤ Type v) :
    G.IsRepresentable ↔ ∃ (a : C) (x : G.obj (Opposite.op a)), ∀ (b : C)
      (u : G.obj (Opposite.op b)), ∃! h : b ⟶ a, G.map h.op x = u := by
  rw [(representable_iff (Functor.const _ |>.obj PUnit) G).2]
  constructor
  · rintro ⟨a, ⟨e⟩⟩
    exact ⟨a, yonedaEquiv e.hom, (isIso_iff_unique_factorization_op e.hom).1 inferInstance⟩
  · rintro ⟨a, x, H⟩
    have : IsIso (yonedaEquiv.symm x) :=
      (isIso_iff_unique_factorization_op _).2 (by simpa using H)
    exact ⟨a, ⟨asIso (yonedaEquiv.symm x)⟩⟩

/-- `c ↓ G` has an initial object iff some `⟨d, f⟩` is a universal arrow. -/
theorem hasInitial_structuredArrow_iff {D : Type*} [Category D] (G : D ⥤ C) (c : C) :
    HasInitial (StructuredArrow c G) ↔ ∃ (d : D) (f : c ⟶ G.obj d),
      ∀ (d' : D) (f' : c ⟶ G.obj d'), ∃! h : d ⟶ d', f ≫ G.map h = f' := by
  constructor
  · intro _
    let X := ⊥_ (StructuredArrow c G)
    have t : IsInitial (StructuredArrow.mk X.hom) :=
      IsInitial.ofIso initialIsInitial (eqToIso (StructuredArrow.eq_mk X))
    exact ⟨X.right, X.hom, ((universalArrow_iff G c X.right).1 X.hom).1 ⟨t⟩⟩
  · rintro ⟨d, f, H⟩
    obtain ⟨t⟩ := ((universalArrow_iff G c d).1 f).2 H
    exact t.hasInitial

/-- `G ↓ c` has a terminal object iff some `⟨d, f⟩` is a universal arrow from `G` to `c`. -/
theorem hasTerminal_costructuredArrow_iff {D : Type*} [Category D] (G : D ⥤ C) (c : C) :
    HasTerminal (CostructuredArrow G c) ↔ ∃ (d : D) (f : G.obj d ⟶ c),
      ∀ (d' : D) (f' : G.obj d' ⟶ c), ∃! h : d' ⟶ d, G.map h ≫ f = f' := by
  constructor
  · intro _
    let X := ⊤_ (CostructuredArrow G c)
    have t : IsTerminal (CostructuredArrow.mk X.hom) :=
      IsTerminal.ofIso terminalIsTerminal (eqToIso (CostructuredArrow.eq_mk X))
    exact ⟨X.left, X.hom, ((universalArrow_iff G c X.left).2 X.hom).1 ⟨t⟩⟩
  · rintro ⟨d, f, H⟩
    obtain ⟨t⟩ := ((universalArrow_iff G c d).2 f).2 H
    exact t.hasTerminal

/-- `ALGD-C1-LIMIT-R02` (prose after 定理 25, p.23).
The condition of 定理 25 on `x ∈ F a` says exactly that `⟨a, x⟩` is an initial object of
`1 ↓ F`, where `1 : 1 → Set` picks the one-point set; in mathlib `1 ↓ F` is
`StructuredArrow PUnit F`. -/
theorem condition_iff_isInitial {F : C ⥤ Type v} {a : C} (x : F.obj a) :
    (∀ (b : C) (u : F.obj b), ∃! h : a ⟶ b, F.map h x = u) ↔
      Nonempty (IsInitial
        (StructuredArrow.mk (↾fun _ : PUnit.{v + 1} ↦ x) : StructuredArrow PUnit.{v + 1} F)) := by
  rw [((universalArrow_iff F PUnit.{v + 1} a).1 _)]
  constructor
  · intro H b f'
    obtain ⟨h, hh, hu⟩ := H b (f' PUnit.unit)
    refine ⟨h, ?_, fun h' hh' ↦ hu h' ?_⟩
    · ext ⟨⟩
      simpa using hh
    · simpa using ConcreteCategory.congr_hom hh' PUnit.unit
  · intro H b u
    obtain ⟨h, hh, hu⟩ := H b (↾fun _ ↦ u)
    refine ⟨h, ?_, fun h' hh' ↦ hu h' ?_⟩
    · simpa using ConcreteCategory.congr_hom hh PUnit.unit
    · ext ⟨⟩
      simpa using hh'

/-- `ALGD-C1-LIMIT-26` (系 26, p.23).
`F : C → Set` is representable iff `1 ↓ F` has an initial object. -/
theorem representable_iff_hasInitial (F : C ⥤ Type v) :
    F.IsCorepresentable ↔ HasInitial (StructuredArrow PUnit.{v + 1} F) := by
  rw [isCorepresentable_iff_exists, hasInitial_structuredArrow_iff]
  constructor
  · rintro ⟨a, x, H⟩
    exact ⟨a, ↾fun _ ↦ x, ((universalArrow_iff F PUnit.{v + 1} a).1 _).1
      ((condition_iff_isInitial x).1 H)⟩
  · rintro ⟨a, f, H⟩
    refine ⟨a, f PUnit.unit, (condition_iff_isInitial _).2 ?_⟩
    have hf : (↾fun _ : PUnit.{v + 1} ↦ f PUnit.unit) = f := by ext ⟨⟩; rfl
    rw [hf]
    exact ((universalArrow_iff F PUnit.{v + 1} a).1 f).2 H

/-- `ALGD-C1-LIMIT-27` (系 27, pp.23–24).
For `G : D → C` and `c ∈ C`, a universal arrow from `c` to `G` exists iff
`Hom_C(c, G(−)) : D → Set` is representable. -/
theorem universalArrow_exists_iff {D : Type*} [Category.{v} D] (G : D ⥤ C) (c : C) :
    HasInitial (StructuredArrow c G) ↔ (G ⋙ coyoneda.obj (Opposite.op c)).IsCorepresentable := by
  rw [hasInitial_structuredArrow_iff, isCorepresentable_iff_exists]
  exact Iff.rfl

/-- `ALGD-C1-LIMIT-28` (定理 28, p.24).
For `F : D → C` and `c ∈ C`, a universal arrow from `F` to `c` exists iff
`Hom_C(F(−), c) : D^op → Set` is representable. -/
theorem universalArrow_from_exists_iff {D : Type*} [Category.{v} D] (F : D ⥤ C) (c : C) :
    HasTerminal (CostructuredArrow F c) ↔ (F.op ⋙ yoneda.obj c).IsRepresentable := by
  rw [hasTerminal_costructuredArrow_iff, isRepresentable_iff_exists]
  exact Iff.rfl

/-- `ALGD-C1-LIMIT-29` (例 29, p.24).
A product of `a` and `b` is exactly an object representing `Hom_C(−, a) × Hom_C(−, b)`: a fan
`t` is a limit iff `h ↦ (π₀ ∘ h, π₁ ∘ h)` is a bijection `Hom_C(x, t) → Hom_C(x, a) × Hom_C(x, b)`
for every `x`. -/
theorem binaryFan_isLimit_iff_bijective {a b : C} (t : BinaryFan a b) :
    Nonempty (IsLimit t) ↔
      ∀ x : C, Function.Bijective (fun h : x ⟶ t.pt ↦ (h ≫ t.fst, h ≫ t.snd)) := by
  constructor
  · rintro ⟨ht⟩ x
    refine ⟨fun h h' e ↦ BinaryFan.IsLimit.hom_ext ht (congrArg _root_.Prod.fst e)
      (congrArg _root_.Prod.snd e), fun p ↦ ⟨ht.lift (BinaryFan.mk p.1 p.2), ?_⟩⟩
    exact _root_.Prod.ext (ht.fac (BinaryFan.mk p.1 p.2) ⟨.left⟩)
      (ht.fac (BinaryFan.mk p.1 p.2) ⟨.right⟩)
  · intro H
    choose l hl using fun x (p : (x ⟶ a) × (x ⟶ b)) ↦ (H x).2 p
    exact ⟨BinaryFan.IsLimit.mk t (fun f g ↦ l _ (f, g))
      (fun f g ↦ congrArg _root_.Prod.fst (hl _ (f, g)))
      (fun f g ↦ congrArg _root_.Prod.snd (hl _ (f, g)))
      fun f g m h₁ h₂ ↦ (H _).1 (by rw [hl]; exact _root_.Prod.ext h₁ h₂)⟩

/-- `ALGD-C1-LIMIT-D13` (定義 (余極限と交換する), p.24).
For `T : J → C` with colimit `⟨colim T, µ⟩` and `F : C → D`, `F` commutes with `colim T` iff
`⟨F(colim T), Fµ⟩` is a colimit of `F T`. mathlib's `PreservesColimit T F` asks this for every
colimit cocone; by uniqueness of colimits this is the same. -/
theorem commutes_with_colimit_iff {D : Type*} [Category D] {J : Type*} [Category J]
    {T : J ⥤ C} (F : C ⥤ D) {c : Cocone T} (hc : IsColimit c) :
    PreservesColimit T F ↔ Nonempty (IsColimit (F.mapCocone c)) :=
  ⟨fun _ ↦ ⟨isColimitOfPreserves F hc⟩,
    fun ⟨h⟩ ↦ preservesColimit_of_preserves_colimit_cocone hc h⟩

/-- `ALGD-C1-LIMIT-D14` (定義 (余連続), p.25).
`F : C → D` is cocontinuous iff it commutes with every colimit of a small diagram, and
continuous iff it commutes with every limit of a small diagram. "Small" is relative to the hom
universe `v` of `C`. -/
theorem cocontinuous_continuous_iff {D : Type*} [Category D] (F : C ⥤ D) :
    (PreservesColimitsOfSize.{v, v} F ↔
        ∀ (J : Type v) [SmallCategory J] (T : J ⥤ C), PreservesColimit T F) ∧
      (PreservesLimitsOfSize.{v, v} F ↔
        ∀ (J : Type v) [SmallCategory J] (T : J ⥤ C), PreservesLimit T F) :=
  ⟨⟨fun _ _ _ _ ↦ inferInstance, fun h ↦ ⟨fun {J} _ ↦ ⟨fun {T} ↦ h J T⟩⟩⟩,
    ⟨fun _ _ _ _ ↦ inferInstance, fun h ↦ ⟨fun {J} _ ↦ ⟨fun {T} ↦ h J T⟩⟩⟩⟩

/-- `ALGD-C1-LIMIT-30` (命題 30, pp.25–26).
For `c ∈ C`, `Hom_C(c, −)` commutes with every limit: if `⟨lim T, π⟩` is a limit, then
`Hom_C(c, lim T)` with the maps `π_j ∘ −` is a limit of `Hom_C(c, T−)`. -/
theorem coyoneda_preserves_limit (c : C) {J : Type*} [Category J] {T : J ⥤ C} {s : Cone T}
    (hs : IsLimit s) :
    (∀ (j : J) (h : c ⟶ s.pt),
        ((coyoneda.obj (Opposite.op c)).mapCone s).π.app j h = h ≫ s.π.app j) ∧
      Nonempty (IsLimit ((coyoneda.obj (Opposite.op c)).mapCone s)) :=
  ⟨fun _ _ ↦ rfl, ⟨isLimitOfPreserves _ hs⟩⟩

/-- `ALGD-C1-LIMIT-31` (定理 31, p.26).
The Yoneda embedding `y : C → Ĉ` commutes with limits. -/
theorem yoneda_preserves_limits : PreservesLimitsOfSize.{w, w} (yoneda : C ⥤ Cᵒᵖ ⥤ Type v) :=
  inferInstance

/-- `ALGD-C1-LIMIT-32` (命題 32, p.27).
For any category `J` and cocomplete `C`, evaluation `ev_j : C^J → C` commutes with small
colimits. -/
theorem evaluation_preserves_colimits [HasColimits C] {J : Type*} [Category J] (j : J) :
    PreservesColimits ((evaluation J C).obj j) :=
  evaluation_preservesColimits j

/-- `ALGD-C1-LIMIT-R03` (prose after 命題 32, p.27).
If `C` is complete, `ev_j : C^J → C` commutes with small limits. -/
theorem evaluation_preserves_limits [HasLimits C] {J : Type*} [Category J] (j : J) :
    PreservesLimits ((evaluation J C).obj j) :=
  evaluationPreservesLimits j

/-- `ALGD-C1-LIMIT-33` (例 33, pp.27–28).
For `θ : F ⇒ G : C → D` with `D` cocomplete, `θ` is an epimorphism of `D^C` iff every component
is; the converse direction needs no hypothesis. Dually for monomorphisms when `D` is complete.
In particular, a morphism of presheaves is epi iff all its components are surjective, and mono
iff all are injective. -/
theorem epi_mono_iff_app {D : Type*} [Category D] {F G : C ⥤ D} (θ : F ⟶ G) :
    ([HasColimits D] → (Epi θ ↔ ∀ a, Epi (θ.app a))) ∧
      ((∀ a, Epi (θ.app a)) → Epi θ) ∧
      ([HasLimits D] → (Mono θ ↔ ∀ a, Mono (θ.app a))) ∧
      ∀ {P Q : Cᵒᵖ ⥤ Type v} (σ : P ⟶ Q),
        (Epi σ ↔ ∀ a, Function.Surjective (σ.app a)) ∧
          (Mono σ ↔ ∀ a, Function.Injective (σ.app a)) :=
  ⟨@fun _ ↦ NatTrans.epi_iff_epi_app θ, fun h ↦ @NatTrans.epi_of_epi_app _ _ _ _ _ _ θ h,
    @fun _ ↦ NatTrans.mono_iff_mono_app θ,
    fun σ ↦ ⟨by simp only [NatTrans.epi_iff_epi_app, epi_iff_surjective],
      by simp only [NatTrans.mono_iff_mono_app, mono_iff_injective]⟩⟩

/-- `ALGD-C1-LIMIT-R04` (closing prose of §5, p.28).
For `F : C → D` and `T : J → C` such that `T` and `F T` have colimits, there is a canonical
`h : colim F T → F(colim T)` with `h ∘ ν_j = F µ_j`, and `F` commutes with `colim T` iff `h` is an
isomorphism. -/
theorem post_comparison {D : Type*} [Category D] {J : Type*} [Category J] (T : J ⥤ C)
    (F : C ⥤ D) [HasColimit T] [HasColimit (T ⋙ F)] :
    (∀ j, colimit.ι (T ⋙ F) j ≫ colimit.post T F = F.map (colimit.ι T j)) ∧
      (PreservesColimit T F ↔ IsIso (colimit.post T F)) :=
  ⟨colimit.ι_post T F, ⟨fun _ ↦ inferInstance, fun _ ↦ preservesColimit_of_isIso_post (F := T) (G := F)⟩⟩

/-! ## Axiom audit

Each declaration carrying a source ID must depend only on Lean's standard axioms. The
expected output is pinned with `#guard_msgs`, so `lake build` fails if it changes. -/

/-- info: 'ProjectEpisteme.AlgD.Limit.CoequalizerPair' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.CoequalizerPair

/-- info: 'ProjectEpisteme.AlgD.Limit.CoproductTriple' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.CoproductTriple

/-- info: 'ProjectEpisteme.AlgD.Limit.PushoutTriple' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.PushoutTriple

/-- info: 'ProjectEpisteme.AlgD.Limit.binaryFan_isLimit_iff_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.binaryFan_isLimit_iff_bijective

/-- info: 'ProjectEpisteme.AlgD.Limit.cocomplete_of_coproducts_coequalizers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.cocomplete_of_coproducts_coequalizers

/-- info: 'ProjectEpisteme.AlgD.Limit.cocontinuous_continuous_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.cocontinuous_continuous_iff

/-- info: 'ProjectEpisteme.AlgD.Limit.coequalizer_iff_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.coequalizer_iff_isInitial

/-- info: 'ProjectEpisteme.AlgD.Limit.colimit_functor_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.colimit_functor_unique

/-- info: 'ProjectEpisteme.AlgD.Limit.commutes_with_colimit_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.commutes_with_colimit_iff

/-- info: 'ProjectEpisteme.AlgD.Limit.complete_of_products_equalizers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.complete_of_products_equalizers

/-- info: 'ProjectEpisteme.AlgD.Limit.completeness_definitions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.completeness_definitions

/-- info: 'ProjectEpisteme.AlgD.Limit.condition_iff_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.condition_iff_isInitial

/-- info: 'ProjectEpisteme.AlgD.Limit.coproduct_iff_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.coproduct_iff_isInitial

/-- info: 'ProjectEpisteme.AlgD.Limit.coyoneda_preserves_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.coyoneda_preserves_limit

/-- info: 'ProjectEpisteme.AlgD.Limit.decreasing_sequence_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.decreasing_sequence_limit

/-- info: 'ProjectEpisteme.AlgD.Limit.epi_mono_iff_app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.epi_mono_iff_app

/-- info: 'ProjectEpisteme.AlgD.Limit.evaluation_preserves_colimits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.evaluation_preserves_colimits

/-- info: 'ProjectEpisteme.AlgD.Limit.evaluation_preserves_limits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.evaluation_preserves_limits

/-- info: 'ProjectEpisteme.AlgD.Limit.fan_isLimit_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.fan_isLimit_iff

/-- info: 'ProjectEpisteme.AlgD.Limit.finitelyComplete_finitelyCocomplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.finitelyComplete_finitelyCocomplete

/-- info: 'ProjectEpisteme.AlgD.Limit.functorCategory_cocomplete_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.functorCategory_cocomplete_complete

/-- info: 'ProjectEpisteme.AlgD.Limit.functorCategory_colimit_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.functorCategory_colimit_pointwise

/-- info: 'ProjectEpisteme.AlgD.Limit.isIso_iff_unique_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.isIso_iff_unique_factorization

/-- info: 'ProjectEpisteme.AlgD.Limit.limit_iff_terminal_colimit_iff_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.limit_iff_terminal_colimit_iff_initial

/-- info: 'ProjectEpisteme.AlgD.Limit.pairComma_iso_coproductTriple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.pairComma_iso_coproductTriple

/-- info: 'ProjectEpisteme.AlgD.Limit.parallelPairComma_iso_coequalizerPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.parallelPairComma_iso_coequalizerPair

/-- info: 'ProjectEpisteme.AlgD.Limit.post_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.post_comparison

/-- info: 'ProjectEpisteme.AlgD.Limit.presheaf_complete_cocomplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.presheaf_complete_cocomplete

/-- info: 'ProjectEpisteme.AlgD.Limit.pushout_iff_isInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.pushout_iff_isInitial

/-- info: 'ProjectEpisteme.AlgD.Limit.representable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.representable_iff

/-- info: 'ProjectEpisteme.AlgD.Limit.representable_iff_hasInitial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.representable_iff_hasInitial

/-- info: 'ProjectEpisteme.AlgD.Limit.representing_object_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.representing_object_unique

/-- info: 'ProjectEpisteme.AlgD.Limit.spanComma_iso_pushoutTriple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.spanComma_iso_pushoutTriple

/-- info: 'ProjectEpisteme.AlgD.Limit.types_colimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.types_colimit

/-- info: 'ProjectEpisteme.AlgD.Limit.types_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.types_limit

/-- info: 'ProjectEpisteme.AlgD.Limit.universalArrow_exists_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.universalArrow_exists_iff

/-- info: 'ProjectEpisteme.AlgD.Limit.universalArrow_from_exists_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.universalArrow_from_exists_iff

/-- info: 'ProjectEpisteme.AlgD.Limit.universalArrow_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.universalArrow_iff

/-- info: 'ProjectEpisteme.AlgD.Limit.yoneda_preserves_limits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Limit.yoneda_preserves_limits
end ProjectEpisteme.AlgD.Limit

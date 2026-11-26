module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.IsoCat
public import Mathlib.CategoryTheory.PEmpty
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Isomorphisms of functor categories

Library layer of the Category track. Each result here shows that a functor is an isomorphism
of categories (`Functor.IsIso`: full, faithful, and bijective on objects), so that it assembles
into an `IsoCat`. mathlib provides the corresponding equivalences; these strict versions are
needed where a source asserts an isomorphism of categories. All are candidates for upstreaming.

* `Functor.equiv.functor : (Discrete PUnit ⥤ C) ⥤ C` is an isomorphism (`C^1 ≅ C`).
* `Functor.star (Discrete PEmpty ⥤ C)` is an isomorphism (`C^0 ≅ 1`).
* `Discrete.evalPair : (Discrete Bool ⥤ C) ⥤ C × C` is an isomorphism (`C^{a,b} ≅ C × C`).
* `ComposableArrows.toArrow : (Fin 2 ⥤ C) ⥤ Arrow C` is an isomorphism (`C^2` is the arrow
  category).
* `Set.characteristicFunctor X : Set X ⥤ (Discrete X ⥤ Fin 2)` is an isomorphism
  (`P(X) ≅ 2^X`), compatible with preimages.
-/

@[expose] public section

namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C]

namespace Functor

/-- A functor out of `Discrete PUnit` is determined by its value on the unique object. -/
theorem ext_of_discretePUnit {F G : Discrete PUnit.{w + 1} ⥤ C}
    (h : F.obj ⟨⟨⟩⟩ = G.obj ⟨⟨⟩⟩) : F = G := by
  refine CategoryTheory.Functor.ext (fun X ↦ by obtain ⟨⟨⟩⟩ := X; exact h) (fun X Y f ↦ ?_)
  obtain ⟨⟨⟩⟩ := X
  obtain ⟨⟨⟩⟩ := Y
  obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
  simp

/-- Evaluation at the unique object, `(Discrete PUnit ⥤ C) ⥤ C`, is an isomorphism of
categories. -/
instance isIso_equiv_functor :
    (Functor.equiv (C := C) : (Discrete PUnit.{w + 1} ⥤ C) ≌ C).functor.IsIso where
  bijective_obj := ⟨fun _ _ h ↦ ext_of_discretePUnit h, fun c ↦ ⟨(Functor.const _).obj c, rfl⟩⟩

/-- The functor from `Discrete PEmpty ⥤ C` to the one-object category is an isomorphism of
categories. -/
instance isIso_star_discretePEmpty :
    (Functor.star (Discrete PEmpty.{w + 1} ⥤ C) : _ ⥤ Discrete PUnit.{w + 1}).IsIso where
  faithful := ⟨fun {_ _} _ _ _ ↦ by ext X; exact X.as.elim⟩
  full := ⟨fun {_ _} _ ↦ ⟨⟨fun X ↦ X.as.elim, fun X ↦ X.as.elim⟩, Subsingleton.elim _ _⟩⟩
  bijective_obj := ⟨fun F G _ ↦ Functor.empty_ext' F G, fun ⟨⟨⟩⟩ ↦ ⟨Functor.empty C, rfl⟩⟩

end Functor

namespace Discrete

/-- Evaluation at both objects of `Discrete Bool`. -/
def evalPair : (Discrete Bool ⥤ C) ⥤ C × C :=
  ((evaluation _ C).obj ⟨false⟩).prod' ((evaluation _ C).obj ⟨true⟩)

/-- A functor out of `Discrete Bool` is determined by its values on the two objects. -/
theorem functor_ext_bool {F G : Discrete Bool ⥤ C} (h₀ : F.obj ⟨false⟩ = G.obj ⟨false⟩)
    (h₁ : F.obj ⟨true⟩ = G.obj ⟨true⟩) : F = G := by
  refine CategoryTheory.Functor.ext (fun X ↦ by obtain ⟨b⟩ := X; cases b; exacts [h₀, h₁])
    (fun X Y f ↦ ?_)
  obtain ⟨x⟩ := X
  obtain ⟨y⟩ := Y
  obtain rfl : x = y := Discrete.eq_of_hom f
  obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
  simp

instance isIso_evalPair : (evalPair (C := C)).IsIso where
  faithful := ⟨fun {_ _} _ _ h ↦ by
    ext ⟨b⟩
    cases b
    · exact congrArg _root_.Prod.fst h
    · exact congrArg _root_.Prod.snd h⟩
  full := ⟨fun {_ _} p ↦ ⟨Discrete.natTrans fun ⟨b⟩ ↦ by cases b; exacts [p.1, p.2], rfl⟩⟩
  bijective_obj := ⟨fun _ _ h ↦ functor_ext_bool (congrArg _root_.Prod.fst h) (congrArg _root_.Prod.snd h),
    fun p ↦ ⟨Discrete.functor (fun b ↦ Bool.rec p.1 p.2 b), rfl⟩⟩

end Discrete

namespace ComposableArrows

/-- A functor `Fin 2 ⥤ C` gives the arrow `F.obj 0 ⟶ F.obj 1`, and a natural transformation
gives the commutative square of its two components. -/
def toArrow : ComposableArrows C 1 ⥤ Arrow C where
  obj F := Arrow.mk F.hom
  map φ := Arrow.homMk (φ.app 0) (φ.app 1) (φ.naturality _).symm

instance isIso_toArrow : (toArrow (C := C)).IsIso where
  faithful := ⟨fun {_ _} _ _ h ↦ ComposableArrows.hom_ext₁
    (congrArg CommaMorphism.left h) (congrArg CommaMorphism.right h)⟩
  full := ⟨fun {_ _} sq ↦ ⟨ComposableArrows.homMk₁ sq.left sq.right sq.w.symm, rfl⟩⟩
  bijective_obj := (ComposableArrows.arrowEquiv (C := C)).bijective

end ComposableArrows

namespace Set

open Classical in
/-- The characteristic-function functor from subsets of `X`, ordered by inclusion, to functors
`Discrete X ⥤ Fin 2`: a subset `A` goes to `x ↦ 1` on `A` and `x ↦ 0` off `A`. -/
noncomputable def characteristicFunctor (X : Type u) : Set X ⥤ (Discrete X ⥤ Fin 2) where
  obj A := Discrete.functor fun x ↦ if x ∈ A then 1 else 0
  map {A B} h := Discrete.natTrans fun ⟨x⟩ ↦ homOfLE (by
    have := leOfHom h
    by_cases hA : x ∈ A
    · simp [hA, this hA]
    · simp [hA])

theorem characteristicFunctor_obj_eq_one {X : Type u} (A : Set X) (x : X) :
    ((characteristicFunctor X).obj A).obj ⟨x⟩ = 1 ↔ x ∈ A := by
  classical
  by_cases hA : x ∈ A <;> simp [characteristicFunctor, hA]

instance isIso_characteristicFunctor (X : Type u) : (characteristicFunctor X).IsIso where
  faithful := ⟨fun {_ _} _ _ _ ↦ Subsingleton.elim _ _⟩
  full := ⟨fun {A B} θ ↦ ⟨homOfLE fun x hx ↦ by
    have h := leOfHom (θ.app ⟨x⟩)
    rw [← characteristicFunctor_obj_eq_one] at hx ⊢
    rw [hx] at h
    exact le_antisymm (Fin.le_last _) h, by ext; exact Subsingleton.elim _ _⟩⟩
  bijective_obj := by
    refine ⟨fun A B h ↦ Set.ext fun x ↦ ?_, fun F ↦ ⟨{x | F.obj ⟨x⟩ = 1}, ?_⟩⟩
    · rw [← characteristicFunctor_obj_eq_one, ← characteristicFunctor_obj_eq_one, h]
    · refine CategoryTheory.Functor.ext (fun X ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
      obtain ⟨x⟩ := X
      classical
      by_cases hx : F.obj ⟨x⟩ = 1
      · simp [characteristicFunctor, hx]
      · have : F.obj ⟨x⟩ = 0 := by omega
        simp [characteristicFunctor, this]

/-- Precomposition with `f : X → Y`, viewed as a functor of discrete categories, corresponds
under `characteristicFunctor` to taking preimages. -/
theorem characteristicFunctor_comp_precomp {X Y : Type u} (f : X → Y) :
    characteristicFunctor Y ⋙ (Functor.whiskeringLeft (Discrete X) (Discrete Y) (Fin 2)).obj
        (Discrete.functor fun x ↦ ⟨f x⟩) =
      (Monotone.functor (f := Set.preimage f) fun _ _ h ↦ Set.preimage_mono h) ⋙
        characteristicFunctor X := by
  refine CategoryTheory.Functor.ext
    (fun A ↦ CategoryTheory.Functor.ext (fun X ↦ by obtain ⟨x⟩ := X; rfl)
      (fun _ _ _ ↦ Subsingleton.elim _ _))
    (fun _ _ _ ↦ by ext; exact Subsingleton.elim _ _)

end Set

end CategoryTheory

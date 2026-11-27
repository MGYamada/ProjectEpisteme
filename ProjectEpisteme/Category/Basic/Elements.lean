/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.IsoCat

/-!
# The category of elements is isomorphic to `yoneda ↓ P`

Library layer of the Category track. mathlib's equivalence
`Functor.Elements.costructuredArrowYonedaEquivalence : P.Elementsᵒᵖ ≌ CostructuredArrow yoneda P`
has a functor that is bijective on objects, so it is an isomorphism of categories. This is a
candidate for upstreaming.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace Functor.Elements

instance isIso_toCostructuredArrow (P : Cᵒᵖ ⥤ Type v) : (toCostructuredArrow P).IsIso where
  faithful := (costructuredArrowYonedaEquivalence P).faithful_functor
  full := (costructuredArrowYonedaEquivalence P).full_functor
  bijective_obj := by
    refine ⟨fun X Y h ↦ ?_, fun Z ↦
      ⟨Opposite.op ((fromCostructuredArrow P).obj (Opposite.op Z)), ?_⟩⟩
    · obtain ⟨@⟨c, x⟩⟩ := X
      obtain ⟨@⟨c', y⟩⟩ := Y
      have h' := congrArg (fun Z ↦ (fromCostructuredArrow P).obj (Opposite.op Z)) h
      obtain ⟨rfl, h₂⟩ : c = c' ∧ x ≍ y := by simpa using h'
      obtain rfl := eq_of_heq h₂
      rfl
    · simpa using (CostructuredArrow.eq_mk Z).symm

end Functor.Elements

end CategoryTheory

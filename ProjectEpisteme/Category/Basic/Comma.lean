module

public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.EqToHom

/-!
# The functor into a comma category induced by a natural transformation

Library layer of the Category track. For functors `F : C₀ ⥤ D`, `G : C₁ ⥤ D`, `Q₀ : X ⥤ C₀`,
`Q₁ : X ⥤ C₁` and a natural transformation `θ : Q₀ ⋙ F ⟶ Q₁ ⋙ G`, `Comma.liftFunctor` is the
functor `X ⥤ Comma F G` sending `x` to `⟨Q₀ x, Q₁ x, θ x⟩`. It is the functor in the strict
universal property of comma categories. mathlib has the special cases
`Functor.toStructuredArrow` and `Functor.toCostructuredArrow`; this general form is a candidate
for upstreaming.
-/

@[expose] public section

namespace CategoryTheory

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
  {D : Type u₂} [Category.{v₂} D] {X : Type u₃} [Category.{v₃} X]

namespace Comma

/-- The functor `X ⥤ Comma F G` determined by `Q₀`, `Q₁` and `θ : Q₀ ⋙ F ⟶ Q₁ ⋙ G`. -/
@[simps]
def liftFunctor (F : C₀ ⥤ D) (G : C₁ ⥤ D) (Q₀ : X ⥤ C₀) (Q₁ : X ⥤ C₁)
    (θ : Q₀ ⋙ F ⟶ Q₁ ⋙ G) : X ⥤ Comma F G where
  obj x := ⟨Q₀.obj x, Q₁.obj x, θ.app x⟩
  map f := ⟨Q₀.map f, Q₁.map f, θ.naturality f⟩

/-- Whiskering the canonical transformation of `Comma F G` by `liftFunctor` gives back `θ`,
up to the equalities `liftFunctor ⋙ fst = Q₀` and `liftFunctor ⋙ snd = Q₁`. Both hold by
definition, so any proofs of them may be supplied. -/
theorem whiskerLeft_liftFunctor_natTrans (F : C₀ ⥤ D) (G : C₁ ⥤ D) (Q₀ : X ⥤ C₀)
    (Q₁ : X ⥤ C₁) (θ : Q₀ ⋙ F ⟶ Q₁ ⋙ G) (h₀ : liftFunctor F G Q₀ Q₁ θ ⋙ fst F G = Q₀)
    (h₁ : liftFunctor F G Q₀ Q₁ θ ⋙ snd F G = Q₁) :
    Functor.whiskerLeft (liftFunctor F G Q₀ Q₁ θ) (natTrans F G) ≫ eqToHom (congrArg (· ⋙ G) h₁) =
      eqToHom (congrArg (· ⋙ F) h₀) ≫ θ := by
  ext x
  simp only [NatTrans.comp_app, eqToHom_app]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end Comma

end CategoryTheory

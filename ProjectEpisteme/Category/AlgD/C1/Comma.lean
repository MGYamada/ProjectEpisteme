module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ProjectEpisteme.Category.Basic.Comma
public import ProjectEpisteme.Category.Basic.Elements
public import ProjectEpisteme.Category.Basic.FunctorCategory

/-!
# alg-d, Chapter 1: コンマ圏 (Comma categories)

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 1, `comma.pdf`
(<https://alg-d.com/math/kan_extension/comma.pdf>), printed date 2026-08-16,
SHA-256 `bf4af11c17b03c64f2f0bb99066b7e3cb16e0a60cc50d5fc15b089566eb2b2ac`,
retrieved 2026-11-26. Ledger: `docs/ledger/algd/C1-COMMA.md`.

## Conventions

* The source's `F ↓ G` is mathlib's `Comma F G`; its `P₀`, `P₁` and `κ` are `Comma.fst`,
  `Comma.snd` and `Comma.natTrans`. The source composes as `g ∘ f`, mathlib as `f ≫ g`.
* The source writes `≅` for an isomorphism of categories and `=` for an identification of
  categories. Both are stated as isomorphisms of categories: `IsoCat`, or `Functor.IsIso`
  for a named functor.
* `1` is `Discrete PUnit`, and `C^2` is `ComposableArrows C 1 = Fin 2 ⥤ C`, as in
  `ALGD-C1-NAT-12`.
-/

@[expose] public section

namespace ProjectEpisteme.AlgD.CommaCategory

open CategoryTheory Functor

universe w v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
  {D : Type u₂} [Category.{v₂} D]

/-- `ALGD-C1-COMMA-D01` (定義, p.1–2).
In the comma category `F ↓ G` of `F : C₀ → D` and `G : C₁ → D`, an object is a triple
`⟨c₀, c₁, f : F c₀ → G c₁⟩`. A morphism `⟨c₀, c₁, f⟩ → ⟨c₀', c₁', f'⟩` is exactly a pair
`⟨g₀, g₁⟩` with `G g₁ ∘ f = f' ∘ F g₀`, and composition and identities are componentwise. -/
theorem comma_category (F : C₀ ⥤ D) (G : C₁ ⥤ D) :
    (∀ {X Y : Comma F G} (g : X ⟶ Y), X.hom ≫ G.map g.right = F.map g.left ≫ Y.hom) ∧
      (∀ (X Y : Comma F G) (g₀ : X.left ⟶ Y.left) (g₁ : X.right ⟶ Y.right),
        X.hom ≫ G.map g₁ = F.map g₀ ≫ Y.hom → ∃ g : X ⟶ Y, g.left = g₀ ∧ g.right = g₁) ∧
      (∀ {X Y Z : Comma F G} (g : X ⟶ Y) (h : Y ⟶ Z),
        (g ≫ h).left = g.left ≫ h.left ∧ (g ≫ h).right = g.right ≫ h.right) ∧
      ∀ X : Comma F G, (𝟙 X : X ⟶ X).left = 𝟙 X.left ∧ (𝟙 X : X ⟶ X).right = 𝟙 X.right :=
  ⟨fun g ↦ g.w.symm, fun _ _ g₀ g₁ w ↦ ⟨⟨g₀, g₁, w.symm⟩, rfl, rfl⟩,
    fun _ _ ↦ ⟨rfl, rfl⟩, fun _ ↦ ⟨rfl, rfl⟩⟩

/-- `ALGD-C1-COMMA-01` (例 1, p.2).
With `F = id_D` and `G : 1 → D` picking `a`, the comma category `F ↓ G` is the slice category
`D/a`. mathlib's `Over a` is defined as this comma category, so the identity is an isomorphism
of categories. -/
theorem comma_id_fromPUnit (a : D) :
    Nonempty (IsoCat (Comma (𝟭 D) (Functor.fromPUnit.{0} a)) (Over a)) :=
  ⟨IsoCat.refl _⟩

/-- `ALGD-C1-COMMA-02` (例 2, p.2).
If `D = 1` and `F`, `G` are the unique functors, then `F ↓ G ≅ C₀ × C₁`: the comparison functor
`⟨c₀, c₁, f⟩ ↦ (c₀, c₁)` is an isomorphism of categories. -/
theorem comma_to_punit (F : C₀ ⥤ Discrete PUnit.{w + 1}) (G : C₁ ⥤ Discrete PUnit.{w + 1}) :
    (Comma.equivProd F G).functor.IsIso :=
  ((Comma.equivProd F G).toIsoCat (fun _ ↦ rfl) (fun _ ↦ rfl)).isIso_functor

/-- `ALGD-C1-COMMA-03` (例 3, p.2).
`id_D ↓ id_D ≅ D^2`, the arrow category of 「自然変換・関手圏」. -/
theorem comma_id_id (D : Type u₂) [Category.{v₂} D] :
    Nonempty (IsoCat (Comma (𝟭 D) (𝟭 D)) (ComposableArrows D 1)) :=
  ⟨(ComposableArrows.toArrow (C := D)).asIsomorphism.symm⟩

/-- `ALGD-C1-COMMA-05` (例 5, category of elements, p.2–3).
For a presheaf `P : C^op → Set`, the comma category `y ↓ P` (mathlib's
`CostructuredArrow yoneda P`) has, by the Yoneda lemma, the pairs `⟨c, x⟩` with `x ∈ Pc` as
objects, and morphisms `⟨c, x⟩ → ⟨c', x'⟩` the `f : c → c'` with `Pf(x') = x`. mathlib's
`P.Elements` is `1 ↓ P` in this presentation: pairs `⟨c, x⟩`, with morphisms
`⟨c, x⟩ → ⟨c', x'⟩` the `f : c' → c` with `Pf(x) = x'`. The comparison functor
`(1 ↓ P)^op → y ↓ P` is an isomorphism of categories. -/
theorem elements_op_iso {C : Type u₃} [Category.{v₃} C] (P : Cᵒᵖ ⥤ Type v₃) :
    (Functor.Elements.toCostructuredArrow P).IsIso :=
  inferInstance

/-- `ALGD-C1-COMMA-06` (命題 6, p.3).
`(F ↓ G)^op = G^op ↓ F^op`: swapping the components and reading `f : F c₀ → G c₁` as a
morphism `G^op c₁ → F^op c₀` of `D^op` is an isomorphism of categories. -/
theorem comma_op (F : C₀ ⥤ D) (G : C₁ ⥤ D) :
    Nonempty (IsoCat (Comma F G)ᵒᵖ (Comma G.op F.op)) :=
  ⟨{ functor := (Comma.opFunctor F G).leftOp
     inverse := Comma.unopFunctor G F
     unit_eq := rfl
     counit_eq := rfl }⟩

/-- `ALGD-C1-COMMA-D02` (prose, p.3–4).
The projections `P₀ : F ↓ G → C₀`, `P₁ : F ↓ G → C₁` take the components, and the natural
transformation `κ : F ∘ P₀ ⇒ G ∘ P₁` has `κ_⟨c₀, c₁, f⟩ = f`. -/
theorem projections (F : C₀ ⥤ D) (G : C₁ ⥤ D) :
    (∀ X : Comma F G, (Comma.fst F G).obj X = X.left ∧ (Comma.snd F G).obj X = X.right) ∧
      (∀ {X Y : Comma F G} (g : X ⟶ Y),
        (Comma.fst F G).map g = g.left ∧ (Comma.snd F G).map g = g.right) ∧
      ∀ X : Comma F G, (Comma.natTrans F G).app X = X.hom :=
  ⟨fun _ ↦ ⟨rfl, rfl⟩, fun _ ↦ ⟨rfl, rfl⟩, fun _ ↦ rfl⟩

/-- `ALGD-C1-COMMA-07` (命題 7, universal property, p.4–5).
For a category `X`, functors `Q₀ : X → C₀`, `Q₁ : X → C₁` and `θ : F ∘ Q₀ ⇒ G ∘ Q₁`, there is a
unique functor `H : X → F ↓ G` with (1) `P₀ ∘ H = Q₀` and `P₁ ∘ H = Q₁`, and (2) `κH = θ`.
Condition (2) is stated through the equalities of (1), as in the source's diagram: `κH`
followed by the identification `(P₁ ∘ H) G = Q₁ G` equals the identification
`(P₀ ∘ H) F = Q₀ F` followed by `θ`. -/
theorem universal_property {X : Type u₃} [Category.{v₃} X] (F : C₀ ⥤ D) (G : C₁ ⥤ D)
    (Q₀ : X ⥤ C₀) (Q₁ : X ⥤ C₁) (θ : Q₀ ⋙ F ⟶ Q₁ ⋙ G) :
    ∃! H : X ⥤ Comma F G, ∃ (h₀ : H ⋙ Comma.fst F G = Q₀) (h₁ : H ⋙ Comma.snd F G = Q₁),
      whiskerLeft H (Comma.natTrans F G) ≫ eqToHom (congrArg (· ⋙ G) h₁) =
        eqToHom (congrArg (· ⋙ F) h₀) ≫ θ := by
  refine ⟨Comma.liftFunctor F G Q₀ Q₁ θ,
    ⟨rfl, rfl, Comma.whiskerLeft_liftFunctor_natTrans F G Q₀ Q₁ θ rfl rfl⟩, ?_⟩
  rintro H ⟨h₀, h₁, h⟩
  subst h₀ h₁
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h
  subst h
  rfl

/-- `ALGD-C1-COMMA-08` (例 8, p.5).
For `F, G : C → D`, natural transformations `θ : F ⇒ G` correspond one-to-one to functors
`H : C → F ↓ G` with `P₀ H = id` and `P₁ H = id`, by `θ ↦ ⟨c, c, θ_c⟩` (the case
`Q₀ = Q₁ = id` of 命題 7). -/
theorem natTrans_equiv_sections {C : Type u₃} [Category.{v₃} C] (F G : C ⥤ D) :
    Function.Bijective (fun θ : F ⟶ G ↦
      (⟨Comma.liftFunctor F G (𝟭 C) (𝟭 C) θ, rfl, rfl⟩ :
        {H : C ⥤ Comma F G // H ⋙ Comma.fst F G = 𝟭 C ∧ H ⋙ Comma.snd F G = 𝟭 C})) := by
  constructor
  · intro θ θ' h
    ext x
    have := Functor.congr_obj (congrArg Subtype.val h) x
    injection this with _ _ h₃
  · rintro ⟨H, h₀, h₁⟩
    let θ : F ⟶ G :=
      eqToHom (congrArg (· ⋙ F) h₀.symm) ≫ whiskerLeft H (Comma.natTrans F G) ≫
        eqToHom (congrArg (· ⋙ G) h₁)
    refine ⟨θ, Subtype.ext ?_⟩
    obtain ⟨H', -, hH'⟩ := universal_property F G (𝟭 C) (𝟭 C) θ
    have e₁ := hH' (Comma.liftFunctor F G (𝟭 C) (𝟭 C) θ)
      ⟨rfl, rfl, Comma.whiskerLeft_liftFunctor_natTrans F G (𝟭 C) (𝟭 C) θ rfl rfl⟩
    have e₂ := hH' H ⟨h₀, h₁, by simp [θ]⟩
    exact e₁.trans e₂.symm

/-! ## Axiom audit

Each verified declaration must depend only on Lean's standard axioms. The expected
output is pinned with `#guard_msgs`, so `lake build` fails if it changes. -/

/-- info: 'ProjectEpisteme.AlgD.CommaCategory.comma_category' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms comma_category

/-- info: 'ProjectEpisteme.AlgD.CommaCategory.comma_id_fromPUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms comma_id_fromPUnit

/-- info: 'ProjectEpisteme.AlgD.CommaCategory.comma_to_punit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms comma_to_punit

/-- info: 'ProjectEpisteme.AlgD.CommaCategory.comma_id_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms comma_id_id

/-- info: 'ProjectEpisteme.AlgD.CommaCategory.elements_op_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms elements_op_iso

/-- info: 'ProjectEpisteme.AlgD.CommaCategory.comma_op' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms comma_op

/-- info: 'ProjectEpisteme.AlgD.CommaCategory.projections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms projections

/-- info: 'ProjectEpisteme.AlgD.CommaCategory.universal_property' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms universal_property

/-- info: 'ProjectEpisteme.AlgD.CommaCategory.natTrans_equiv_sections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms natTrans_equiv_sections
end ProjectEpisteme.AlgD.CommaCategory

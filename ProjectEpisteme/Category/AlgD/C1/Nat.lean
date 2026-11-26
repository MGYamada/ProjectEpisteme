module

public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.NatIso
public import ProjectEpisteme.Category.Basic.FunctorCategory

/-!
# alg-d, Chapter 1: 自然変換・関手圏 (Natural transformations and functor categories)

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 1, `nat.pdf`
(<https://alg-d.com/math/kan_extension/nat.pdf>), printed date 2026-05-14,
SHA-256 `9d4c2b4fe05ca20b15ff041fe3884756138a3e76492d12f54da8597fabf61fb1`,
retrieved 2026-11-26. Ledger: `docs/ledger/algd/C1-NAT.md`.

## Conventions

* alg-d composes as `g ∘ f` and writes `GF` for `F` followed by `G`; mathlib writes `f ≫ g` and
  `F ⋙ G`. The source's vertical composite `σ ∘ θ` is `θ ≫ σ`.
* The source's whiskering `Hθ` (functor on the left) is `Functor.whiskerRight θ H`, and its
  `θF` is `Functor.whiskerLeft F θ`.
* The source's horizontal composite of `θ : F₀ ⇒ F₁` and `σ : G₀ ⇒ G₁` is `σF₁ ∘ G₀θ`, that is
  `whiskerRight θ G₀ ≫ whiskerLeft F₁ σ`. mathlib's `θ ◫ σ` is defined by the other formula
  `G₁θ ∘ σF₀`; 例 2 shows that they agree.
* The functor category `D^C` is `C ⥤ D`, and `1` is `Discrete PUnit`.
* The source writes `≅` for an isomorphism of categories, which is stricter than an
  equivalence (`≃` in the source, `≌` in mathlib). Such claims are stated with
  `Functor.IsIso` (full, faithful, and bijective on objects), which yields an `IsoCat` through
  `Functor.asIsomorphism`. The functors involved come from
  `ProjectEpisteme.Category.Basic.FunctorCategory`.
-/

@[expose] public section

namespace ProjectEpisteme.AlgD.Nat

open CategoryTheory Functor

universe w v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

/-- `ALGD-C1-NAT-D01` (prose, §1, p.2).
For `θ : F ⇒ G` and `σ : G ⇒ H`, the vertical composite `σ ∘ θ` has components
`(σ ∘ θ)_a = σ_a ∘ θ_a`. -/
theorem vcomp_app {F G H : C ⥤ D} (θ : F ⟶ G) (σ : G ⟶ H) (a : C) :
    (θ ≫ σ).app a = θ.app a ≫ σ.app a :=
  NatTrans.comp_app θ σ a

/-- `ALGD-C1-NAT-D02` (prose, §1, p.2–3).
For `θ : F ⇒ G` between functors `A → B` and `H : B → C`, the whiskering `Hθ : HF ⇒ HG` has
components `(Hθ)_a = H(θ_a)`. -/
theorem whiskerRight_app {F G : A ⥤ B} (θ : F ⟶ G) (H : B ⥤ C) (a : A) :
    (whiskerRight θ H).app a = H.map (θ.app a) :=
  rfl

/-- `ALGD-C1-NAT-D03` (prose, §1, p.3–4).
For `F : A → B` and `θ : G ⇒ H` between functors `B → C`, the whiskering `θF : GF ⇒ HF` has
components `(θF)_a = θ_{Fa}`. -/
theorem whiskerLeft_app (F : A ⥤ B) {G H : B ⥤ C} (θ : G ⟶ H) (a : A) :
    (whiskerLeft F θ).app a = θ.app (F.obj a) :=
  rfl

/-- 例 1 (p.4) builds a composite from whiskerings and a vertical composition. It has no
standalone claim; this example checks that the composite `F₄θ ∘ σF₀ : F₃F₀ ⇒ F₄F₂` has the
stated type. -/
example {C₀ C₁ C₂ C₃ : Type*} [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    (F₀ : C₀ ⥤ C₁) (F₁ : C₁ ⥤ C₂) (F₂ : C₀ ⥤ C₂) (F₃ : C₁ ⥤ C₃) (F₄ : C₂ ⥤ C₃)
    (θ : F₀ ⋙ F₁ ⟶ F₂) (σ : F₃ ⟶ F₁ ⋙ F₄) : F₀ ⋙ F₃ ⟶ F₂ ⋙ F₄ :=
  whiskerLeft F₀ σ ≫ whiskerRight θ F₄

/-- `ALGD-C1-NAT-02` (例 2, p.5–6).
For `θ : F₀ ⇒ F₁` (functors `A → B`) and `σ : G₀ ⇒ G₁` (functors `B → C`), the two composites
`σF₁ ∘ G₀θ` and `G₁θ ∘ σF₀` agree. The first is the source's horizontal composite, and the
second part identifies it with mathlib's `θ ◫ σ`. -/
theorem horizontal_composites_eq {F₀ F₁ : A ⥤ B} {G₀ G₁ : B ⥤ C} (θ : F₀ ⟶ F₁)
    (σ : G₀ ⟶ G₁) :
    whiskerRight θ G₀ ≫ whiskerLeft F₁ σ = whiskerLeft F₀ σ ≫ whiskerRight θ G₁ ∧
      NatTrans.hcomp θ σ = whiskerRight θ G₀ ≫ whiskerLeft F₁ σ := by
  constructor <;> ext a <;> simp

/-- `ALGD-C1-NAT-03` (例 3, interchange law, p.6–7).
For `θ : F₀ ⇒ F₁`, `θ' : F₁ ⇒ F₂` and `σ : G₀ ⇒ G₁`, `σ' : G₁ ⇒ G₂`, the horizontal composite
of `θ' ∘ θ` and `σ' ∘ σ` equals `(σ'F₂ ∘ G₁θ') ∘ (σF₁ ∘ G₀θ)`. -/
theorem interchange {F₀ F₁ F₂ : A ⥤ B} {G₀ G₁ G₂ : B ⥤ C} (θ : F₀ ⟶ F₁) (θ' : F₁ ⟶ F₂)
    (σ : G₀ ⟶ G₁) (σ' : G₁ ⟶ G₂) :
    whiskerRight (θ ≫ θ') G₀ ≫ whiskerLeft F₂ (σ ≫ σ') =
      (whiskerRight θ G₀ ≫ whiskerLeft F₁ σ) ≫ (whiskerRight θ' G₁ ≫ whiskerLeft F₂ σ') := by
  ext a
  simp

/-- `ALGD-C1-NAT-04` (例 4, p.7).
For `θ : F ⇒ id_C` and `σ : id_C ⇒ G`, the horizontal composite of `θ` followed by `σ`, the
vertical composite `σ ∘ θ`, and the horizontal composite of `σ` followed by `θ` are equal.

The three live in `F ⋙ 𝟭 C ⟶ 𝟭 C ⋙ G`, `F ⟶ G` and `𝟭 C ⋙ F ⟶ G ⋙ 𝟭 C`, which are the same
type up to the definitional equalities `F ⋙ 𝟭 C = F = 𝟭 C ⋙ F`. -/
theorem horizontal_eq_vertical_of_id {F G : C ⥤ C} (θ : F ⟶ 𝟭 C) (σ : 𝟭 C ⟶ G) :
    (whiskerRight θ (𝟭 C) ≫ whiskerLeft (𝟭 C) σ : F ⋙ 𝟭 C ⟶ 𝟭 C ⋙ G) = θ ≫ σ ∧
      θ ≫ σ = (whiskerRight σ F ≫ whiskerLeft G θ : 𝟭 C ⋙ F ⟶ G ⋙ 𝟭 C) := by
  constructor <;> ext a <;> simp

/-- `ALGD-C1-NAT-D04` (prose, §2, p.8).
The functor category `D^C`: its morphisms `F → G` are the natural transformations `F ⇒ G`,
the identity `id_F` has components `id_{Fa}`, and composition is vertical composition. -/
theorem functorCategory_hom_id_comp {F G H : C ⥤ D} :
    (F ⟶ G) = NatTrans F G ∧ (∀ a, (𝟙 F : F ⟶ F).app a = 𝟙 (F.obj a)) ∧
      ∀ (θ : F ⟶ G) (σ : G ⟶ H) (a : C), (θ ≫ σ).app a = θ.app a ≫ σ.app a :=
  ⟨rfl, fun _ ↦ rfl, fun _ _ _ ↦ rfl⟩

/-- `ALGD-C1-NAT-R01` (※ box, p.8–9).
If `C` is small and `D` is locally small, then `D^C` is locally small. Here "small" and
"locally small" are relative to the universe `w`: `C : Type w` with `SmallCategory C`, and
`LocallySmall.{w} D`. -/
theorem functorCategory_locallySmall (C : Type w) [SmallCategory C] [LocallySmall.{w} D] :
    LocallySmall.{w} (C ⥤ D) :=
  inferInstance

/-- `ALGD-C1-NAT-05` (例 5, p.9).
`C^0 ≅ 1` and `C^1 ≅ C`: the unique functor from `Discrete PEmpty ⥤ C` to the one-object
category, and evaluation `(Discrete PUnit ⥤ C) ⥤ C` at the unique object, are isomorphisms of
categories. -/
theorem functorCategory_zero_one :
    (Functor.star (Discrete PEmpty.{w + 1} ⥤ C) : _ ⥤ Discrete PUnit.{w + 1}).IsIso ∧
      (Functor.equiv (C := C) : (Discrete PUnit.{w + 1} ⥤ C) ≌ C).functor.IsIso :=
  ⟨inferInstance, inferInstance⟩

/-- `ALGD-C1-NAT-06` (例 6, p.9).
For a monoid `M` viewed as a one-object category, `Set^M` is the category of left `M`-sets and
equivariant maps. mathlib's `Action (Type w) M` is that category: an object is a type `V` with
a monoid hom `M →* End V` (a left action, since `End V` multiplies by composition), and a
morphism is an equivariant map. Its comparison functor to `SingleObj M ⥤ Type w` is an
isomorphism of categories. -/
theorem functorCategory_singleObj (M : Type w) [Monoid M] :
    (Action.functorCategoryEquivalence (Type w) M).functor.IsIso :=
  ((Action.functorCategoryEquivalence (Type w) M).toIsoCat (fun _ ↦ rfl)
    (fun _ ↦ rfl)).isIso_functor

/-- `ALGD-C1-NAT-07` (例 7, p.9).
For the discrete category `X = {a, b}` (here `Discrete Bool`), `C^X ≅ C × C`: evaluation at
both objects is an isomorphism of categories. -/
theorem functorCategory_discrete_two : (Discrete.evalPair (C := C)).IsIso :=
  inferInstance

/-- `ALGD-C1-NAT-08` (例 8, p.9).
A morphism of presheaves `P ⇒ Q` on `C` is a natural transformation, so `Set^{C^op}` is the
category of presheaves. -/
theorem presheaf_hom (P Q : Cᵒᵖ ⥤ Type w) : (P ⟶ Q) = NatTrans P Q :=
  rfl

/-- `ALGD-C1-NAT-09` (命題 9, p.9–10).
A natural transformation `θ : F ⇒ G` is an isomorphism in `D^C` if and only if each component
`θ_a` is an isomorphism (`θ` is a natural isomorphism). -/
theorem isIso_iff_isIso_app {F G : C ⥤ D} (θ : F ⟶ G) : IsIso θ ↔ ∀ a, IsIso (θ.app a) :=
  NatTrans.isIso_iff_isIso_app θ

/-- `ALGD-C1-NAT-D05` (prose, §2, p.10–11).
Postcomposition with `F : C → D` is a functor `C^M → D^M` sending `G` to `FG` and `θ` to
`Fθ`. -/
theorem postcomposition_obj_map {M : Type u₅} [Category.{v₅} M] (F : C ⥤ D) {G H : M ⥤ C}
    (θ : G ⟶ H) :
    ((whiskeringRight M C D).obj F).obj G = G ⋙ F ∧
      ((whiskeringRight M C D).obj F).map θ = whiskerRight θ F :=
  ⟨rfl, rfl⟩

/-- `ALGD-C1-NAT-D06` (prose, §2, p.11).
Precomposition with `F : C → D` is a functor `F⁻¹ : M^D → M^C` sending `G` to `GF` and `θ` to
`θF`. -/
theorem precomposition_obj_map {M : Type u₅} [Category.{v₅} M] (F : C ⥤ D) {G H : D ⥤ M}
    (θ : G ⟶ H) :
    ((whiskeringLeft C D M).obj F).obj G = F ⋙ G ∧
      ((whiskeringLeft C D M).obj F).map θ = whiskerLeft F θ :=
  ⟨rfl, rfl⟩

/-- `ALGD-C1-NAT-10` (例 10, diagonal functor, p.11).
Precomposition with `! : C → 1`, after `D ≅ D^1`, is the diagonal functor `Δ : D → D^C`:
`Δa` is constant at `a` with `Δa(f) = id_a`, and `(Δf)_c = f`. -/
theorem diagonal :
    Functor.const (Discrete PUnit.{w + 1}) ⋙ (whiskeringLeft C _ D).obj (Functor.star C) =
        Functor.const C ∧
      (∀ (a : D) (c : C), ((Functor.const C).obj a).obj c = a) ∧
      (∀ (a : D) {c c' : C} (f : c ⟶ c'), ((Functor.const C).obj a).map f = 𝟙 a) ∧
      ∀ {a b : D} (f : a ⟶ b) (c : C), ((Functor.const C).map f).app c = f :=
  ⟨rfl, fun _ _ ↦ rfl, fun _ _ _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- `ALGD-C1-NAT-11` (例 11, evaluation, p.12).
For `a : C`, precomposition with the functor `1 → C` picking `a`, after `D^1 ≅ D`, is the
evaluation `ev_a : D^C → D` with `ev_a(G) = Ga` and `ev_a(θ) = θ_a`. Letting `a` vary gives a
functor `ev : D^C × C → D` with `ev(F, a) = Fa` and `ev(θ, f) = θ_b ∘ Ff`; this is mathlib's
`evaluationUncurried` with the factors swapped. -/
theorem ev_functors (a : C) :
    (whiskeringLeft (Discrete PUnit.{w + 1}) C D).obj ((Functor.const _).obj a) ⋙
          (Functor.equiv (C := D)).functor = (CategoryTheory.evaluation C D).obj a ∧
      (∀ G : C ⥤ D, ((CategoryTheory.evaluation C D).obj a).obj G = G.obj a) ∧
      (∀ {G H : C ⥤ D} (θ : G ⟶ H), ((CategoryTheory.evaluation C D).obj a).map θ = θ.app a) ∧
      (∀ (F : C ⥤ D) (a : C),
        (CategoryTheory.Prod.swap (C ⥤ D) C ⋙ evaluationUncurried C D).obj (F, a) = F.obj a) ∧
      ∀ {F G : C ⥤ D} {a b : C} (θ : F ⟶ G) (f : a ⟶ b),
        (CategoryTheory.Prod.swap (C ⥤ D) C ⋙ evaluationUncurried C D).map
          (X := (F, a)) (Y := (G, b)) (θ, f) = F.map f ≫ θ.app b :=
  ⟨rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- `ALGD-C1-NAT-12` (例 12, arrow category, p.12).
With `2 = {0 → 1}` (here `Fin 2`), `C^2` is the arrow category: sending `F` to the arrow
`F 0 → F 1` is an isomorphism of categories onto `Arrow C`, whose morphisms `f → g` are pairs
`⟨h, k⟩` with `g ∘ h = k ∘ f`. Precomposition with the two functors `1 → 2` (evaluation at `0`
and at `1`) becomes `dom` and `cod`, and the diagonal sends `c` to `id_c`. -/
theorem arrowCategory :
    (ComposableArrows.toArrow (C := C)).IsIso ∧
      ComposableArrows.toArrow ⋙ Arrow.leftFunc = (evaluation (Fin 2) C).obj 0 ∧
      ComposableArrows.toArrow ⋙ Arrow.rightFunc = (evaluation (Fin 2) C).obj 1 ∧
      ∀ c : C, ComposableArrows.toArrow.obj ((Functor.const (Fin 2)).obj c) = Arrow.mk (𝟙 c) :=
  ⟨inferInstance, rfl, rfl, fun _ ↦ rfl⟩

/-- `ALGD-C1-NAT-13` (例 13, p.12–13).
For a set `X` viewed as a discrete category, `A ↦ χ_A` is an isomorphism of categories from
`P(X)`, ordered by inclusion, to `2^X`. For `f : X → Y`, precomposition `f⁻¹ : 2^Y → 2^X`
corresponds to the preimage map `P(Y) → P(X)`. -/
theorem powerset_iso_functorCategory (X : Type u₁) :
    (Set.characteristicFunctor X).IsIso ∧
      ∀ {Y : Type u₁} (f : X → Y),
        Set.characteristicFunctor Y ⋙ (whiskeringLeft (Discrete X) (Discrete Y) (Fin 2)).obj
            (Discrete.functor fun x ↦ ⟨f x⟩) =
          (Monotone.functor (f := Set.preimage f) fun _ _ h ↦ Set.preimage_mono h) ⋙
            Set.characteristicFunctor X :=
  ⟨inferInstance, Set.characteristicFunctor_comp_precomp⟩

/-- `ALGD-C1-NAT-D07` (prose, §2, p.13).
For `T : A × B → C` and `a ∈ A`, the functor `T(a, −) : B → C` sends `b` to `T(a, b)` and
`g : b → b'` to `T(id_a, g)`; dually `T(−, b)` sends `f` to `T(f, id_b)`. -/
theorem partial_functors (T : A × B ⥤ C) (a : A) (b : B) :
    (∀ b' : B, ((curry.obj T).obj a).obj b' = T.obj (a, b')) ∧
      (∀ {b₁ b₂ : B} (g : b₁ ⟶ b₂),
        ((curry.obj T).obj a).map g = T.map (X := (a, b₁)) (Y := (a, b₂)) (𝟙 a, g)) ∧
      (∀ a' : A, ((curry.obj T).flip.obj b).obj a' = T.obj (a', b)) ∧
      ∀ {a₁ a₂ : A} (f : a₁ ⟶ a₂),
        ((curry.obj T).flip.obj b).map f = T.map (X := (a₁, b)) (Y := (a₂, b)) (f, 𝟙 b) :=
  ⟨fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- `ALGD-C1-NAT-D08` (prose, §2, p.13–14).
`a ↦ T(a, −)` extends to a functor `T̃ : A → C^B` with `T̃(f)_b = T(f, id_b)` for `f : a → a'`. -/
theorem curry_map_app (T : A × B ⥤ C) {a a' : A} (f : a ⟶ a') (b : B) :
    ((curry.obj T).map f).app b = T.map (X := (a, b)) (Y := (a', b)) (f, 𝟙 b) :=
  rfl

/-- `ALGD-C1-NAT-R02` (prose, §2, p.14).
Functors `T : A × B → C` correspond one-to-one to functors `T̃ : A → C^B`; the inverse sends
`T̃` to the functor with `T(a, b) = T̃(a)(b)`. -/
theorem curry_bijective :
    Function.Bijective (curry.obj : (A × B ⥤ C) → (A ⥤ B ⥤ C)) ∧
      ∀ (T : A ⥤ B ⥤ C) (a : A) (b : B), (uncurry.obj T).obj (a, b) = (T.obj a).obj b :=
  ⟨Function.bijective_iff_has_inverse.mpr
      ⟨uncurry.obj, uncurry_obj_curry_obj, curry_obj_uncurry_obj⟩,
    fun _ _ _ ↦ rfl⟩

/-! ## Axiom audit

Each verified declaration must depend only on Lean's standard axioms. The expected
output is pinned with `#guard_msgs`, so `lake build` fails if it changes. -/

/-- info: 'ProjectEpisteme.AlgD.Nat.vcomp_app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms vcomp_app

/-- info: 'ProjectEpisteme.AlgD.Nat.whiskerRight_app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whiskerRight_app

/-- info: 'ProjectEpisteme.AlgD.Nat.whiskerLeft_app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whiskerLeft_app

/-- info: 'ProjectEpisteme.AlgD.Nat.horizontal_composites_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms horizontal_composites_eq

/-- info: 'ProjectEpisteme.AlgD.Nat.interchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms interchange

/-- info: 'ProjectEpisteme.AlgD.Nat.horizontal_eq_vertical_of_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms horizontal_eq_vertical_of_id

/-- info: 'ProjectEpisteme.AlgD.Nat.functorCategory_hom_id_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms functorCategory_hom_id_comp

/-- info: 'ProjectEpisteme.AlgD.Nat.functorCategory_locallySmall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms functorCategory_locallySmall

/-- info: 'ProjectEpisteme.AlgD.Nat.functorCategory_zero_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms functorCategory_zero_one

/-- info: 'ProjectEpisteme.AlgD.Nat.functorCategory_singleObj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms functorCategory_singleObj

/-- info: 'ProjectEpisteme.AlgD.Nat.functorCategory_discrete_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms functorCategory_discrete_two

/-- info: 'ProjectEpisteme.AlgD.Nat.presheaf_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms presheaf_hom

/-- info: 'ProjectEpisteme.AlgD.Nat.isIso_iff_isIso_app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isIso_iff_isIso_app

/-- info: 'ProjectEpisteme.AlgD.Nat.postcomposition_obj_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms postcomposition_obj_map

/-- info: 'ProjectEpisteme.AlgD.Nat.precomposition_obj_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms precomposition_obj_map

/-- info: 'ProjectEpisteme.AlgD.Nat.diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms diagonal

/-- info: 'ProjectEpisteme.AlgD.Nat.ev_functors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ev_functors

/-- info: 'ProjectEpisteme.AlgD.Nat.arrowCategory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arrowCategory

/-- info: 'ProjectEpisteme.AlgD.Nat.powerset_iso_functorCategory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms powerset_iso_functorCategory

/-- info: 'ProjectEpisteme.AlgD.Nat.partial_functors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms partial_functors

/-- info: 'ProjectEpisteme.AlgD.Nat.curry_map_app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms curry_map_app

/-- info: 'ProjectEpisteme.AlgD.Nat.curry_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms curry_bijective
end ProjectEpisteme.AlgD.Nat

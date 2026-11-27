/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.AdjunctionPreserves
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.TFAE
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Yoneda

/-!
# alg-d, Chapter 2: Kan拡張 (Kan extensions)

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 2, `kan_extension.pdf`
(<https://alg-d.com/math/kan_extension/kan_extension.pdf>), printed date 2026-09-11,
SHA-256 `72fb7c6c1ef47cf9f45a38e71bc2196bcebc7163594158be8ea9e3fcaf88ef66`,
retrieved 2026-11-26. Ledger: `docs/ledger/algd/C2-KAN.md`.

## Conventions

* The source extends `E : C → U` along `F : C → D`; mathlib's `L.leftKanExtension F` extends
  `F` along `L`. Here the source's letters are kept: `F` is the functor extended along and `E`
  the functor extended, so the source's `F † E` is `F.leftKanExtension E`.
* The source composes as `g ∘ f` and writes `TF`; mathlib writes `f ≫ g` and `F ⋙ T`. The unit
  `η : E ⇒ (F † E) F` is `η : E ⟶ F ⋙ T`, and `τF ∘ η` is `η ≫ whiskerLeft F τ`.
* `F⁻¹ : U^D → U^C` is precomposition `(whiskeringLeft C D U).obj F`.
* A left Kan extension is stated as unique factorization (`isLeftKanExtension_iff`), which is
  equivalent to mathlib's class `Functor.IsLeftKanExtension` (an initial object of
  `LeftExtension F E`).
* "K commutes with the left Kan extension `⟨T, η⟩`" is `CommutesWith K T η`; mathlib's
  `Functor.PreservesLeftKanExtension` asks this for every left Kan extension of `E` along `F`.
* Absolute Kan extensions and Kan lifts are not in mathlib for functors (the bicategorical
  versions are `Bicategory.LeftExtension.IsAbsKan` and `Bicategory.LeftLift`). They are defined
  here by unique factorization, with the universes of the test categories as parameters.
* "Absolute" quantifies over all categories, but Lean quantifies over one universe pair: the
  test categories of `IsAbsoluteLeftKanExtension.{w, w'}` live in `Type w` with hom universe
  `w'`. 定理 17 and 20–22 instantiate these with the universes that their proofs use.
* For Kan lifts the test functors act by precomposition, so "F commutes with F‡ id_D" in
  定理 21 means that precomposing with `F` gives a Kan lift again.
* From 補題 24 on, `Ĉ = C^op → Type v` compares `Set`-valued presheaves, so `D` and `U` share
  the hom universe `v`. From 系 28 on, `C` is small, as in the source, and `F † y` is
  `restrictYoneda F = (d ↦ Hom_D(F−, d))` with the unit `restrictYonedaUnit F`.
-/

@[expose] public section

namespace ProjectEpisteme.AlgD.Kan

open CategoryTheory Limits Functor Opposite

universe w w' v v₁ v₂ v₃ v₄ v₅ u u₁ u₂ u₃ u₄ u₅

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {U : Type u₃} [Category.{v₃} U]

/-! ## §1 Definition -/

/-- A structured arrow is initial iff it has the unique factorization property. -/
private theorem structuredArrow_isInitial_iff {X : Type*} [Category X] {Y : Type*} [Category Y]
    (G : Y ⥤ X) (x : X) (y : Y) (f : x ⟶ G.obj y) :
    Nonempty (IsInitial (StructuredArrow.mk f : StructuredArrow x G)) ↔
      ∀ (y' : Y) (f' : x ⟶ G.obj y'), ∃! h : y ⟶ y', f ≫ G.map h = f' := by
  constructor
  · rintro ⟨t⟩ y' f'
    refine ⟨(t.to (StructuredArrow.mk f')).right, StructuredArrow.w (t.to (StructuredArrow.mk f')),
      fun h hh ↦ ?_⟩
    exact congrArg CommaMorphism.right
      (t.hom_ext (StructuredArrow.homMk h hh : StructuredArrow.mk f ⟶ StructuredArrow.mk f') _)
  · intro H
    choose h hw huniq using H
    exact ⟨IsInitial.ofUniqueHom (fun Y ↦ StructuredArrow.homMk (h Y.right Y.hom) (hw _ _))
      fun Y m ↦ StructuredArrow.hom_ext _ _ (huniq _ _ m.right (StructuredArrow.w m))⟩

/-- A costructured arrow is terminal iff it has the unique factorization property. -/
private theorem costructuredArrow_isTerminal_iff {X : Type*} [Category X] {Y : Type*}
    [Category Y] (G : Y ⥤ X) (x : X) (y : Y) (f : G.obj y ⟶ x) :
    Nonempty (IsTerminal (CostructuredArrow.mk f : CostructuredArrow G x)) ↔
      ∀ (y' : Y) (f' : G.obj y' ⟶ x), ∃! h : y' ⟶ y, G.map h ≫ f = f' := by
  constructor
  · rintro ⟨t⟩ y' f'
    refine ⟨(t.from (CostructuredArrow.mk f')).left,
      CostructuredArrow.w (t.from (CostructuredArrow.mk f')), fun h hh ↦ ?_⟩
    exact congrArg CommaMorphism.left
      (t.hom_ext (CostructuredArrow.homMk h hh : CostructuredArrow.mk f' ⟶ CostructuredArrow.mk f)
        _)
  · intro H
    choose h hw huniq using H
    exact ⟨IsTerminal.ofUniqueHom (fun Y ↦ CostructuredArrow.homMk (h Y.left Y.hom) (hw _ _))
      fun Y m ↦ CostructuredArrow.hom_ext _ _ (huniq _ _ m.left (CostructuredArrow.w m))⟩

/-- `ALGD-C2-KAN-D01` (定義, §1, p.1–2).
A left Kan extension of `E : C → U` along `F : C → D` is a universal arrow `⟨T, η⟩` from `E` to
`F⁻¹`: `T : D → U` and `η : E ⇒ TF`, such that for every `S : D → U` and `θ : E ⇒ SF` there is
a unique `τ : T ⇒ S` with `θ = τF ∘ η`. This is equivalent to mathlib's
`Functor.IsLeftKanExtension`. -/
theorem isLeftKanExtension_iff {F : C ⥤ D} {E : C ⥤ U} (T : D ⥤ U) (η : E ⟶ F ⋙ T) :
    T.IsLeftKanExtension η ↔
      ∀ (S : D ⥤ U) (θ : E ⟶ F ⋙ S), ∃! τ : T ⟶ S, θ = η ≫ whiskerLeft F τ := by
  have key := structuredArrow_isInitial_iff ((whiskeringLeft C D U).obj F) E T η
  constructor
  · intro h S θ
    obtain ⟨τ, hτ, huniq⟩ := key.1 h.nonempty_isUniversal S θ
    exact ⟨τ, hτ.symm, fun τ' hτ' ↦ huniq τ' hτ'.symm⟩
  · intro h
    refine ⟨key.2 fun S θ ↦ ?_⟩
    obtain ⟨τ, hτ, huniq⟩ := h S θ
    exact ⟨τ, hτ.symm, fun τ' hτ' ↦ huniq τ' hτ'.symm⟩

/-- `ALGD-C2-KAN-D03` (prose, §1, p.2).
A right Kan extension `⟨T, ε⟩` of `E` along `F` reverses the natural transformations:
`ε : TF ⇒ E`, and for every `S : D → U` and `θ : SF ⇒ E` there is a unique `τ : S ⇒ T` with
`θ = ε ∘ τF`. This is equivalent to mathlib's `Functor.IsRightKanExtension`. -/
theorem isRightKanExtension_iff {F : C ⥤ D} {E : C ⥤ U} (T : D ⥤ U) (ε : F ⋙ T ⟶ E) :
    T.IsRightKanExtension ε ↔
      ∀ (S : D ⥤ U) (θ : F ⋙ S ⟶ E), ∃! τ : S ⟶ T, θ = whiskerLeft F τ ≫ ε := by
  have key := costructuredArrow_isTerminal_iff ((whiskeringLeft C D U).obj F) E T ε
  constructor
  · intro h S θ
    obtain ⟨τ, hτ, huniq⟩ := key.1 h.nonempty_isUniversal S θ
    exact ⟨τ, hτ.symm, fun τ' hτ' ↦ huniq τ' hτ'.symm⟩
  · intro h
    refine ⟨key.2 fun S θ ↦ ?_⟩
    obtain ⟨τ, hτ, huniq⟩ := h S θ
    exact ⟨τ, hτ.symm, fun τ' hτ' ↦ huniq τ' hτ'.symm⟩

section KanLift

variable {X : Type u₄} [Category.{v₄} X]

/-- `ALGD-C2-KAN-D04` (prose, §1, p.3).
A left Kan lift of `E : X → U` along `F : D → U` is `⟨L, η⟩` with `L : X → D` and
`η : E ⇒ FL`, such that for every `S : X → D` and `θ : E ⇒ FS` there is a unique `τ : L ⇒ S`
with `θ = Fτ ∘ η`. The source writes `L = F† E`. -/
def IsLeftKanLift (F : D ⥤ U) {E : X ⥤ U} (L : X ⥤ D) (η : E ⟶ L ⋙ F) : Prop :=
  ∀ (S : X ⥤ D) (θ : E ⟶ S ⋙ F), ∃! τ : L ⟶ S, θ = η ≫ whiskerRight τ F

/-- A right Kan lift of `E : X → U` along `F : D → U` (the source's `F‡ E`) is `⟨R, ε⟩` with
`ε : FR ⇒ E`, such that every `θ : FS ⇒ E` factors as `ε ∘ Fτ` for a unique `τ : S ⇒ R`.
This is part of `ALGD-C2-KAN-D04`. -/
def IsRightKanLift (F : D ⥤ U) {E : X ⥤ U} (R : X ⥤ D) (ε : R ⋙ F ⟶ E) : Prop :=
  ∀ (S : X ⥤ D) (θ : S ⋙ F ⟶ E), ∃! τ : S ⟶ R, θ = whiskerRight τ F ≫ ε

/-- Kan lifts are universal arrows for postcomposition `F_* : D^X → U^X`: a left Kan lift is an
initial object of `E ↓ F_*` and a right Kan lift a terminal object of `F_* ↓ E`. -/
theorem isLeftKanLift_iff_isInitial (F : D ⥤ U) {E : X ⥤ U} (L : X ⥤ D) (η : E ⟶ L ⋙ F) :
    IsLeftKanLift F L η ↔ Nonempty (IsInitial
      (StructuredArrow.mk η : StructuredArrow E ((whiskeringRight X D U).obj F))) := by
  rw [structuredArrow_isInitial_iff]
  exact forall₂_congr fun S θ ↦ existsUnique_congr fun τ ↦ eq_comm

theorem isRightKanLift_iff_isTerminal (F : D ⥤ U) {E : X ⥤ U} (R : X ⥤ D) (ε : R ⋙ F ⟶ E) :
    IsRightKanLift F R ε ↔ Nonempty (IsTerminal
      (CostructuredArrow.mk ε : CostructuredArrow ((whiskeringRight X D U).obj F) E)) := by
  rw [costructuredArrow_isTerminal_iff]
  exact forall₂_congr fun S θ ↦ existsUnique_congr fun τ ↦ eq_comm

end KanLift

/-- `ALGD-C2-KAN-01` (命題 1, p.3).
`F † E` exists iff `Hom_{U^C}(E, F⁻¹(−)) : U^D → Set` is representable, that is, iff there are
`T : D → U` and bijections `φ_S : Hom(T, S) ≅ Hom(E, SF)` natural in `S`. Then `⟨T, η⟩` with
`η := φ_T(id_T)` is a left Kan extension, so `η` is its unit. Conversely the left Kan extension
gives such bijections, `τ ↦ τF ∘ η` (`Functor.homEquivOfIsLeftKanExtension`). Representability
is written out because `Hom(E, SF)` and `Hom(T, S)` lie in different universes when `C` and `D`
do. -/
theorem representable_iff_hasLeftKanExtension (F : C ⥤ D) (E : C ⥤ U) :
    ((∃ (T : D ⥤ U) (φ : ∀ S : D ⥤ U, (T ⟶ S) ≃ (E ⟶ F ⋙ S)),
        ∀ (S S' : D ⥤ U) (τ : T ⟶ S) (σ : S ⟶ S'), φ S' (τ ≫ σ) = φ S τ ≫ whiskerLeft F σ) ↔
      F.HasLeftKanExtension E) ∧
    ∀ (T : D ⥤ U) (φ : ∀ S : D ⥤ U, (T ⟶ S) ≃ (E ⟶ F ⋙ S)),
      (∀ (S S' : D ⥤ U) (τ : T ⟶ S) (σ : S ⟶ S'), φ S' (τ ≫ σ) = φ S τ ≫ whiskerLeft F σ) →
      T.IsLeftKanExtension (φ T (𝟙 T)) := by
  have unit : ∀ (T : D ⥤ U) (φ : ∀ S : D ⥤ U, (T ⟶ S) ≃ (E ⟶ F ⋙ S)),
      (∀ (S S' : D ⥤ U) (τ : T ⟶ S) (σ : S ⟶ S'), φ S' (τ ≫ σ) = φ S τ ≫ whiskerLeft F σ) →
      T.IsLeftKanExtension (φ T (𝟙 T)) := by
    intro T φ hφ
    rw [isLeftKanExtension_iff]
    intro S θ
    have hfac : ∀ τ : T ⟶ S, φ S τ = φ T (𝟙 T) ≫ whiskerLeft F τ := fun τ ↦ by
      simpa using hφ T S (𝟙 T) τ
    refine ⟨(φ S).symm θ, ?_, fun τ hτ ↦ ?_⟩
    · beta_reduce
      rw [← hfac, Equiv.apply_symm_apply]
    · beta_reduce at hτ
      rw [← hfac] at hτ
      rw [hτ, Equiv.symm_apply_apply]
  refine ⟨⟨fun ⟨T, φ, hφ⟩ ↦ ?_, fun _ ↦ ?_⟩, unit⟩
  · have := unit T φ hφ
    exact HasLeftKanExtension.mk T (φ T (𝟙 T))
  · refine ⟨F.leftKanExtension E,
      fun S ↦ homEquivOfIsLeftKanExtension _ (F.leftKanExtensionUnit E) S, fun S S' τ σ ↦ ?_⟩
    simp [homEquivOfIsLeftKanExtension]

/-- `ALGD-C2-KAN-02` (命題 2, p.3).
If every `E ∈ U^C` has a left Kan extension along `F`, then `F† : U^C → U^D` is left adjoint to
`F⁻¹`, and the unit of `F† ⊣ F⁻¹` at `E` is the unit of `F † E`. Similarly, if every `E` has a
right Kan extension, then `F‡` is right adjoint to `F⁻¹` with counit the counits of the right Kan
extensions; together `F† ⊣ F⁻¹ ⊣ F‡`. -/
theorem lan_ran_adjunction (F : C ⥤ D) :
    (∀ [∀ E : C ⥤ U, F.HasLeftKanExtension E] (E : C ⥤ U),
        (F.lanAdjunction U).unit.app E = F.leftKanExtensionUnit E) ∧
    ∀ [∀ E : C ⥤ U, F.HasRightKanExtension E] (E : C ⥤ U),
        (F.ranAdjunction U).counit.app E = F.rightKanExtensionCounit E := by
  refine ⟨fun E ↦ ?_, fun E ↦ ?_⟩
  · rw [lanAdjunction_unit]
    rfl
  · rw [ranAdjunction_counit]
    rfl

private theorem star_map {J : Type u₄} [Category.{v₄} J] {j j' : J} (f : j ⟶ j') :
    (star.{w} J).map f = 𝟙 _ :=
  rfl

/-- `ALGD-C2-KAN-03` (例 3, p.3–4).
For `E : J → U` and the unique functor `J → 1`, a cocone `⟨c, μ⟩` on `E` is a colimit iff the
functor `1 → U` with value `c`, together with `μ : E ⇒ ∆c`, is a left Kan extension of `E` along
`J → 1`: colimits are left Kan extensions whose unit is the colimit cocone. Dually, limits are
right Kan extensions along `J → 1`. -/
theorem colimit_iff_isLeftKanExtension {J : Type u₄} [Category.{v₄} J] (E : J ⥤ U) :
    (∀ c : Cocone E, Nonempty (IsColimit c) ↔
      (fromPUnit.{w} c.pt).IsLeftKanExtension (F := E) (L := star J) c.ι) ∧
    ∀ c : Cone E, Nonempty (IsLimit c) ↔
      (fromPUnit.{w} c.pt).IsRightKanExtension (F := E) (L := star J) c.π := by
  refine ⟨fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [isLeftKanExtension_iff]
    constructor
    · rintro ⟨hc⟩ S θ
      have hθ : ∀ (j j' : J) (f : j ⟶ j'), E.map f ≫ θ.app j' = θ.app j ≫ 𝟙 _ := by
        intro j j' f
        have h := θ.naturality f
        erw [Functor.comp_map, star_map, S.map_id] at h
        exact h
      let s : Cocone E := ⟨S.obj ⟨⟨⟩⟩, { app := θ.app, naturality := hθ }⟩
      refine ⟨Discrete.natTrans fun _ ↦ hc.desc s, ?_, fun τ hτ ↦ ?_⟩
      · ext j
        exact (hc.fac s j).symm
      · ext ⟨⟨⟩⟩
        refine hc.uniq s _ fun j ↦ ?_
        exact (congrArg (fun α ↦ NatTrans.app α j) hτ).symm
    · intro h
      refine ⟨IsColimit.ofExistsUnique fun s ↦ ?_⟩
      obtain ⟨τ, hτ, huniq⟩ := h (fromPUnit s.pt) s.ι
      refine ⟨τ.app ⟨⟨⟩⟩, fun j ↦ (congrArg (fun α ↦ NatTrans.app α j) hτ).symm,
        fun f hf ↦ ?_⟩
      have := huniq (Discrete.natTrans fun _ ↦ f) (by ext j; exact (hf j).symm)
      rw [← this]
      rfl
  · rw [isRightKanExtension_iff]
    constructor
    · rintro ⟨hc⟩ S θ
      have hθ : ∀ (j j' : J) (f : j ⟶ j'), 𝟙 _ ≫ θ.app j' = θ.app j ≫ E.map f := by
        intro j j' f
        have h := θ.naturality f
        erw [Functor.comp_map, star_map, S.map_id] at h
        exact h
      let s : Cone E := ⟨S.obj ⟨⟨⟩⟩, { app := θ.app, naturality := hθ }⟩
      refine ⟨Discrete.natTrans fun _ ↦ hc.lift s, ?_, fun τ hτ ↦ ?_⟩
      · ext j
        exact (hc.fac s j).symm
      · ext ⟨⟨⟩⟩
        refine hc.uniq s _ fun j ↦ ?_
        exact (congrArg (fun α ↦ NatTrans.app α j) hτ).symm
    · intro h
      refine ⟨IsLimit.ofExistsUnique fun s ↦ ?_⟩
      obtain ⟨τ, hτ, huniq⟩ := h (fromPUnit s.pt) s.π
      refine ⟨τ.app ⟨⟨⟩⟩, fun j ↦ (congrArg (fun α ↦ NatTrans.app α j) hτ).symm,
        fun f hf ↦ ?_⟩
      have := huniq (Discrete.natTrans fun _ ↦ f) (by ext j; exact (hf j).symm)
      rw [← this]
      rfl

/-! ## §2 Pointwise Kan extensions -/

/-- `ALGD-C2-KAN-04` (定理 4, p.7).
If for every `d ∈ D` the colimit of `F ↓ d → C → U` exists, then the left Kan extension `F † E`
exists and `F † E(d) ≅ colim(F ↓ d → C → U)`. The functor built in the proof is mathlib's
`Functor.pointwiseLeftKanExtension`: `d ↦ colim(F ↓ d → C → U)`, with `Lf` induced by
`F ↓ d → F ↓ d'`. -/
theorem pointwise_leftKanExtension (F : C ⥤ D) (E : C ⥤ U)
    [∀ d : D, HasColimit (CostructuredArrow.proj F d ⋙ E)] :
    (F.pointwiseLeftKanExtension E).IsLeftKanExtension (F.pointwiseLeftKanExtensionUnit E) ∧
    F.HasLeftKanExtension E ∧
    ∀ d : D, Nonempty ((F.leftKanExtension E).obj d ≅ colimit (CostructuredArrow.proj F d ⋙ E)) :=
  ⟨inferInstance, inferInstance, fun d ↦ ⟨F.leftKanExtensionObjIsoColimit E d⟩⟩

/-- `ALGD-C2-KAN-05` (系 5, p.7).
If `U` is cocomplete and `C` is small, then every `E : C → U` has a left Kan extension along
`F : C → D`, so `F⁻¹ : U^D → U^C` has a left adjoint `F† ⊣ F⁻¹`. "Small" and "cocomplete" refer
to the universe `v` of the hom-sets of `D` and `U`. -/
theorem hasLeftKanExtension_of_cocomplete {C : Type v} [SmallCategory C] {D : Type u₂}
    [Category.{v} D] {U : Type u₃} [Category.{v} U] [HasColimits U] (F : C ⥤ D) :
    (∀ E : C ⥤ U, F.HasLeftKanExtension E) ∧ ((whiskeringLeft C D U).obj F).IsRightAdjoint := by
  have : ∀ E : C ⥤ U, F.HasLeftKanExtension E := fun E ↦ inferInstance
  exact ⟨this, (F.lanAdjunction U).isRightAdjoint⟩

/-- `ALGD-C2-KAN-06` (系 6, p.7).
For small categories `C`, `D` and `F : C → D`, every presheaf `E : C^op → Set` has a left Kan
extension `F † E : D^op → Set` along `F^op`. -/
theorem presheaf_hasLeftKanExtension {C : Type v} [SmallCategory C] {D : Type v} [SmallCategory D]
    (F : C ⥤ D) (E : Cᵒᵖ ⥤ Type v) : F.op.HasLeftKanExtension E :=
  (hasLeftKanExtension_of_cocomplete F.op).1 E

/-- `ALGD-C2-KAN-R01` (prose after 系 6, p.7, with footnote 2).
For small `C`, `D` there is an adjunction `F† ⊣ F⁻¹ : Ĉ → D̂`; precisely, `(F^op)⁻¹` has the left
adjoint `(F^op)†` (`Functor.lanAdjunction`). -/
theorem presheaf_lan_adjunction {C : Type v} [SmallCategory C] {D : Type v} [SmallCategory D]
    (F : C ⥤ D) : ((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)).obj F.op).IsRightAdjoint :=
  (hasLeftKanExtension_of_cocomplete F.op).2

/-- `ALGD-C2-KAN-07` (定理 7, p.7).
If for every `d ∈ D` the limit of `d ↓ F → C → U` exists, then the right Kan extension `F ‡ E`
exists and `F ‡ E(d) ≅ lim(d ↓ F → C → U)`. -/
theorem pointwise_rightKanExtension (F : C ⥤ D) (E : C ⥤ U)
    [∀ d : D, HasLimit (StructuredArrow.proj d F ⋙ E)] :
    (F.pointwiseRightKanExtension E).IsRightKanExtension (F.pointwiseRightKanExtensionCounit E) ∧
    F.HasRightKanExtension E ∧
    ∀ d : D, Nonempty ((F.rightKanExtension E).obj d ≅ limit (StructuredArrow.proj d F ⋙ E)) :=
  ⟨inferInstance, inferInstance, fun d ↦
    ⟨(isPointwiseRightKanExtensionOfIsRightKanExtension _ (F.rightKanExtensionCounit E) d).isoLimit⟩⟩

/-- `ALGD-C2-KAN-R02` (prose after 定理 7, p.8).
If `U` is complete and `C` is small, every `E : C → U` has a right Kan extension along `F`, so
`F⁻¹` has a right adjoint `F‡`. In particular, for small `C`, `D`, `F⁻¹ ⊣ F‡ : D̂ → Ĉ`. -/
theorem hasRightKanExtension_of_complete {C : Type v} [SmallCategory C] {D : Type u₂}
    [Category.{v} D] {U : Type u₃} [Category.{v} U] [HasLimits U] (F : C ⥤ D) :
    (∀ E : C ⥤ U, F.HasRightKanExtension E) ∧ ((whiskeringLeft C D U).obj F).IsLeftAdjoint ∧
    ∀ {D' : Type v} [SmallCategory D'] (F' : C ⥤ D'),
      ((whiskeringLeft Cᵒᵖ D'ᵒᵖ (Type v)).obj F'.op).IsLeftAdjoint := by
  have : ∀ E : C ⥤ U, F.HasRightKanExtension E := fun E ↦ inferInstance
  refine ⟨this, (F.ranAdjunction U).isLeftAdjoint, fun {D'} _ F' ↦ ?_⟩
  have : ∀ E : Cᵒᵖ ⥤ Type v, F'.op.HasRightKanExtension E := fun E ↦ inferInstance
  exact (F'.op.ranAdjunction (Type v)).isLeftAdjoint

/-- `ALGD-C2-KAN-08` (例 8, p.8–9).
For a map `f : X → Y`, the preimage functor `f⁻¹ : P(Y) → P(X)` between the posets of subsets has
the image functor `A ↦ f(A)` as left adjoint (the left Kan extension `f†`) and
`f_!(A) = Y ∖ f(X ∖ A)` (`Set.kernImage`) as right adjoint. Hence `f⁻¹` preserves unions and
intersections. The image functor has no left adjoint in general, since it need not preserve
intersections. -/
theorem preimage_adjoints {X Y : Type u} (f : X → Y) :
    Nonempty ((Set.image_preimage (f := f)).monotone_l.functor ⊣
      (Set.image_preimage (f := f)).monotone_u.functor) ∧
    Nonempty ((Set.preimage_kernImage (f := f)).monotone_l.functor ⊣
      (Set.preimage_kernImage (f := f)).monotone_u.functor) ∧
    (∀ A : Set X, Set.kernImage f A = (f '' Aᶜ)ᶜ) ∧
    (∀ A B : Set Y, f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B ∧ f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B) ∧
    ∃ g : Bool → Unit, ¬ (Set.image_preimage (f := g)).monotone_l.functor.IsRightAdjoint := by
  refine ⟨⟨(Set.image_preimage (f := f)).adjunction⟩, ⟨(Set.preimage_kernImage (f := f)).adjunction⟩,
    fun A ↦ Set.kernImage_eq_compl, fun A B ↦ ⟨Set.preimage_union, Set.preimage_inter⟩,
    fun _ ↦ (), fun h ↦ ?_⟩
  obtain ⟨L, ⟨adj⟩⟩ := h
  have hinf := (adj.gc).u_inf (b₁ := ({true} : Set Bool)) (b₂ := {false})
  have h1 : ((fun _ ↦ ()) '' ({true} ∩ {false} : Set Bool)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro _ ⟨b, hb, -⟩
    cases b <;> simp_all
  have h2 : (() : Unit) ∈ ((fun _ ↦ ()) '' ({true} : Set Bool)) ∩
      ((fun _ ↦ ()) '' ({false} : Set Bool)) :=
    ⟨⟨true, rfl, rfl⟩, ⟨false, rfl, rfl⟩⟩
  have : (() : Unit) ∈ ((fun _ ↦ ()) '' ({true} ∩ {false} : Set Bool)) := by
    have e : (fun _ ↦ ()) '' ({true} ∩ {false} : Set Bool) =
        (fun _ ↦ ()) '' ({true} : Set Bool) ∩ (fun _ ↦ ()) '' ({false} : Set Bool) := hinf
    rw [e]
    exact h2
  rw [h1] at this
  exact this

section Example11

/-- The functor `1 → 2` with value `1`, used in 例 11. -/
abbrev ex11F : Discrete PUnit.{1} ⥤ Fin 2 := fromPUnit 1

/-- The functor `1 → {a, b}` with value `a`, used in 例 11. -/
abbrev ex11E : Discrete PUnit.{1} ⥤ Discrete Bool := fromPUnit ⟨true⟩

/-- `ALGD-C2-KAN-11` (例 11, p.11).
A left Kan extension need not be pointwise. For `F : 1 → 2 = {0 → 1}` with value `1` and
`E : 1 → U = {a, b}` (discrete) with value `a`, the constant functor `∆a` with the identity unit
is a left Kan extension of `E` along `F`; but `F ↓ 0` is empty and `{a, b}` has no initial
object, so the colimit needed at `0` does not exist and there is no pointwise left Kan
extension. -/
theorem leftKanExtension_not_pointwise :
    ((const (Fin 2)).obj (⟨true⟩ : Discrete Bool)).IsLeftKanExtension (F := ex11E) (L := ex11F)
      (𝟙 ex11E) ∧
    ¬ HasColimit (CostructuredArrow.proj ex11F 0 ⋙ ex11E) := by
  constructor
  · rw [isLeftKanExtension_iff]
    intro S θ
    have h1 : (⟨true⟩ : Discrete Bool) = S.obj 1 := Discrete.ext (Discrete.eq_of_hom (θ.app ⟨⟨⟩⟩))
    have h0 : S.obj 0 = S.obj 1 :=
      Discrete.ext (Discrete.eq_of_hom (S.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))))
    have hS : ∀ i : Fin 2, (⟨true⟩ : Discrete Bool) = S.obj i := by
      intro i
      fin_cases i
      · exact h1.trans h0.symm
      · exact h1
    refine ⟨{ app := fun i ↦ eqToHom (hS i), naturality := fun _ _ _ ↦ Subsingleton.elim _ _ },
      ?_, fun τ _ ↦ ?_⟩
    · ext
      exact Subsingleton.elim _ _
    · ext
      exact Subsingleton.elim _ _
  · intro h
    have hempty : IsEmpty (CostructuredArrow ex11F 0) :=
      ⟨fun g ↦ absurd (leOfHom g.hom) (by change ¬ (1 : Fin 2) ≤ 0; decide)⟩
    let c := colimit (CostructuredArrow.proj ex11F 0 ⋙ ex11E)
    let s : Cocone (CostructuredArrow.proj ex11F 0 ⋙ ex11E) :=
      ⟨⟨!c.as⟩, { app := fun g ↦ (hempty.false g).elim, naturality := fun g ↦ (hempty.false g).elim }⟩
    have := Discrete.eq_of_hom (colimit.desc _ s)
    exact Bool.not_ne_self c.as this.symm

end Example11

/-- `ALGD-C2-KAN-D05` (定義 (各点左 Kan 拡張), p.15–16).
`⟨T, η⟩` is a pointwise left Kan extension of `E` along `F` iff for every `d ∈ D` the cocone
`⟨T d, μ^d⟩` with `μ^d := Tκ ∘ ηP₀`, that is `μ^d_⟨c, f⟩ = T f ∘ η_c`, is a colimit of
`F ↓ d → C → U`. mathlib's `LeftExtension.IsPointwiseLeftKanExtension` asks that every
`(LeftExtension.mk T η).coconeAt d` be a colimit; this states that `coconeAt d` is `⟨T d, μ^d⟩`. -/
theorem coconeAt_eq (F : C ⥤ D) (E : C ⥤ U) (T : D ⥤ U) (η : E ⟶ F ⋙ T) (d : D) :
    ((LeftExtension.mk T η).coconeAt d).pt = T.obj d ∧
    ∀ g : CostructuredArrow F d,
      ((LeftExtension.mk T η).coconeAt d).ι.app g = η.app g.left ≫ T.map g.hom :=
  ⟨rfl, fun _ ↦ rfl⟩

/-- `ALGD-C2-KAN-13` (命題 13, p.16).
The left Kan extension `⟨L, η⟩` built in the proof of 定理 4 is pointwise. -/
theorem pointwiseLeftKanExtension_isPointwise (F : C ⥤ D) (E : C ⥤ U)
    [∀ d : D, HasColimit (CostructuredArrow.proj F d ⋙ E)] :
    Nonempty (LeftExtension.mk _ (F.pointwiseLeftKanExtensionUnit E)).IsPointwiseLeftKanExtension :=
  ⟨F.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension E⟩

/-- `ALGD-C2-KAN-14` (命題 14, p.16–17).
Every pointwise left Kan extension is a left Kan extension. -/
theorem isPointwise_isLeftKanExtension {F : C ⥤ D} {E : C ⥤ U} {T : D ⥤ U} {η : E ⟶ F ⋙ T}
    (h : (LeftExtension.mk T η).IsPointwiseLeftKanExtension) : T.IsLeftKanExtension η :=
  h.isLeftKanExtension

section Commutes

variable {V : Type u₄} [Category.{v₄} V]

/-- `K : U → V` commutes with `⟨T, η⟩` when `⟨K ∘ T, Kη⟩` is a left Kan extension of `KE` along
`F` (the definition `ALGD-C2-KAN-D06`). -/
def CommutesWith (K : U ⥤ V) {F : C ⥤ D} {E : C ⥤ U} (T : D ⥤ U) (η : E ⟶ F ⋙ T) : Prop :=
  (T ⋙ K).IsLeftKanExtension (whiskerRight η K ≫ (Functor.associator F T K).hom)

/-- `ALGD-C2-KAN-D06` (定義 (左 Kan 拡張と交換する), p.17).
For a left Kan extension `⟨T, η⟩` of `E` along `F`, `K : U → V` commutes with it iff
`⟨K ∘ T, Kη⟩` is a left Kan extension of `KE` along `F` (`CommutesWith`). This is equivalent to
mathlib's `Functor.PreservesLeftKanExtension`, which asks it for every left Kan extension of `E`
along `F`. -/
theorem commutesWith_iff_preserves (K : U ⥤ V) {F : C ⥤ D} {E : C ⥤ U} (T : D ⥤ U)
    (η : E ⟶ F ⋙ T) [T.IsLeftKanExtension η] :
    CommutesWith K T η ↔ K.PreservesLeftKanExtension E F :=
  ⟨fun h ↦ PreservesLeftKanExtension.mk_of_preserves_isLeftKanExtension K E F T η h,
    fun _ ↦ PreservesLeftKanExtension.preserves T η⟩

/-- `ALGD-C2-KAN-15` (定理 15, p.18).
If `⟨T, η⟩` is a pointwise left Kan extension of `E` along `F` and `K : U → V` preserves the
colimits of `F ↓ d → C → U`, then `⟨K ∘ T, Kη⟩` is again pointwise, so `K` commutes with
`⟨T, η⟩`. -/
theorem commutesWith_of_preservesColimit {F : C ⥤ D} {E : C ⥤ U} {T : D ⥤ U}
    {η : E ⟶ F ⋙ T} (h : (LeftExtension.mk T η).IsPointwiseLeftKanExtension) (K : U ⥤ V)
    [∀ d : D, PreservesColimit (CostructuredArrow.proj F d ⋙ E) K] :
    Nonempty (LeftExtension.mk (T ⋙ K)
      (whiskerRight η K ≫ (Functor.associator F T K).hom)).IsPointwiseLeftKanExtension ∧
    CommutesWith K T η := by
  have h' := LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
    (LeftExtension.postcompose₂ObjMkIso K η) (h.postcompose K)
  exact ⟨⟨h'⟩, h'.isLeftKanExtension⟩

end Commutes

/-! ## §3 Adjunctions and Kan extensions -/

/-- `ALGD-C2-KAN-D07` (定義 (絶対左 Kan 拡張), p.18).
An absolute left Kan extension of `E` along `F` is a left Kan extension `⟨T, η⟩` that commutes
with every functor `H : U → V`. The test categories `V` range over `Type w` with hom universe
`w'`; these are the first two universe parameters. -/
def IsAbsoluteLeftKanExtension {F : C ⥤ D} {E : C ⥤ U} (T : D ⥤ U) (η : E ⟶ F ⋙ T) : Prop :=
  T.IsLeftKanExtension η ∧ ∀ (V : Type w) [Category.{w'} V] (H : U ⥤ V), CommutesWith H T η


/-- `ALGD-C2-KAN-16` (命題 16, p.18–19).
`⟨T, η⟩` is an absolute left Kan extension iff it is a left Kan extension and for every
category `V`, functors `H : U → V`, `K : D → V` and `θ : HE ⇒ KF` there is a unique
`τ : HT ⇒ K` with `θ = τF ∘ Hη`. (The source omits the first conjunct, which is the case
`H = id_U`; here the test categories range over a fixed universe that need not contain `U`.) -/
theorem isAbsoluteLeftKanExtension_iff {F : C ⥤ D} {E : C ⥤ U} (T : D ⥤ U) (η : E ⟶ F ⋙ T) :
    IsAbsoluteLeftKanExtension.{w, w'} T η ↔ T.IsLeftKanExtension η ∧
      ∀ (V : Type w) [Category.{w'} V] (H : U ⥤ V) (K : D ⥤ V) (θ : E ⋙ H ⟶ F ⋙ K),
        ∃! τ : T ⋙ H ⟶ K,
          θ = whiskerRight η H ≫ (Functor.associator F T H).hom ≫ whiskerLeft F τ := by
  refine and_congr_right fun _ ↦ forall_congr' fun V ↦ forall_congr' fun _ ↦
    forall_congr' fun H ↦ ?_
  rw [CommutesWith, isLeftKanExtension_iff]
  exact forall₂_congr fun K θ ↦ existsUnique_congr fun τ ↦ by rw [Category.assoc]

section AdjunctionKan

variable {F : C ⥤ D} {G : D ⥤ C}

/-- For `F ⊣ G` and any `H : C → V`, every `θ : H ⇒ KF` factors uniquely through `Hη` as
`τF ∘ Hη`, with `τ := Kε ∘ θG`. -/
theorem adjunction_commutesWith (adj : F ⊣ G) {V : Type*} [Category V] (H : C ⥤ V) :
    CommutesWith H G adj.unit := by
  rw [CommutesWith, isLeftKanExtension_iff]
  intro K θ
  refine ⟨
    { app := fun d ↦ θ.app (G.obj d) ≫ K.map (adj.counit.app d)
      naturality := fun d d' g ↦ ?_ }, ?_, fun τ hτ ↦ ?_⟩
  · have h1 := θ.naturality (G.map g)
    dsimp at h1 ⊢
    rw [reassoc_of% h1]
    simp only [Category.assoc, ← K.map_comp, adj.counit_naturality]
  · ext c
    have h1 := θ.naturality (adj.unit.app c)
    dsimp at h1 ⊢
    simp only [Category.comp_id]
    rw [reassoc_of% h1, ← K.map_comp, adj.left_triangle_components, K.map_id, Category.comp_id]
  · ext d
    have h2 := congrArg (fun α ↦ NatTrans.app α (G.obj d)) hτ
    have h3 := τ.naturality (adj.counit.app d)
    dsimp at h2 h3 ⊢
    rw [h2]
    simp only [Category.comp_id, Category.assoc]
    rw [← h3, ← H.map_comp_assoc, adj.right_triangle_components, H.map_id, Category.id_comp]

/-- For `F ⊣ G`, `⟨G, η⟩` is a left Kan extension of `id_C` along `F`. -/
theorem adjunction_isLeftKanExtension (adj : F ⊣ G) : G.IsLeftKanExtension adj.unit := by
  rw [isLeftKanExtension_iff]
  intro K θ
  refine ⟨
    { app := fun d ↦ θ.app (G.obj d) ≫ K.map (adj.counit.app d)
      naturality := fun d d' g ↦ ?_ }, ?_, fun τ hτ ↦ ?_⟩
  · have h1 := θ.naturality (G.map g)
    dsimp at h1 ⊢
    rw [reassoc_of% h1]
    simp only [Category.assoc, ← K.map_comp, adj.counit_naturality]
  · ext c
    have h1 := θ.naturality (adj.unit.app c)
    dsimp at h1 ⊢
    rw [reassoc_of% h1, ← K.map_comp, adj.left_triangle_components, K.map_id, Category.comp_id]
  · ext d
    have h2 := congrArg (fun α ↦ NatTrans.app α (G.obj d)) hτ
    have h3 := τ.naturality (adj.counit.app d)
    dsimp at h2 h3 ⊢
    rw [h2, Category.assoc, ← h3, ← Category.assoc, adj.right_triangle_components,
      Category.id_comp]

/-- For `F ⊣ G`, `⟨G, η⟩` is an absolute left Kan extension of `id_C` along `F`, for test
categories in any universes. -/
theorem adjunction_isAbsoluteLeftKanExtension (adj : F ⊣ G) :
    IsAbsoluteLeftKanExtension.{w, w'} G adj.unit :=
  ⟨adjunction_isLeftKanExtension adj, fun _ _ H ↦ adjunction_commutesWith adj H⟩

/-- If `⟨G, η⟩` is a left Kan extension of `id_C` along `F` and `F` commutes with it, then
`F ⊣ G` with unit `η`. -/
theorem adjunction_of_commutesWith (G : D ⥤ C) (η : 𝟭 C ⟶ F ⋙ G) (hG : G.IsLeftKanExtension η)
    (hF : CommutesWith F G η) : ∃ adj : F ⊣ G, adj.unit = η := by
  rw [CommutesWith, isLeftKanExtension_iff] at hF
  obtain ⟨ε, hε, -⟩ := hF (𝟭 D) ((Functor.leftUnitor F).hom ≫ (Functor.rightUnitor F).inv)
  have left : ∀ c, F.map (η.app c) ≫ ε.app (F.obj c) = 𝟙 _ := fun c ↦ by
    have := congrArg (fun α ↦ NatTrans.app α c) hε
    dsimp at this
    simpa using this.symm
  rw [isLeftKanExtension_iff] at hG
  obtain ⟨σ, -, hσ⟩ := hG G η
  let ρ : G ⟶ G := (Functor.rightUnitor G).inv ≫ whiskerLeft G η ≫
    (Functor.associator G F G).inv ≫ whiskerRight ε G ≫ (Functor.leftUnitor G).hom
  have hρ : ρ = σ := hσ ρ (by
    ext c
    have h1 := η.naturality (η.app c)
    dsimp [ρ] at h1 ⊢
    simp only [Category.id_comp, Category.comp_id]
    rw [reassoc_of% h1, ← G.map_comp, left]
    simp)
  have h1 : 𝟙 G = σ := hσ (𝟙 G) (by ext; simp)
  have right : ∀ d, η.app (G.obj d) ≫ G.map (ε.app d) = 𝟙 _ := fun d ↦ by
    have := congrArg (fun α ↦ NatTrans.app α d) (hρ.trans h1.symm)
    dsimp [ρ] at this
    simpa using this
  exact ⟨
    { unit := η
      counit := ε
      left_triangle_components := left
      right_triangle_components := right }, rfl⟩

/-- `ALGD-C2-KAN-17`, `ALGD-C2-AFT-01` (定理 17, p.19–20; restated as `aft.pdf` 定理 1, p.1–2).
For `F : C → D` the following are equivalent: (1) `F` is a left adjoint; (2) an absolute left
Kan extension `⟨F† id_C, η⟩` of `id_C` along `F` exists; (3) a left Kan extension
`⟨F† id_C, η⟩` exists and `F` commutes with it. In that case `F ⊣ F† id_C` with unit `η`.
In (2) the test categories range over the universes of `D`, which is what (2) ⇒ (3) uses; (1)
gives absoluteness in every universe (`adjunction_isAbsoluteLeftKanExtension`). -/
theorem isLeftAdjoint_tfae (F : C ⥤ D) :
    List.TFAE [F.IsLeftAdjoint,
      ∃ (G : D ⥤ C) (η : 𝟭 C ⟶ F ⋙ G), IsAbsoluteLeftKanExtension.{u₂, v₂} G η,
      ∃ (G : D ⥤ C) (η : 𝟭 C ⟶ F ⋙ G), G.IsLeftKanExtension η ∧ CommutesWith F G η] ∧
    ∀ (G : D ⥤ C) (η : 𝟭 C ⟶ F ⋙ G), G.IsLeftKanExtension η → CommutesWith F G η →
      ∃ adj : F ⊣ G, adj.unit = η := by
  refine ⟨?_, adjunction_of_commutesWith⟩
  tfae_have 1 → 2 := fun _ ↦ ⟨F.rightAdjoint, (Adjunction.ofIsLeftAdjoint F).unit,
    adjunction_isAbsoluteLeftKanExtension _⟩
  tfae_have 2 → 3 := fun ⟨G, η, h⟩ ↦ ⟨G, η, h.1, h.2 D F⟩
  tfae_have 3 → 1 := fun ⟨G, η, h1, h2⟩ ↦
    (adjunction_of_commutesWith G η h1 h2).choose.isLeftAdjoint
  tfae_finish

end AdjunctionKan

/-- `ALGD-C2-KAN-18` (系 18, p.20–21).
A category `C` has a terminal object iff `colim(id_C)` exists, and then `colim(id_C) ≅ 1`. The
source derives this from 定理 17, since a terminal object is a right adjoint of `C → 1`; here it
is proved directly. -/
theorem hasTerminal_iff_hasColimit_id :
    (HasTerminal C ↔ HasColimit (𝟭 C)) ∧
    ∀ [HasTerminal C] [HasColimit (𝟭 C)], Nonempty (colimit (𝟭 C) ≅ ⊤_ C) := by
  refine ⟨⟨fun _ ↦ ⟨⟨⟨_, colimitOfDiagramTerminal terminalIsTerminal (𝟭 C)⟩⟩⟩, fun _ ↦ ?_⟩,
    ⟨colimit.isoColimitCocone ⟨_, colimitOfDiagramTerminal terminalIsTerminal (𝟭 C)⟩⟩⟩
  have hid : colimit.ι (𝟭 C) (colimit (𝟭 C)) = 𝟙 (colimit (𝟭 C)) :=
    colimit.hom_ext fun X ↦ by
      erw [Category.comp_id]
      exact colimit.w (𝟭 C) (colimit.ι (𝟭 C) X)
  refine IsTerminal.hasTerminal (X := colimit (𝟭 C))
    (IsTerminal.ofUniqueHom (fun X ↦ colimit.ι (𝟭 C) X) fun X f ↦ ?_)
  rw [← Category.comp_id f, ← hid]
  exact colimit.w (𝟭 C) f

/-- `ALGD-C2-KAN-19`, `ALGD-C2-AFT-02` (命題 19, p.21; restated as `aft.pdf` 命題 2, p.2).
If `J` has a terminal object `1`, every `T : J → C` has a colimit and `colim T ≅ T(1)`. -/
theorem colimit_of_terminal {J : Type u₄} [Category.{v₄} J] (T : J ⥤ C) {t : J}
    (ht : IsTerminal t) : HasColimit T ∧ ∀ [HasColimit T], Nonempty (colimit T ≅ T.obj t) :=
  ⟨⟨⟨⟨_, colimitOfDiagramTerminal ht T⟩⟩⟩,
    ⟨colimit.isoColimitCocone ⟨_, colimitOfDiagramTerminal ht T⟩⟩⟩

/-- `K : U → V` commutes with a right Kan extension `⟨T, ε⟩` when `⟨K ∘ T, Kε⟩` is a right
Kan extension of `KE` along `F`. -/
def CommutesWithRight {V : Type u₄} [Category.{v₄} V] (K : U ⥤ V) {F : C ⥤ D} {E : C ⥤ U}
    (T : D ⥤ U) (ε : F ⋙ T ⟶ E) : Prop :=
  (T ⋙ K).IsRightKanExtension ((Functor.associator F T K).inv ≫ whiskerRight ε K)

/-- `ALGD-C2-KAN-D08` (prose before 定理 20, p.21).
Absolute right Kan extensions and absolute Kan lifts are defined like absolute left Kan
extensions. An absolute right Kan extension is a right Kan extension `⟨T, ε⟩` that commutes with
every `H : U → V` (`CommutesWithRight`). For Kan lifts the test functors act by precomposition:
an absolute left (right) Kan lift `⟨L, η⟩` of `E : X → U` along `F` is one such that
`⟨LH, ηH⟩` is again a left (right) Kan lift of `EH` for every `H : Y → X`
(`IsAbsoluteLeftKanLift`, `IsAbsoluteRightKanLift`), as for `Bicategory.LeftLift.IsAbsKan`. -/
def IsAbsoluteRightKanExtension {F : C ⥤ D} {E : C ⥤ U} (T : D ⥤ U) (ε : F ⋙ T ⟶ E) : Prop :=
  T.IsRightKanExtension ε ∧ ∀ (V : Type w) [Category.{w'} V] (H : U ⥤ V), CommutesWithRight H T ε

/-- An absolute left Kan lift: a left Kan lift `⟨L, η⟩` of `E` along `F` such that `⟨LH, ηH⟩` is
a left Kan lift of `EH` along `F` for every `H : Y → X` (part of `ALGD-C2-KAN-D08`). -/
def IsAbsoluteLeftKanLift {X : Type u₄} [Category.{v₄} X] (F : D ⥤ U) {E : X ⥤ U} (L : X ⥤ D)
    (η : E ⟶ L ⋙ F) : Prop :=
  IsLeftKanLift F L η ∧ ∀ (Y : Type w) [Category.{w'} Y] (H : Y ⥤ X),
    IsLeftKanLift F (H ⋙ L) (whiskerLeft H η ≫ (Functor.associator H L F).inv)

/-- An absolute right Kan lift: a right Kan lift `⟨R, ε⟩` of `E` along `F` such that `⟨RH, εH⟩`
is a right Kan lift of `EH` along `F` for every `H : Y → X` (part of `ALGD-C2-KAN-D08`). -/
def IsAbsoluteRightKanLift {X : Type u₄} [Category.{v₄} X] (F : D ⥤ U) {E : X ⥤ U} (R : X ⥤ D)
    (ε : R ⋙ F ⟶ E) : Prop :=
  IsRightKanLift F R ε ∧ ∀ (Y : Type w) [Category.{w'} Y] (H : Y ⥤ X),
    IsRightKanLift F (H ⋙ R) ((Functor.associator H R F).hom ≫ whiskerLeft H ε)

section AdjunctionKan2

variable {F : C ⥤ D} {G : D ⥤ C}

/-- For `F ⊣ G` and any `H : D → V`, `⟨HF, Hε⟩` is a right Kan extension of `H` along `G`. -/
theorem adjunction_commutesWithRight (adj : F ⊣ G) {V : Type*} [Category V] (H : D ⥤ V) :
    CommutesWithRight H F adj.counit := by
  rw [CommutesWithRight, isRightKanExtension_iff]
  intro K θ
  refine ⟨
    { app := fun c ↦ K.map (adj.unit.app c) ≫ θ.app (F.obj c)
      naturality := fun c c' g ↦ ?_ }, ?_, fun τ hτ ↦ ?_⟩
  · have h1 := θ.naturality (F.map g)
    dsimp at h1 ⊢
    rw [Category.assoc, ← h1, ← K.map_comp_assoc, ← K.map_comp_assoc, adj.unit_naturality]
  · ext d
    have h1 := θ.naturality (adj.counit.app d)
    dsimp at h1 ⊢
    simp only [Category.id_comp, Category.assoc]
    rw [← h1, ← K.map_comp_assoc, adj.right_triangle_components, K.map_id, Category.id_comp]
  · ext c
    have h2 := congrArg (fun α ↦ NatTrans.app α (F.obj c)) hτ
    have h3 := τ.naturality (adj.unit.app c)
    dsimp at h2 h3 ⊢
    rw [h2]
    simp only [Category.id_comp]
    rw [reassoc_of% h3, ← H.map_comp, adj.left_triangle_components, H.map_id, Category.comp_id]

/-- For `F ⊣ G`, `⟨F, ε⟩` is a right Kan extension of `id_D` along `G`. -/
theorem adjunction_isRightKanExtension (adj : F ⊣ G) : F.IsRightKanExtension adj.counit := by
  rw [isRightKanExtension_iff]
  intro K θ
  refine ⟨
    { app := fun c ↦ K.map (adj.unit.app c) ≫ θ.app (F.obj c)
      naturality := fun c c' g ↦ ?_ }, ?_, fun τ hτ ↦ ?_⟩
  · have h1 := θ.naturality (F.map g)
    dsimp at h1 ⊢
    rw [Category.assoc, ← h1, ← K.map_comp_assoc, ← K.map_comp_assoc, adj.unit_naturality]
  · ext d
    have h1 := θ.naturality (adj.counit.app d)
    dsimp at h1 ⊢
    rw [Category.assoc, ← h1, ← K.map_comp_assoc, adj.right_triangle_components, K.map_id,
      Category.id_comp]
  · ext c
    have h2 := congrArg (fun α ↦ NatTrans.app α (F.obj c)) hτ
    have h3 := τ.naturality (adj.unit.app c)
    dsimp at h2 h3 ⊢
    rw [h2, reassoc_of% h3, adj.left_triangle_components, Category.comp_id]

/-- If `⟨T, ε⟩` is a right Kan extension of `id_D` along `G` and `G` commutes with it, then
`T ⊣ G` with counit `ε`. -/
theorem adjunction_of_commutesWithRight (T : C ⥤ D) (ε : G ⋙ T ⟶ 𝟭 D)
    (hT : T.IsRightKanExtension ε) (hG : CommutesWithRight G T ε) :
    ∃ adj : T ⊣ G, adj.counit = ε := by
  rw [CommutesWithRight, isRightKanExtension_iff] at hG
  obtain ⟨η, hη, -⟩ := hG (𝟭 C) ((Functor.rightUnitor G).hom ≫ (Functor.leftUnitor G).inv)
  have right : ∀ d, η.app (G.obj d) ≫ G.map (ε.app d) = 𝟙 _ := fun d ↦ by
    have := congrArg (fun α ↦ NatTrans.app α d) hη
    dsimp at this
    simpa using this.symm
  rw [isRightKanExtension_iff] at hT
  obtain ⟨σ, -, hσ⟩ := hT T ε
  let ρ : T ⟶ T := (Functor.leftUnitor T).inv ≫ whiskerRight η T ≫
    (Functor.associator T G T).hom ≫ whiskerLeft T ε ≫ (Functor.rightUnitor T).hom
  have hρ : ρ = σ := hσ ρ (by
    ext d
    have h1 := ε.naturality (ε.app d)
    dsimp [ρ] at h1 ⊢
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    rw [← h1, ← T.map_comp_assoc, right]
    simp)
  have h1 : 𝟙 T = σ := hσ (𝟙 T) (by ext; simp)
  have left : ∀ c, T.map (η.app c) ≫ ε.app (T.obj c) = 𝟙 _ := fun c ↦ by
    have := congrArg (fun α ↦ NatTrans.app α c) (hρ.trans h1.symm)
    dsimp [ρ] at this
    simpa using this
  exact ⟨
    { unit := η
      counit := ε
      left_triangle_components := left
      right_triangle_components := right }, rfl⟩

/-- `ALGD-C2-KAN-20` (定理 20, p.21–22).
For `G : D → C` the following are equivalent: (1) `G` is a right adjoint; (2) an absolute right
Kan extension `⟨G‡ id_D, ε⟩` of `id_D` along `G` exists; (3) a right Kan extension
`⟨G‡ id_D, ε⟩` exists and `G` commutes with it. In that case `G‡ id_D ⊣ G` with counit `ε`.
The source omits the proof as similar to 定理 17. -/
theorem isRightAdjoint_tfae (G : D ⥤ C) :
    List.TFAE [G.IsRightAdjoint,
      ∃ (T : C ⥤ D) (ε : G ⋙ T ⟶ 𝟭 D), IsAbsoluteRightKanExtension.{u₁, v₁} T ε,
      ∃ (T : C ⥤ D) (ε : G ⋙ T ⟶ 𝟭 D), T.IsRightKanExtension ε ∧ CommutesWithRight G T ε] ∧
    ∀ (T : C ⥤ D) (ε : G ⋙ T ⟶ 𝟭 D), T.IsRightKanExtension ε → CommutesWithRight G T ε →
      ∃ adj : T ⊣ G, adj.counit = ε := by
  refine ⟨?_, adjunction_of_commutesWithRight⟩
  tfae_have 1 → 2 := fun _ ↦ ⟨G.leftAdjoint, (Adjunction.ofIsRightAdjoint G).counit,
    adjunction_isRightKanExtension _, fun _ _ H ↦ adjunction_commutesWithRight _ H⟩
  tfae_have 2 → 3 := fun ⟨T, ε, h⟩ ↦ ⟨T, ε, h.1, h.2 C G⟩
  tfae_have 3 → 1 := fun ⟨T, ε, h1, h2⟩ ↦
    (adjunction_of_commutesWithRight T ε h1 h2).choose.isRightAdjoint
  tfae_finish

/-- For `F ⊣ G` and any `H : Y → D`, `⟨GH, εH⟩` is a right Kan lift of `H` along `F`. -/
theorem adjunction_isRightKanLift_comp (adj : F ⊣ G) {Y : Type*} [Category Y] (H : Y ⥤ D) :
    IsRightKanLift F (H ⋙ G) ((Functor.associator H G F).hom ≫ whiskerLeft H adj.counit) := by
  intro S θ
  refine ⟨
    { app := fun y ↦ adj.unit.app (S.obj y) ≫ G.map (θ.app y)
      naturality := fun y y' g ↦ ?_ }, ?_, fun τ hτ ↦ ?_⟩
  · have h1 := θ.naturality g
    dsimp at h1 ⊢
    rw [← adj.unit_naturality_assoc, ← G.map_comp, h1, G.map_comp, Category.assoc]
  · ext y
    dsimp
    simp only [Category.id_comp, F.map_comp, Category.assoc, adj.counit_naturality]
    rw [adj.left_triangle_components_assoc]
  · ext y
    have h2 := congrArg (fun α ↦ NatTrans.app α y) hτ
    dsimp at h2 ⊢
    rw [h2, Category.id_comp, G.map_comp, adj.unit_naturality_assoc,
      adj.right_triangle_components, Category.comp_id]

/-- For `F ⊣ G`, `⟨G, ε⟩` is a right Kan lift of `id_D` along `F`. -/
theorem adjunction_isRightKanLift (adj : F ⊣ G) : IsRightKanLift F G adj.counit := by
  intro S θ
  refine ⟨
    { app := fun d ↦ adj.unit.app (S.obj d) ≫ G.map (θ.app d)
      naturality := fun d d' g ↦ ?_ }, ?_, fun τ hτ ↦ ?_⟩
  · have h1 := θ.naturality g
    dsimp at h1 ⊢
    rw [← adj.unit_naturality_assoc, ← G.map_comp, h1, G.map_comp, Category.assoc]
  · ext d
    dsimp
    simp only [F.map_comp, Category.assoc, adj.counit_naturality]
    rw [adj.left_triangle_components_assoc]
  · ext d
    have h2 := congrArg (fun α ↦ NatTrans.app α d) hτ
    dsimp at h2 ⊢
    rw [h2, G.map_comp, adj.unit_naturality_assoc, adj.right_triangle_components,
      Category.comp_id]

/-- If `⟨R, ε⟩` is a right Kan lift of `id_D` along `F` and `F` commutes with it, then `F ⊣ R`
with counit `ε`. -/
theorem adjunction_of_isRightKanLift (R : D ⥤ C) (ε : R ⋙ F ⟶ 𝟭 D) (hR : IsRightKanLift F R ε)
    (hF : IsRightKanLift F (F ⋙ R) ((Functor.associator F R F).hom ≫ whiskerLeft F ε)) :
    ∃ adj : F ⊣ R, adj.counit = ε := by
  obtain ⟨η, hη, -⟩ := hF (𝟭 C) ((Functor.leftUnitor F).hom ≫ (Functor.rightUnitor F).inv)
  have left : ∀ c, F.map (η.app c) ≫ ε.app (F.obj c) = 𝟙 _ := fun c ↦ by
    have := congrArg (fun α ↦ NatTrans.app α c) hη
    dsimp at this
    simpa using this.symm
  obtain ⟨σ, -, hσ⟩ := hR R ε
  let ρ : R ⟶ R := (Functor.rightUnitor R).inv ≫ whiskerLeft R η ≫
    (Functor.associator R F R).inv ≫ whiskerRight ε R ≫ (Functor.leftUnitor R).hom
  have hρ : ρ = σ := hσ ρ (by
    ext d
    have h1 := ε.naturality (ε.app d)
    dsimp [ρ] at h1 ⊢
    simp only [Category.id_comp, Category.comp_id, F.map_comp, Category.assoc]
    rw [h1, reassoc_of% (left (R.obj d))])
  have h1 : 𝟙 R = σ := hσ (𝟙 R) (by ext; simp)
  have right : ∀ d, η.app (R.obj d) ≫ R.map (ε.app d) = 𝟙 _ := fun d ↦ by
    have := congrArg (fun α ↦ NatTrans.app α d) (hρ.trans h1.symm)
    dsimp [ρ] at this
    simpa using this
  exact ⟨
    { unit := η
      counit := ε
      left_triangle_components := left
      right_triangle_components := right }, rfl⟩

/-- `ALGD-C2-KAN-21` (定理 21, p.22).
For `F : C → D` the following are equivalent: (1) `F` is a left adjoint; (2) an absolute right
Kan lift `⟨F‡ id_D, ε⟩` of `id_D` along `F` exists; (3) a right Kan lift `⟨F‡ id_D, ε⟩` exists
and `F` commutes with it (precomposing with `F` gives a right Kan lift of `F`). In that case
`F ⊣ F‡ id_D` with counit `ε`. The source omits the proof as similar to 定理 17. -/
theorem isLeftAdjoint_tfae_kanLift (F : C ⥤ D) :
    List.TFAE [F.IsLeftAdjoint,
      ∃ (R : D ⥤ C) (ε : R ⋙ F ⟶ 𝟭 D), IsAbsoluteRightKanLift.{u₁, v₁} F R ε,
      ∃ (R : D ⥤ C) (ε : R ⋙ F ⟶ 𝟭 D), IsRightKanLift F R ε ∧
        IsRightKanLift F (F ⋙ R) ((Functor.associator F R F).hom ≫ whiskerLeft F ε)] ∧
    ∀ (R : D ⥤ C) (ε : R ⋙ F ⟶ 𝟭 D), IsRightKanLift F R ε →
      IsRightKanLift F (F ⋙ R) ((Functor.associator F R F).hom ≫ whiskerLeft F ε) →
      ∃ adj : F ⊣ R, adj.counit = ε := by
  refine ⟨?_, adjunction_of_isRightKanLift⟩
  tfae_have 1 → 2 := fun _ ↦ ⟨F.rightAdjoint, (Adjunction.ofIsLeftAdjoint F).counit,
    adjunction_isRightKanLift _, fun _ _ H ↦ adjunction_isRightKanLift_comp _ H⟩
  tfae_have 2 → 3 := fun ⟨R, ε, h⟩ ↦ ⟨R, ε, h.1, h.2 C F⟩
  tfae_have 3 → 1 := fun ⟨R, ε, h1, h2⟩ ↦
    (adjunction_of_isRightKanLift R ε h1 h2).choose.isLeftAdjoint
  tfae_finish

/-- For `F ⊣ G` and any `H : Y → C`, `⟨FH, ηH⟩` is a left Kan lift of `H` along `G`. -/
theorem adjunction_isLeftKanLift_comp (adj : F ⊣ G) {Y : Type*} [Category Y] (H : Y ⥤ C) :
    IsLeftKanLift G (H ⋙ F) (whiskerLeft H adj.unit ≫ (Functor.associator H F G).inv) := by
  intro S θ
  refine ⟨
    { app := fun y ↦ F.map (θ.app y) ≫ adj.counit.app (S.obj y)
      naturality := fun y y' g ↦ ?_ }, ?_, fun τ hτ ↦ ?_⟩
  · have h1 := θ.naturality g
    dsimp at h1 ⊢
    rw [← F.map_comp_assoc, h1, F.map_comp, Category.assoc, Category.assoc,
      adj.counit_naturality]
  · ext y
    dsimp
    simp only [Category.comp_id, G.map_comp]
    rw [adj.unit_naturality_assoc, adj.right_triangle_components, Category.comp_id]
  · ext y
    have h2 := congrArg (fun α ↦ NatTrans.app α y) hτ
    dsimp at h2 ⊢
    rw [h2, Category.comp_id, F.map_comp, Category.assoc, adj.counit_naturality,
      adj.left_triangle_components_assoc]

/-- For `F ⊣ G`, `⟨F, η⟩` is a left Kan lift of `id_C` along `G`. -/
theorem adjunction_isLeftKanLift (adj : F ⊣ G) : IsLeftKanLift G F adj.unit := by
  intro S θ
  refine ⟨
    { app := fun c ↦ F.map (θ.app c) ≫ adj.counit.app (S.obj c)
      naturality := fun c c' g ↦ ?_ }, ?_, fun τ hτ ↦ ?_⟩
  · have h1 := θ.naturality g
    dsimp at h1 ⊢
    rw [← F.map_comp_assoc, h1, F.map_comp, Category.assoc, Category.assoc,
      adj.counit_naturality]
  · ext c
    dsimp
    rw [G.map_comp, adj.unit_naturality_assoc, adj.right_triangle_components, Category.comp_id]
  · ext c
    have h2 := congrArg (fun α ↦ NatTrans.app α c) hτ
    dsimp at h2 ⊢
    rw [h2, F.map_comp, Category.assoc, adj.counit_naturality,
      adj.left_triangle_components_assoc]

/-- If `⟨L, η⟩` is a left Kan lift of `id_C` along `G` and `G` commutes with it, then `L ⊣ G`
with unit `η`. -/
theorem adjunction_of_isLeftKanLift (L : C ⥤ D) (η : 𝟭 C ⟶ L ⋙ G) (hL : IsLeftKanLift G L η)
    (hG : IsLeftKanLift G (G ⋙ L) (whiskerLeft G η ≫ (Functor.associator G L G).inv)) :
    ∃ adj : L ⊣ G, adj.unit = η := by
  obtain ⟨ε, hε, -⟩ := hG (𝟭 D) ((Functor.rightUnitor G).hom ≫ (Functor.leftUnitor G).inv)
  have right : ∀ d, η.app (G.obj d) ≫ G.map (ε.app d) = 𝟙 _ := fun d ↦ by
    have := congrArg (fun α ↦ NatTrans.app α d) hε
    dsimp at this
    simpa using this.symm
  obtain ⟨σ, -, hσ⟩ := hL L η
  let ρ : L ⟶ L := (Functor.leftUnitor L).inv ≫ whiskerRight η L ≫
    (Functor.associator L G L).hom ≫ whiskerLeft L ε ≫ (Functor.rightUnitor L).hom
  have hρ : ρ = σ := hσ ρ (by
    ext c
    have h1 := η.naturality (η.app c)
    dsimp [ρ] at h1 ⊢
    simp only [Category.id_comp, Category.comp_id, G.map_comp]
    rw [← reassoc_of% h1, right]
    simp)
  have h1 : 𝟙 L = σ := hσ (𝟙 L) (by ext; simp)
  have left : ∀ c, L.map (η.app c) ≫ ε.app (L.obj c) = 𝟙 _ := fun c ↦ by
    have := congrArg (fun α ↦ NatTrans.app α c) (hρ.trans h1.symm)
    dsimp [ρ] at this
    simpa using this
  exact ⟨
    { unit := η
      counit := ε
      left_triangle_components := left
      right_triangle_components := right }, rfl⟩

/-- `ALGD-C2-KAN-22` (定理 22, p.22).
For `G : D → C` the following are equivalent: (1) `G` is a right adjoint; (2) an absolute left
Kan lift `⟨G† id_C, η⟩` of `id_C` along `G` exists; (3) a left Kan lift `⟨G† id_C, η⟩` exists
and `G` commutes with it. In that case `G† id_C ⊣ G` with unit `η`. The source omits the proof
as similar to 定理 17. -/
theorem isRightAdjoint_tfae_kanLift (G : D ⥤ C) :
    List.TFAE [G.IsRightAdjoint,
      ∃ (L : C ⥤ D) (η : 𝟭 C ⟶ L ⋙ G), IsAbsoluteLeftKanLift.{u₂, v₂} G L η,
      ∃ (L : C ⥤ D) (η : 𝟭 C ⟶ L ⋙ G), IsLeftKanLift G L η ∧
        IsLeftKanLift G (G ⋙ L) (whiskerLeft G η ≫ (Functor.associator G L G).inv)] ∧
    ∀ (L : C ⥤ D) (η : 𝟭 C ⟶ L ⋙ G), IsLeftKanLift G L η →
      IsLeftKanLift G (G ⋙ L) (whiskerLeft G η ≫ (Functor.associator G L G).inv) →
      ∃ adj : L ⊣ G, adj.unit = η := by
  refine ⟨?_, adjunction_of_isLeftKanLift⟩
  tfae_have 1 → 2 := fun _ ↦ ⟨G.leftAdjoint, (Adjunction.ofIsRightAdjoint G).unit,
    adjunction_isLeftKanLift _, fun _ _ H ↦ adjunction_isLeftKanLift_comp _ H⟩
  tfae_have 2 → 3 := fun ⟨L, η, h⟩ ↦ ⟨L, η, h.1, h.2 D G⟩
  tfae_have 3 → 1 := fun ⟨L, η, h1, h2⟩ ↦
    (adjunction_of_isLeftKanLift L η h1 h2).choose.isRightAdjoint
  tfae_finish

end AdjunctionKan2

/-- `ALGD-C2-KAN-23` (定理 23, p.22–25).
Left adjoints commute with left Kan extensions: if `L ⊣ R : U → V` and `⟨T, η⟩` is a left Kan
extension of `E` along `F`, then `⟨L ∘ T, Lη⟩` is a left Kan extension of `LE` along `F`. -/
theorem leftAdjoint_commutesWith {V : Type u₄} [Category.{v₄} V] (K : U ⥤ V) [K.IsLeftAdjoint]
    {F : C ⥤ D} {E : C ⥤ U} (T : D ⥤ U) (η : E ⟶ F ⋙ T) [T.IsLeftKanExtension η] :
    CommutesWith K T η :=
  (commutesWith_iff_preserves K T η).2 inferInstance

/-! ## §4 The Yoneda embedding and Kan extensions -/

/-- `ALGD-C2-KAN-29` (系 29, p.33).
`y † y ≅ id_Ĉ`: the left Kan extension of the Yoneda embedding along itself exists and is
isomorphic to the identity. The source assumes `C` small; this holds for any locally small `C`,
with `Ĉ = C^op → Type v₁`. -/
theorem yoneda_lan_yoneda :
    yoneda.HasLeftKanExtension (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁) ∧
    Nonempty (yoneda.leftKanExtension (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁) ≅ 𝟭 _) :=
  ⟨inferInstance, ⟨IsDense.leftKanExtensionIso yoneda⟩⟩

/-- `ALGD-C2-KAN-R05` (※ after 系 29, p.33).
`⟨id_Ĉ, id_y⟩` is a left Kan extension of `y` along `y`, and it is pointwise. -/
theorem yoneda_isLeftKanExtension_id :
    (𝟭 (Cᵒᵖ ⥤ Type v₁)).IsLeftKanExtension (Functor.rightUnitor (yoneda : C ⥤ _)).inv ∧
    Nonempty (LeftExtension.mk (𝟭 (Cᵒᵖ ⥤ Type v₁))
      (Functor.rightUnitor (yoneda : C ⥤ _)).inv).IsPointwiseLeftKanExtension :=
  ⟨inferInstance, (isDense_iff_nonempty_isPointwiseLeftKanExtension yoneda).1 inferInstance⟩

/-- `ALGD-C2-KAN-30` (系 30, p.33–34).
Every presheaf `P` on a small category `C` is a colimit of representables: there are a small
`J` and `T : J → C` with `P ≅ colim(J → C → Ĉ)`. As in the source's proof, `J = y ↓ P` and the
colimit cocone is the tautological one (`Presheaf.isColimitTautologicalCocone`). -/
theorem presheaf_colimit_of_representables {C : Type v} [SmallCategory C] (P : Cᵒᵖ ⥤ Type v) :
    ∃ (J : Type v) (_ : SmallCategory J) (T : J ⥤ C) (c : Cocone (T ⋙ yoneda)),
      Nonempty (IsColimit c) ∧ c.pt = P :=
  ⟨CostructuredArrow yoneda P, inferInstance, CostructuredArrow.proj yoneda P,
    Presheaf.tautologicalCocone P, ⟨Presheaf.isColimitTautologicalCocone P⟩, rfl⟩

/-- `ALGD-C2-KAN-31` (補題 31, p.34).
If `F : C → D` is fully faithful and `f : F c ≅ d`, then `F ↓ d` has a terminal object, namely
`⟨c, f⟩`. -/
theorem costructuredArrow_mk_isTerminal {F : C ⥤ D} [F.Full] [F.Faithful] {c : C} {d : D}
    (f : F.obj c ≅ d) :
    Nonempty (IsTerminal (CostructuredArrow.mk f.hom : CostructuredArrow F d)) := by
  rw [costructuredArrow_isTerminal_iff]
  intro c' g
  refine ⟨F.preimage (g ≫ f.inv), by simp, fun h hh ↦ F.map_injective ?_⟩
  rw [F.map_preimage, ← hh, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `ALGD-C2-KAN-32` (命題 32, p.34).
A presheaf `P ∈ Ĉ` is representable iff the comma category `y ↓ P` has a terminal object. -/
theorem isRepresentable_iff_hasTerminal (P : Cᵒᵖ ⥤ Type v₁) :
    P.IsRepresentable ↔ HasTerminal (CostructuredArrow yoneda P) := by
  constructor
  · rintro ⟨X, ⟨r⟩⟩
    obtain ⟨t⟩ := costructuredArrow_mk_isTerminal (F := yoneda) r.toIso
    exact t.hasTerminal
  · intro _
    let t := ⊤_ (CostructuredArrow yoneda P)
    let e : P ≅ yoneda.obj t.left :=
      (Presheaf.isColimitTautologicalCocone P).coconePointUniqueUpToIso
        (colimitOfDiagramTerminal terminalIsTerminal _)
    exact ⟨t.left, ⟨Functor.representableByEquiv.symm e.symm⟩⟩

/-- `ALGD-C2-KAN-34` (定理 34, p.35).
For `F : C → D`, `F† ∘ y ≅ y ∘ F : C → D̂`; in particular `F† (Hom_C(−, a)) ≅ Hom_D(−, F a)`,
so left Kan extensions of representables are representable. The second statement is mathlib's
instance: `Hom_D(−, F a)` with the maps `f ↦ F f` is a left Kan extension of `Hom_C(−, a)`
along `F^op`. The bundled form needs every left Kan extension along `F^op` to exist, which holds
for small `C` (系 6). -/
theorem lan_yoneda {D : Type u₂} [Category.{v₁} D] (F : C ⥤ D) :
    (∀ a : C, (yoneda.obj (F.obj a)).IsLeftKanExtension (yonedaMap F a)) ∧
    ∀ [∀ P : Cᵒᵖ ⥤ Type v₁, F.op.HasLeftKanExtension P],
      Nonempty (yoneda ⋙ F.op.lan ≅ F ⋙ yoneda) :=
  ⟨fun _ ↦ inferInstance, ⟨isoWhiskerRight uliftYonedaIsoYoneda.symm _ ≪≫
    (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{v₁} F).symm ≪≫
    isoWhiskerLeft F uliftYonedaIsoYoneda⟩⟩

/-- `ALGD-C2-KAN-36` (定理 36, p.35–36).
If `⟨F † E, η⟩` is a pointwise left Kan extension and `F` is fully faithful, then `η` is a
natural isomorphism, so `F † E` extends the domain of `E`. -/
theorem unit_isIso_of_fullyFaithful {F : C ⥤ D} [F.Full] [F.Faithful] {E : C ⥤ U} {T : D ⥤ U}
    {η : E ⟶ F ⋙ T} (h : (LeftExtension.mk T η).IsPointwiseLeftKanExtension) : IsIso η :=
  h.isIso_hom

/-- `ALGD-C2-KAN-D10` (定義 (2), p.38).
`F : C → D` is dense iff `⟨id_D, id_F⟩` is a pointwise left Kan extension of `F` along `F`. This
is mathlib's `Functor.IsDense`. -/
theorem isDense_iff (F : C ⥤ D) :
    F.IsDense ↔ Nonempty (LeftExtension.mk (𝟭 D) (Functor.rightUnitor F).inv).IsPointwiseLeftKanExtension :=
  isDense_iff_nonempty_isPointwiseLeftKanExtension F

/-- `ALGD-C2-KAN-42` (例 42, p.38).
The Yoneda embedding is dense (系 29). -/
theorem yoneda_isDense : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).IsDense :=
  inferInstance

/-! ### Pointwise Kan extensions through hom-sets (補題 24, 定理 25) -/

section HomSets

variable {D : Type u₂} [Category.{v} D] {U : Type u₃} [Category.{v} U]

/-- For `η : E ⇒ TF`, the map `φ_du : Hom_U(Td, u) → Hom_Ĉ(Hom_D(F−, d), Hom_U(E−, u))`,
`φ_du(k)_c(f) = k ∘ Tf ∘ η_c`, of formula (26). -/
def presheafHom {F : C ⥤ D} {E : C ⥤ U} {T : D ⥤ U} (η : E ⟶ F ⋙ T) (d : D) (u : U)
    (k : T.obj d ⟶ u) : F.op ⋙ yoneda.obj d ⟶ E.op ⋙ yoneda.obj u where
  app c := ↾ fun f ↦ η.app c.unop ≫ T.map f ≫ k
  naturality c c' g := by
    ext f
    simp [η.naturality_assoc]

@[simp]
theorem presheafHom_app_apply {F : C ⥤ D} {E : C ⥤ U} {T : D ⥤ U} (η : E ⟶ F ⋙ T) (d : D)
    (u : U) (k : T.obj d ⟶ u) (c : Cᵒᵖ) (f : F.obj c.unop ⟶ d) :
    (presheafHom η d u k).app c f = η.app c.unop ≫ T.map f ≫ k :=
  rfl

/-- The bijection `ξ_u` of 補題 24 between cocones on `F ↓ d → C → U` with vertex `u` and
natural transformations `Hom_D(F−, d) ⇒ Hom_U(E−, u)`: `ξ_u(θ)_c(f) = θ_⟨c, f⟩`, with inverse
`ζ_u(β)_⟨c, f⟩ = β_c(f)`. -/
def coconeHomEquiv (F : C ⥤ D) (E : C ⥤ U) (d : D) (u : U) :
    (CostructuredArrow.proj F d ⋙ E ⟶ (const _).obj u) ≃
      (F.op ⋙ yoneda.obj d ⟶ E.op ⋙ yoneda.obj u) where
  toFun θ :=
    { app c := ↾ fun f ↦ θ.app (CostructuredArrow.mk f)
      naturality c c' g := by
        ext f
        have h := θ.naturality (CostructuredArrow.homMk g.unop rfl :
          CostructuredArrow.mk (F.map g.unop ≫ f) ⟶ CostructuredArrow.mk f)
        dsimp at h ⊢
        simpa using h.symm }
  invFun β :=
    { app g := β.app (op g.left) g.hom
      naturality g g' φ := by
        have h := ConcreteCategory.congr_hom (β.naturality φ.left.op) g'.hom
        dsimp at h ⊢
        rw [Category.comp_id, ← CostructuredArrow.w φ]
        simpa using h.symm }
  left_inv θ := by
    ext g
    rfl
  right_inv β := by
    ext c f
    rfl

/-- `ALGD-C2-KAN-24` (補題 24, p.25–28).
For `F : C → D`, `E : C → U` and `d ∈ D`, with `K := E P₀ : F ↓ d → U`, the maps
`ξ_u : Hom_{U^{F↓d}}(K, ∆u) → Hom_Ĉ(Hom_D(F−, d), Hom_U(E−, u))`, `ξ_u(θ)_c(f) = θ_⟨c, f⟩`,
are bijections natural in `u ∈ U`. Here `Ĉ = C^op → Type v`, where `v` is the common hom
universe of `D` and `U`. -/
theorem coconeHomEquiv_natural (F : C ⥤ D) (E : C ⥤ U) (d : D) :
    (∀ u : U, Function.Bijective (coconeHomEquiv F E d u)) ∧
    (∀ (u u' : U) (k : u ⟶ u') (θ : CostructuredArrow.proj F d ⋙ E ⟶ (const _).obj u),
      coconeHomEquiv F E d u' (θ ≫ (const _).map k) =
        coconeHomEquiv F E d u θ ≫ whiskerLeft E.op (yoneda.map k)) ∧
    ∀ (u : U) (θ : CostructuredArrow.proj F d ⋙ E ⟶ (const _).obj u) (c : C)
      (f : F.obj c ⟶ d),
      (coconeHomEquiv F E d u θ).app (op c) f = θ.app (CostructuredArrow.mk f) :=
  ⟨fun u ↦ (coconeHomEquiv F E d u).bijective, fun _ _ _ _ ↦ by ext; rfl, fun _ _ _ _ ↦ rfl⟩

/-- A cocone is a colimit iff `k ↦ k ∘ ι` is bijective for every vertex. -/
private theorem isColimit_iff_bijective {J : Type*} [Category J] {K : J ⥤ U} (c : Cocone K) :
    Nonempty (IsColimit c) ↔
      ∀ u : U, Function.Bijective (fun k : c.pt ⟶ u ↦ c.ι ≫ (const J).map k) := by
  constructor
  · rintro ⟨h⟩ u
    refine ⟨fun k k' hkk ↦ h.hom_ext fun j ↦ congrArg (fun α ↦ NatTrans.app α j) hkk,
      fun θ ↦ ⟨h.desc ⟨u, θ⟩, ?_⟩⟩
    ext j
    exact h.fac ⟨u, θ⟩ j
  · intro hb
    refine ⟨IsColimit.ofExistsUnique fun s ↦ ?_⟩
    obtain ⟨k, hk⟩ := (hb s.pt).2 s.ι
    refine ⟨k, fun j ↦ congrArg (fun α ↦ NatTrans.app α j) hk, fun k' hk' ↦ (hb s.pt).1 ?_⟩
    beta_reduce at hk hk' ⊢
    rw [hk]
    ext j
    exact hk' j

/-- `ALGD-C2-KAN-26` (formula (26), ※ in the proof of 定理 25, p.29).
`⟨T, η⟩` is a pointwise left Kan extension iff every map `φ_du`, `φ_du(k)_c(f) = k ∘ Tf ∘ η_c`,
is bijective. So the bijection of 定理 25 (3) obtained from a pointwise left Kan extension is
given by formula (26). -/
theorem isPointwise_iff_bijective {F : C ⥤ D} {E : C ⥤ U} (T : D ⥤ U) (η : E ⟶ F ⋙ T) :
    Nonempty (LeftExtension.mk T η).IsPointwiseLeftKanExtension ↔
      ∀ (d : D) (u : U), Function.Bijective (presheafHom η d u) := by
  have key : ∀ d u, presheafHom η d u = coconeHomEquiv F E d u ∘
      fun k ↦ ((LeftExtension.mk T η).coconeAt d).ι ≫ (const _).map k := by
    intro d u
    funext k
    ext c f
    simp [presheafHom, coconeHomEquiv, LeftExtension.coconeAt]
  simp_rw [key, Equiv.comp_bijective]
  constructor
  · rintro ⟨h⟩ d
    exact (isColimit_iff_bijective _).1 ⟨h d⟩
  · intro h
    exact ⟨fun d ↦ ((isColimit_iff_bijective _).2 (h d)).some⟩

/-- If every `Hom_U(−, u) : U → Set^op` commutes with `⟨T, η⟩`, then every `φ_du` is bijective.
The test functor is `Hom_D(−, d) : D → Set^op`. -/
theorem bijective_of_commutesWith_yoneda {F : C ⥤ D} {E : C ⥤ U} {T : D ⥤ U} (η : E ⟶ F ⋙ T)
    (d : D) (u : U) (hu : CommutesWith (yoneda.obj u).rightOp T η) :
    Function.Bijective (presheafHom η d u) := by
  rw [CommutesWith, isLeftKanExtension_iff] at hu
  let θ : (F.op ⋙ yoneda.obj d ⟶ E.op ⋙ yoneda.obj u) →
      (E ⋙ (yoneda.obj u).rightOp ⟶ F ⋙ (yoneda.obj d).rightOp) := fun β ↦
    { app c := (β.app (op c)).op
      naturality c c' g := Quiver.Hom.unop_inj (β.naturality g.op).symm }
  let τ : (T.obj d ⟶ u) → (T ⋙ (yoneda.obj u).rightOp ⟶ (yoneda.obj d).rightOp) := fun k ↦
    { app d' := (↾ fun x : d' ⟶ d ↦ T.map x ≫ k).op
      naturality d' d'' g := Quiver.Hom.unop_inj (by ext x; simp) }
  have hτ : ∀ k, θ (presheafHom η d u k) =
      (whiskerRight η _ ≫ (Functor.associator F T _).hom) ≫ whiskerLeft F (τ k) := by
    intro k
    ext c x
    simp [θ, τ]
    rfl
  constructor
  · intro k k' hkk
    obtain ⟨σ, -, hσ⟩ := hu _ (θ (presheafHom η d u k))
    have e1 := hσ (τ k) (hτ k)
    have e2 := hσ (τ k') (by rw [hkk]; exact hτ k')
    have := ConcreteCategory.congr_hom
      (congrArg (fun α : T ⋙ (yoneda.obj u).rightOp ⟶ (yoneda.obj d).rightOp ↦ (α.app d).unop)
        (e1.trans e2.symm)) (𝟙 d)
    simpa [τ] using this
  · intro β
    obtain ⟨σ, hσ, -⟩ := hu _ (θ β)
    refine ⟨(σ.app d).unop (𝟙 d), ?_⟩
    ext c f
    have h1 := ConcreteCategory.congr_hom
      (congrArg (fun α : E ⋙ (yoneda.obj u).rightOp ⟶ F ⋙ (yoneda.obj d).rightOp ↦
        (α.app c.unop).unop) hσ) f
    have h2 := ConcreteCategory.congr_hom (congrArg Quiver.Hom.unop (σ.naturality f)) (𝟙 d)
    simp [θ] at h1 h2
    change η.app c.unop ≫ T.map f ≫ (σ.app d).unop (𝟙 d) = β.app c f
    rw [h1, h2]

/-- `(2) ⇒ (1)` of 定理 25 for a fixed `η`. -/
theorem isPointwise_of_commutesWith_yoneda {F : C ⥤ D} {E : C ⥤ U} {T : D ⥤ U}
    (η : E ⟶ F ⋙ T) (hu : ∀ u : U, CommutesWith (yoneda.obj u).rightOp T η) :
    Nonempty (LeftExtension.mk T η).IsPointwiseLeftKanExtension :=
  (isPointwise_iff_bijective T η).2 fun d u ↦ bijective_of_commutesWith_yoneda η d u (hu u)

/-- `ALGD-C2-KAN-25`, `ALGD-C2-AFT-03` (定理 25, p.28–31; restated as `aft.pdf` 定理 3, p.2).
For `F : C → D`, `E : C → U` and `T : D → U` the following are equivalent:
(1) some `η : E ⇒ TF` makes `⟨T, η⟩` a pointwise left Kan extension of `E` along `F`;
(2) some `η` makes `⟨T, η⟩` a left Kan extension with which every `Hom_U(−, u) : U → Set^op`
commutes; (3) there are bijections `Hom_U(Td, u) ≅ Hom_Ĉ(Hom_D(F−, d), Hom_U(E−, u))` natural in
`d ∈ D` and `u ∈ U`. Here `D` and `U` share the hom universe `v` and `Ĉ = C^op → Type v`. -/
theorem pointwise_tfae (F : C ⥤ D) (E : C ⥤ U) (T : D ⥤ U) :
    List.TFAE [
      ∃ η : E ⟶ F ⋙ T, Nonempty (LeftExtension.mk T η).IsPointwiseLeftKanExtension,
      ∃ η : E ⟶ F ⋙ T, T.IsLeftKanExtension η ∧ ∀ u : U, CommutesWith (yoneda.obj u).rightOp T η,
      ∃ φ : ∀ (d : D) (u : U), (T.obj d ⟶ u) ≃ (F.op ⋙ yoneda.obj d ⟶ E.op ⋙ yoneda.obj u),
        (∀ (d : D) (u u' : U) (h : T.obj d ⟶ u) (k : u ⟶ u'),
          φ d u' (h ≫ k) = φ d u h ≫ whiskerLeft E.op (yoneda.map k)) ∧
        ∀ (d d' : D) (u : U) (g : d ⟶ d') (h : T.obj d' ⟶ u),
          φ d u (T.map g ≫ h) = whiskerLeft F.op (yoneda.map g) ≫ φ d' u h] := by
  tfae_have 1 → 2 := by
    rintro ⟨η, ⟨h⟩⟩
    refine ⟨η, h.isLeftKanExtension, fun u ↦ ?_⟩
    have : ∀ d : D, PreservesColimit (CostructuredArrow.proj F d ⋙ E) (yoneda.obj u).rightOp :=
      fun _ ↦ preservesColimit_rightOp _ _
    exact (commutesWith_of_preservesColimit h _).2
  tfae_have 2 → 1 := fun ⟨η, _, hu⟩ ↦ ⟨η, isPointwise_of_commutesWith_yoneda η hu⟩
  tfae_have 1 → 3 := by
    rintro ⟨η, h⟩
    have hb := (isPointwise_iff_bijective T η).1 h
    refine ⟨fun d u ↦ Equiv.ofBijective _ (hb d u), fun d u u' h k ↦ ?_, fun d d' u g h ↦ ?_⟩
    · ext c f
      simp [presheafHom]
    · ext c f
      simp [presheafHom]
  tfae_have 3 → 1 := by
    rintro ⟨φ, hu, hd⟩
    let ηf : ∀ c : C, E.obj c ⟶ T.obj (F.obj c) := fun c ↦
      (φ (F.obj c) (T.obj (F.obj c)) (𝟙 _)).app (op c) (𝟙 (F.obj c))
    have key : ∀ (d : D) (u : U) (h : T.obj d ⟶ u) (c : C) (f : F.obj c ⟶ d),
        (φ d u h).app (op c) f = ηf c ≫ T.map f ≫ h := by
      intro d u h c f
      have e1 := ConcreteCategory.congr_hom
        (congrArg (fun α : F.op ⋙ yoneda.obj (F.obj c) ⟶ E.op ⋙ yoneda.obj u ↦ α.app (op c))
          (hd (F.obj c) d u f h)) (𝟙 (F.obj c))
      have e2 := ConcreteCategory.congr_hom
        (congrArg (fun α : F.op ⋙ yoneda.obj (F.obj c) ⟶ E.op ⋙ yoneda.obj u ↦ α.app (op c))
          (hu (F.obj c) (T.obj (F.obj c)) u (𝟙 _) (T.map f ≫ h))) (𝟙 (F.obj c))
      simp only [Category.id_comp] at e1 e2
      simp at e1 e2
      rw [← e1, e2]
    let η : E ⟶ F ⋙ T :=
      { app := ηf
        naturality c c' g := by
          have e := ConcreteCategory.congr_hom
            ((φ (F.obj c') (T.obj (F.obj c')) (𝟙 _)).naturality g.op) (𝟙 (F.obj c'))
          simp at e
          rw [key] at e
          simpa using e.symm }
    refine ⟨η, (isPointwise_iff_bijective T η).2 fun d u ↦ ?_⟩
    have : presheafHom η d u = φ d u := by
      funext h
      ext c f
      exact (key d u h c.unop f).symm
    rw [this]
    exact (φ d u).bijective
  tfae_finish

/-- For `ε : TF ⇒ E`, the map `Hom_U(u, Td) → Hom_{Set^C}(Hom_D(d, F−), Hom_U(u, E−))`,
`k ↦ (f ↦ ε_c ∘ Tf ∘ k)`, dual to `presheafHom`. -/
def copresheafHom {F : C ⥤ D} {E : C ⥤ U} {T : D ⥤ U} (ε : F ⋙ T ⟶ E) (d : D) (u : U)
    (k : u ⟶ T.obj d) : F ⋙ coyoneda.obj (op d) ⟶ E ⋙ coyoneda.obj (op u) where
  app c := ↾ fun f ↦ k ≫ T.map f ≫ ε.app c
  naturality c c' g := by
    ext f
    simp [← ε.naturality]

/-- Cones on `d ↓ F → C → U` with vertex `u` correspond to natural transformations
`Hom_D(d, F−) ⇒ Hom_U(u, E−)`, dually to `coconeHomEquiv`. -/
def coneHomEquiv (F : C ⥤ D) (E : C ⥤ U) (d : D) (u : U) :
    ((const _).obj u ⟶ StructuredArrow.proj d F ⋙ E) ≃
      (F ⋙ coyoneda.obj (op d) ⟶ E ⋙ coyoneda.obj (op u)) where
  toFun θ :=
    { app c := ↾ fun f ↦ θ.app (StructuredArrow.mk f)
      naturality c c' g := by
        ext f
        have h := θ.naturality (StructuredArrow.homMk g rfl :
          StructuredArrow.mk f ⟶ StructuredArrow.mk (f ≫ F.map g))
        dsimp at h ⊢
        simpa using h }
  invFun β :=
    { app g := β.app g.right g.hom
      naturality g g' φ := by
        have h := ConcreteCategory.congr_hom (β.naturality φ.right) g.hom
        dsimp at h ⊢
        rw [Category.id_comp, ← StructuredArrow.w φ]
        simpa using h }
  left_inv θ := by
    ext g
    rfl
  right_inv β := by
    ext c f
    rfl

/-- A cone is a limit iff `k ↦ π ∘ k` is bijective for every vertex. -/
private theorem isLimit_iff_bijective {J : Type*} [Category J] {K : J ⥤ U} (c : Cone K) :
    Nonempty (IsLimit c) ↔
      ∀ u : U, Function.Bijective (fun k : u ⟶ c.pt ↦ (const J).map k ≫ c.π) := by
  constructor
  · rintro ⟨h⟩ u
    refine ⟨fun k k' hkk ↦ h.hom_ext fun j ↦ congrArg (fun α ↦ NatTrans.app α j) hkk,
      fun θ ↦ ⟨h.lift ⟨u, θ⟩, ?_⟩⟩
    ext j
    exact h.fac ⟨u, θ⟩ j
  · intro hb
    refine ⟨IsLimit.ofExistsUnique fun s ↦ ?_⟩
    obtain ⟨k, hk⟩ := (hb s.pt).2 s.π
    refine ⟨k, fun j ↦ congrArg (fun α ↦ NatTrans.app α j) hk, fun k' hk' ↦ (hb s.pt).1 ?_⟩
    beta_reduce at hk hk' ⊢
    rw [hk]
    ext j
    exact hk' j

/-- Dual of `isPointwise_iff_bijective`: `⟨T, ε⟩` is a pointwise right Kan extension iff every
`k ↦ (f ↦ ε_c ∘ Tf ∘ k)` is bijective. -/
theorem isPointwiseRight_iff_bijective {F : C ⥤ D} {E : C ⥤ U} (T : D ⥤ U) (ε : F ⋙ T ⟶ E) :
    Nonempty (RightExtension.mk T ε).IsPointwiseRightKanExtension ↔
      ∀ (d : D) (u : U), Function.Bijective (copresheafHom ε d u) := by
  have key : ∀ d u, copresheafHom ε d u = coneHomEquiv F E d u ∘
      fun k ↦ (const _).map k ≫ ((RightExtension.mk T ε).coneAt d).π := by
    intro d u
    funext k
    ext c f
    simp [copresheafHom, coneHomEquiv, RightExtension.coneAt]
  simp_rw [key, Equiv.comp_bijective]
  constructor
  · rintro ⟨h⟩ d
    exact (isLimit_iff_bijective _).1 ⟨h d⟩
  · intro h
    exact ⟨fun d ↦ ((isLimit_iff_bijective _).2 (h d)).some⟩

/-- If every `Hom_U(u, −)` commutes with the right Kan extension `⟨T, ε⟩`, then every
`k ↦ (f ↦ ε_c ∘ Tf ∘ k)` is bijective. The test functor is `Hom_D(d, −)`. -/
theorem bijective_of_commutesWithRight_coyoneda {F : C ⥤ D} {E : C ⥤ U} {T : D ⥤ U}
    (ε : F ⋙ T ⟶ E) (d : D) (u : U) (hu : CommutesWithRight (coyoneda.obj (op u)) T ε) :
    Function.Bijective (copresheafHom ε d u) := by
  rw [CommutesWithRight, isRightKanExtension_iff] at hu
  let τ : (u ⟶ T.obj d) → (coyoneda.obj (op d) ⟶ T ⋙ coyoneda.obj (op u)) := fun k ↦
    { app d' := ↾ fun x : d ⟶ d' ↦ k ≫ T.map x
      naturality d' d'' g := by ext x; simp }
  have hτ : ∀ k, copresheafHom ε d u k =
      whiskerLeft F (τ k) ≫ (Functor.associator F T _).inv ≫ whiskerRight ε _ := by
    intro k
    ext c x
    simp [τ, copresheafHom]
  constructor
  · intro k k' hkk
    obtain ⟨σ, -, hσ⟩ := hu _ (copresheafHom ε d u k)
    have e1 := hσ (τ k) (hτ k)
    have e2 := hσ (τ k') (by rw [hkk]; exact hτ k')
    have := ConcreteCategory.congr_hom
      (congrArg (fun α : coyoneda.obj (op d) ⟶ T ⋙ coyoneda.obj (op u) ↦ α.app d)
        (e1.trans e2.symm)) (𝟙 d)
    simpa [τ] using this
  · intro β
    obtain ⟨σ, hσ, -⟩ := hu _ β
    refine ⟨σ.app d (𝟙 d), ?_⟩
    ext c f
    have h1 := ConcreteCategory.congr_hom
      (congrArg (fun α : F ⋙ coyoneda.obj (op d) ⟶ E ⋙ coyoneda.obj (op u) ↦ α.app c) hσ) f
    have h2 := ConcreteCategory.congr_hom (σ.naturality f) (𝟙 d)
    simp at h1 h2
    change σ.app d (𝟙 d) ≫ T.map f ≫ ε.app c = β.app c f
    rw [h1, h2, Category.assoc]

/-- `ALGD-C2-KAN-R03` (※ after 定理 25, p.32).
Dually, for `T : D → U` the following are equivalent: (1) some `ε : TF ⇒ E` makes `⟨T, ε⟩` a
pointwise right Kan extension of `E` along `F`; (2) some `ε` makes `⟨T, ε⟩` a right Kan
extension with which every `Hom_U(u, −) : U → Set` commutes; (3) there are bijections
`Hom_U(u, Td) ≅ Hom_{Set^C}(Hom_D(d, F−), Hom_U(u, E−))` natural in `d` and `u`. -/
theorem pointwiseRight_tfae (F : C ⥤ D) (E : C ⥤ U) (T : D ⥤ U) :
    List.TFAE [
      ∃ ε : F ⋙ T ⟶ E, Nonempty (RightExtension.mk T ε).IsPointwiseRightKanExtension,
      ∃ ε : F ⋙ T ⟶ E, T.IsRightKanExtension ε ∧
        ∀ u : U, CommutesWithRight (coyoneda.obj (op u)) T ε,
      ∃ φ : ∀ (d : D) (u : U), (u ⟶ T.obj d) ≃ (F ⋙ coyoneda.obj (op d) ⟶ E ⋙ coyoneda.obj (op u)),
        (∀ (d : D) (u u' : U) (k : u ⟶ u') (h : u' ⟶ T.obj d),
          φ d u (k ≫ h) = φ d u' h ≫ whiskerLeft E (coyoneda.map k.op)) ∧
        ∀ (d d' : D) (u : U) (g : d ⟶ d') (h : u ⟶ T.obj d),
          φ d' u (h ≫ T.map g) = whiskerLeft F (coyoneda.map g.op) ≫ φ d u h] := by
  tfae_have 1 → 2 := by
    rintro ⟨ε, ⟨h⟩⟩
    refine ⟨ε, h.isRightKanExtension, fun u ↦ ?_⟩
    have h' := RightExtension.isPointwiseRightKanExtensionEquivOfIso
      (RightExtension.postcompose₂ObjMkIso (coyoneda.obj (op u)) ε) (h.postcompose _)
    exact h'.isRightKanExtension
  tfae_have 2 → 1 := fun ⟨ε, _, hu⟩ ↦ ⟨ε, (isPointwiseRight_iff_bijective T ε).2
    fun d u ↦ bijective_of_commutesWithRight_coyoneda ε d u (hu u)⟩
  tfae_have 1 → 3 := by
    rintro ⟨ε, h⟩
    have hb := (isPointwiseRight_iff_bijective T ε).1 h
    refine ⟨fun d u ↦ Equiv.ofBijective _ (hb d u), fun d u u' k h ↦ ?_, fun d d' u g h ↦ ?_⟩
    · ext c f
      simp [copresheafHom]
    · ext c f
      simp [copresheafHom]
  tfae_have 3 → 1 := by
    rintro ⟨φ, hu, hd⟩
    let εf : ∀ c : C, T.obj (F.obj c) ⟶ E.obj c := fun c ↦
      (φ (F.obj c) (T.obj (F.obj c)) (𝟙 _)).app c (𝟙 (F.obj c))
    have key : ∀ (d : D) (u : U) (h : u ⟶ T.obj d) (c : C) (f : d ⟶ F.obj c),
        (φ d u h).app c f = h ≫ T.map f ≫ εf c := by
      intro d u h c f
      have e1 := ConcreteCategory.congr_hom
        (congrArg (fun α : F ⋙ coyoneda.obj (op (F.obj c)) ⟶ E ⋙ coyoneda.obj (op u) ↦ α.app c)
          (hd d (F.obj c) u f h)) (𝟙 (F.obj c))
      have e2 := ConcreteCategory.congr_hom
        (congrArg (fun α : F ⋙ coyoneda.obj (op (F.obj c)) ⟶ E ⋙ coyoneda.obj (op u) ↦ α.app c)
          (hu (F.obj c) u (T.obj (F.obj c)) (h ≫ T.map f) (𝟙 _))) (𝟙 (F.obj c))
      simp only [Category.comp_id] at e1 e2
      simp at e1 e2
      rw [← e1, e2]
    let ε : F ⋙ T ⟶ E :=
      { app := εf
        naturality c c' g := by
          have e := ConcreteCategory.congr_hom
            ((φ (F.obj c) (T.obj (F.obj c)) (𝟙 _)).naturality g) (𝟙 (F.obj c))
          simp at e
          rw [key] at e
          simpa using e }
    refine ⟨ε, (isPointwiseRight_iff_bijective T ε).2 fun d u ↦ ?_⟩
    have : copresheafHom ε d u = φ d u := by
      funext h
      ext c f
      exact (key d u h c f).symm
    rw [this]
    exact (φ d u).bijective
  tfae_finish

/-- `ALGD-C2-KAN-27` (系 27, p.32).
Every absolute left Kan extension is pointwise: it commutes with every `Hom_U(−, u)`, so 定理 25
applies. The test categories include `Set^op`, so absoluteness is taken in the universe of
`(Type v)ᵒᵖ`. -/
theorem isPointwise_of_isAbsolute {F : C ⥤ D} {E : C ⥤ U} {T : D ⥤ U} {η : E ⟶ F ⋙ T}
    (h : IsAbsoluteLeftKanExtension.{v + 1, v} T η) :
    Nonempty (LeftExtension.mk T η).IsPointwiseLeftKanExtension :=
  isPointwise_of_commutesWith_yoneda η fun _ ↦ h.2 _ _

end HomSets

/-! ### Presheaves on a small category (系 28 – 命題 44; §5: 定理 45, 46 and 例 50) -/

section Small

variable {C : Type v} [SmallCategory C] {D : Type u₂} [Category.{v} D]

/-- The functor `d ↦ Hom_D(F−, d) : D → Ĉ`, which is `F † y` by 系 28. -/
abbrev restrictYoneda (F : C ⥤ D) : D ⥤ Cᵒᵖ ⥤ Type v :=
  yoneda ⋙ (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)).obj F.op

/-- The unit `η : y ⇒ (F † y) F` of 系 28: `(η_c)_a = F : Hom_C(a, c) → Hom_D(Fa, Fc)`. -/
def restrictYonedaUnit (F : C ⥤ D) : yoneda ⟶ F ⋙ restrictYoneda F where
  app c := yonedaMap F c
  naturality c c' g := by
    ext a f
    simp [yonedaMap]

/-- `ALGD-C2-KAN-R04` (prose after 系 28, p.32–33).
The unit `η_c : y(c) ⇒ Hom_D(F−, Fc)` of 系 28 corresponds to `id_{Fc}` under the Yoneda lemma. -/
theorem restrictYonedaUnit_yonedaEquiv (F : C ⥤ D) (c : C) :
    yonedaEquiv ((restrictYonedaUnit F).app c) = 𝟙 (F.obj c) := by
  rw [yonedaEquiv_apply]
  exact F.map_id c

/-- `ALGD-C2-KAN-39` (formula (39), p.36).
`(η_c)_a = F : Hom_C(a, c) → Hom_D(Fa, Fc)` for the unit of 系 28. -/
theorem restrictYonedaUnit_app_app (F : C ⥤ D) (c a : C) (f : a ⟶ c) :
    ((restrictYonedaUnit F).app c).app (op a) f = F.map f :=
  rfl

/-- The Yoneda isomorphism `P ≅ Hom_Ĉ(y−, P)`, `x ↦ x̂`. -/
def yonedaPresheafIso (P : Cᵒᵖ ⥤ Type v) : P ≅ yoneda.op ⋙ yoneda.obj P :=
  NatIso.ofComponents (fun c ↦ Equiv.toIso yonedaEquiv.symm) fun {c c'} g ↦ by
    ext x
    exact (yonedaEquiv_symm_naturality_left g.unop P x).symm

theorem presheafHom_restrictYonedaUnit (F : C ⥤ D) (d : D) (P : Cᵒᵖ ⥤ Type v)
    (k : (restrictYoneda F).obj d ⟶ P) :
    presheafHom (restrictYonedaUnit F) d P k = k ≫ (yonedaPresheafIso P).hom := by
  ext c f
  apply yonedaEquiv.injective
  rw [yonedaEquiv_apply]
  simp [yonedaPresheafIso, presheafHom, restrictYonedaUnit, yonedaMap]

private theorem comp_iso_bijective {X Y Z : Cᵒᵖ ⥤ Type v} (e : Y ≅ Z) :
    Function.Bijective (fun k : X ⟶ Y ↦ k ≫ e.hom) :=
  ⟨fun k k' h ↦ by simpa using congrArg (· ≫ e.inv) h, fun β ↦ ⟨β ≫ e.inv, by simp⟩⟩

/-- `ALGD-C2-KAN-28` (系 28, p.32).
For small `C` and `F : C → D`, `T := (d ↦ Hom_D(F−, d))` with the unit `(η_c)_a = F` is a
pointwise left Kan extension of the Yoneda embedding `y : C → Ĉ` along `F`. Hence `F † y`
exists and `F † y(d) ≅ Hom_D(F−, d)` naturally in `d`. -/
theorem restrictYoneda_isPointwise (F : C ⥤ D) :
    Nonempty (LeftExtension.mk (restrictYoneda F) (restrictYonedaUnit F)).IsPointwiseLeftKanExtension ∧
    F.HasLeftKanExtension yoneda ∧ Nonempty (F.leftKanExtension yoneda ≅ restrictYoneda F) := by
  have h : Nonempty (LeftExtension.mk (restrictYoneda F)
      (restrictYonedaUnit F)).IsPointwiseLeftKanExtension := by
    rw [isPointwise_iff_bijective]
    intro d P
    have : presheafHom (restrictYonedaUnit F) d P = fun k ↦ k ≫ (yonedaPresheafIso P).hom := by
      funext k
      exact presheafHom_restrictYonedaUnit F d P k
    rw [this]
    exact comp_iso_bijective _
  have : (restrictYoneda F).IsLeftKanExtension (restrictYonedaUnit F) := h.some.isLeftKanExtension
  exact ⟨h, HasLeftKanExtension.mk _ (restrictYonedaUnit F),
    ⟨leftKanExtensionUnique _ (F.leftKanExtensionUnit yoneda) _ (restrictYonedaUnit F)⟩⟩

theorem restrictYonedaUnit_comp_map (F : C ⥤ D) (c : C) {d : D} (f : F.obj c ⟶ d) :
    (restrictYonedaUnit F).app c ≫ (restrictYoneda F).map f = yonedaEquiv.symm f := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_apply, Equiv.apply_symm_apply]
  simp [restrictYonedaUnit, yonedaMap]

private theorem iso_comp_bijective {X Y Z : Cᵒᵖ ⥤ Type v} (e : X ≅ Y) :
    Function.Bijective (fun β : Y ⟶ Z ↦ e.hom ≫ β) :=
  ⟨fun k k' h ↦ by simpa using congrArg (e.inv ≫ ·) h, fun β ↦ ⟨e.inv ≫ β, by simp⟩⟩

/-- `ALGD-C2-KAN-33` (定理 33, p.34–35).
If `⟨T₁, η₁⟩` is a pointwise left Kan extension of `E` along `F` and `⟨T₂, η₂⟩` a pointwise left
Kan extension of `E` along `y`, then `T₂ ∘ F† y ≅ T₁`, that is, `y† E ∘ F† y ≅ F† E`. -/
theorem lan_comp_restrictYoneda {U : Type u₃} [Category.{v} U] (F : C ⥤ D) (E : C ⥤ U)
    {T₁ : D ⥤ U} {η₁ : E ⟶ F ⋙ T₁} (h₁ : (LeftExtension.mk T₁ η₁).IsPointwiseLeftKanExtension)
    {T₂ : (Cᵒᵖ ⥤ Type v) ⥤ U} {η₂ : E ⟶ yoneda ⋙ T₂}
    (h₂ : (LeftExtension.mk T₂ η₂).IsPointwiseLeftKanExtension) :
    Nonempty (restrictYoneda F ⋙ T₂ ≅ T₁) := by
  let η : E ⟶ F ⋙ (restrictYoneda F ⋙ T₂) := η₂ ≫ whiskerRight (restrictYonedaUnit F) T₂
  have hb₂ := (isPointwise_iff_bijective T₂ η₂).1 ⟨h₂⟩
  have hη : Nonempty (LeftExtension.mk _ η).IsPointwiseLeftKanExtension := by
    rw [isPointwise_iff_bijective]
    intro d u
    have : presheafHom η d u = fun k ↦ (yonedaPresheafIso ((restrictYoneda F).obj d)).hom ≫
        presheafHom η₂ ((restrictYoneda F).obj d) u k := by
      funext k
      ext c f
      change (η₂.app c.unop ≫ T₂.map ((restrictYonedaUnit F).app c.unop)) ≫
          T₂.map ((restrictYoneda F).map f) ≫ k = η₂.app c.unop ≫ T₂.map (yonedaEquiv.symm f) ≫ k
      rw [← restrictYonedaUnit_comp_map, T₂.map_comp]
      simp
    rw [this]
    exact (iso_comp_bijective _).comp (hb₂ _ u)
  have : T₁.IsLeftKanExtension η₁ := h₁.isLeftKanExtension
  have : (restrictYoneda F ⋙ T₂).IsLeftKanExtension η := hη.some.isLeftKanExtension
  exact ⟨leftKanExtensionUnique _ η _ η₁⟩

/-- A functor `K : Ĉ → U` that preserves the colimits of the diagrams `y ↓ P → C → Ĉ` is a
pointwise left Kan extension of `K y` along `y`, with the identity unit. -/
theorem isPointwise_of_preservesColimit {U : Type u₃} [Category.{v} U]
    (K : (Cᵒᵖ ⥤ Type v) ⥤ U)
    [∀ P : Cᵒᵖ ⥤ Type v, PreservesColimit (CostructuredArrow.proj yoneda P ⋙ yoneda) K] :
    Nonempty (LeftExtension.mk K (𝟙 (yoneda ⋙ K))).IsPointwiseLeftKanExtension := by
  obtain ⟨h⟩ := (yoneda_isLeftKanExtension_id (C := C)).2
  obtain ⟨h'⟩ := (commutesWith_of_preservesColimit h K).1
  exact ⟨LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
    (StructuredArrow.isoMk (Functor.leftUnitor K) (by ext; simp)) h'⟩

/-- The unit `Hom_C(a, −) ⇒ ev_a ∘ y` of 系 35, the identity. -/
def coyonedaUnit (a : C) :
    coyoneda.obj (op a) ⟶ yoneda ⋙ (evaluation Cᵒᵖ (Type v)).obj (op a) :=
  𝟙 (coyoneda.obj (op a))

/-- `ALGD-C2-KAN-35` (系 35, p.35).
`y†(Hom_C(a, −)) ≅ ev_a`: evaluation at `a`, with the identity unit
`Hom_C(a, −) = ev_a ∘ y`, is a pointwise left Kan extension of `Hom_C(a, −)` along `y`. -/
theorem lan_yoneda_coyoneda (a : C) :
    Nonempty (LeftExtension.mk ((evaluation Cᵒᵖ (Type v)).obj (op a))
      (coyonedaUnit a)).IsPointwiseLeftKanExtension ∧
    Nonempty (yoneda.leftKanExtension (coyoneda.obj (op a)) ≅
      (evaluation Cᵒᵖ (Type v)).obj (op a)) := by
  obtain ⟨h⟩ := isPointwise_of_preservesColimit (C := C) ((evaluation Cᵒᵖ (Type v)).obj (op a))
  have h' : (LeftExtension.mk ((evaluation Cᵒᵖ (Type v)).obj (op a))
      (coyonedaUnit a)).IsPointwiseLeftKanExtension := h
  have : ((evaluation Cᵒᵖ (Type v)).obj (op a)).IsLeftKanExtension (coyonedaUnit a) :=
    h'.isLeftKanExtension
  exact ⟨⟨h'⟩, ⟨leftKanExtensionUnique _ (yoneda.leftKanExtensionUnit (coyoneda.obj (op a))) _
    (coyonedaUnit a)⟩⟩

/-- `ALGD-C2-KAN-38` (定理 38, p.36–37).
If `⟨T, η⟩` is a left Kan extension of `y` along `F : C → D` and `η` is an isomorphism, then `F`
is fully faithful. -/
theorem fullyFaithful_of_isIso_unit (F : C ⥤ D) (T : D ⥤ Cᵒᵖ ⥤ Type v) (η : yoneda ⟶ F ⋙ T)
    [T.IsLeftKanExtension η] [IsIso η] : F.Full ∧ F.Faithful := by
  have : (restrictYoneda F).IsLeftKanExtension (restrictYonedaUnit F) :=
    (restrictYoneda_isPointwise F).1.some.isLeftKanExtension
  let τ := T.descOfIsLeftKanExtension η (restrictYoneda F) (restrictYonedaUnit F)
  have hτ : η ≫ whiskerLeft F τ = restrictYonedaUnit F := T.descOfIsLeftKanExtension_fac η _ _
  have : IsIso τ := (isLeftKanExtension_iff_isIso τ η (restrictYonedaUnit F) hτ).1 inferInstance
  have : IsIso (restrictYonedaUnit F) := by
    rw [← hτ]
    infer_instance
  have hbij : ∀ a c : C, Function.Bijective (fun f : a ⟶ c ↦ F.map f) := fun a c ↦
    (isIso_iff_bijective (((restrictYonedaUnit F).app c).app (op a))).1 inferInstance
  exact ⟨{ map_surjective := fun {a c} ↦ (hbij a c).2 },
    { map_injective := fun {a c} ↦ (hbij a c).1 }⟩

/-- `ALGD-C2-KAN-40` (系 40, p.37).
`F : C → D` is fully faithful iff for every `E : C → U` and every pointwise left Kan extension
`⟨F† E, η⟩` the unit `η` is an isomorphism. The categories `U` range over `Type (v + 1)` with
hom universe `v`, which contains `Ĉ`. -/
theorem fullyFaithful_iff_isIso_unit (F : C ⥤ D) :
    (F.Full ∧ F.Faithful) ↔ ∀ (U : Type (v + 1)) [Category.{v} U] (E : C ⥤ U) (T : D ⥤ U)
      (η : E ⟶ F ⋙ T), Nonempty (LeftExtension.mk T η).IsPointwiseLeftKanExtension → IsIso η := by
  constructor
  · rintro ⟨_, _⟩ U _ E T η ⟨h⟩
    exact h.isIso_hom
  · intro h
    have hp := (restrictYoneda_isPointwise F).1
    have : IsIso (restrictYonedaUnit F) := h _ _ _ _ hp
    have : (restrictYoneda F).IsLeftKanExtension (restrictYonedaUnit F) :=
      hp.some.isLeftKanExtension
    exact fullyFaithful_of_isIso_unit F _ (restrictYonedaUnit F)

/-- `ALGD-C2-KAN-D09` (定義 (1), p.37).
`F : C → D` is strongly generating iff `F † y : D → Ĉ` is conservative. By 系 28, `F † y` is
`d ↦ Hom_D(F−, d)` (`restrictYoneda F`). -/
def IsStronglyGenerating (F : C ⥤ D) : Prop :=
  (restrictYoneda F).ReflectsIsomorphisms

/-- `ALGD-C2-KAN-43` (定理 43, p.38–39).
For `F : C → D` the following are equivalent: (1) `F` is dense; (2) for some natural
isomorphism `η : F ⇒ F`, `⟨id_D, η⟩` is a pointwise left Kan extension of `F` along `F`;
(3) `F † y : D → Ĉ` is fully faithful. mathlib's
`Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda` assumes that `F` is full. -/
theorem isDense_tfae (F : C ⥤ D) :
    List.TFAE [F.IsDense,
      ∃ η : F ⟶ F ⋙ 𝟭 D, IsIso η ∧ Nonempty (LeftExtension.mk (𝟭 D) η).IsPointwiseLeftKanExtension,
      (restrictYoneda F).Full ∧ (restrictYoneda F).Faithful] := by
  tfae_have 1 → 2 := fun h ↦ ⟨(Functor.rightUnitor F).inv, inferInstance, (isDense_iff F).1 h⟩
  tfae_have 2 → 3 := by
    rintro ⟨η, _, h⟩
    have hb := (isPointwise_iff_bijective (𝟭 D) η).1 h
    refine ⟨{ map_surjective := fun {d d'} β ↦ ?_ }, { map_injective := fun {d d'} k k' hk ↦ ?_ }⟩
    · let β' : F.op ⋙ yoneda.obj d ⟶ F.op ⋙ yoneda.obj d' :=
        { app c := ↾ fun x ↦ η.app c.unop ≫ β.app c x
          naturality c c' g := by
            ext x
            have h1 := ConcreteCategory.congr_hom (β.naturality g) x
            simp at h1 ⊢
            rw [h1] }
      obtain ⟨k, hk⟩ := (hb d d').2 β'
      refine ⟨k, ?_⟩
      ext c f
      have h1 := ConcreteCategory.congr_hom
        (congrArg (fun α : F.op ⋙ yoneda.obj d ⟶ F.op ⋙ yoneda.obj d' ↦ α.app c) hk) f
      change η.app c.unop ≫ f ≫ k = η.app c.unop ≫ β.app c f at h1
      exact (cancel_epi (η.app c.unop)).1 h1
    · apply (hb d d').1
      ext c f
      have h1 := ConcreteCategory.congr_hom
        (congrArg (fun α : F.op ⋙ yoneda.obj d ⟶ F.op ⋙ yoneda.obj d' ↦ α.app c) hk) f
      change f ≫ k = f ≫ k' at h1
      change η.app c.unop ≫ f ≫ k = η.app c.unop ≫ f ≫ k'
      rw [h1]
  tfae_have 3 → 1 := by
    rintro ⟨_, _⟩
    rw [isDense_iff, isPointwise_iff_bijective]
    intro d d'
    have : presheafHom (Functor.rightUnitor F).inv d d' = (restrictYoneda F).map := by
      funext k
      ext c f
      simp [presheafHom]
    rw [this]
    exact ⟨(restrictYoneda F).map_injective, (restrictYoneda F).map_surjective⟩
  tfae_finish

/-- `ALGD-C2-KAN-44` (命題 44, p.39).
Every dense functor is strongly generating. -/
theorem isStronglyGenerating_of_isDense (F : C ⥤ D) [F.IsDense] : IsStronglyGenerating F := by
  obtain ⟨_, _⟩ := ((isDense_tfae F).out 1 3).1 ‹F.IsDense›
  exact (inferInstance : (restrictYoneda F).ReflectsIsomorphisms)

/-- `ALGD-C2-KAN-41` (定理 41, p.37).
For small `C`, `D` and `F : C → D`, with `F†, F‡ : Ĉ → D̂`, the following are equivalent:
(1) `F` is fully faithful; (2) `F†` is fully faithful; (3) `F‡` is fully faithful. -/
theorem lan_fullyFaithful_tfae {D : Type v} [SmallCategory D] (F : C ⥤ D) :
    List.TFAE [F.Full ∧ F.Faithful, (F.op.lan (H := Type v)).Full ∧ (F.op.lan (H := Type v)).Faithful,
      (F.op.ran (H := Type v)).Full ∧ (F.op.ran (H := Type v)).Faithful] := by
  tfae_have 1 → 2 := by
    rintro ⟨_, _⟩
    let h := (F.op.lanAdjunction (Type v)).fullyFaithfulLOfIsIsoUnit
    exact ⟨h.full, h.faithful⟩
  tfae_have 2 → 1 := by
    rintro ⟨_, _⟩
    obtain ⟨e⟩ := (lan_yoneda F).2
    have : (F ⋙ yoneda).Full := Functor.Full.of_iso e
    have : (F ⋙ yoneda).Faithful := Functor.Faithful.of_iso e
    exact ⟨Functor.Full.of_comp_faithful F yoneda, Functor.Faithful.of_comp F yoneda⟩
  tfae_have 2 ↔ 3 := by
    let t : Adjunction.Triple F.op.lan ((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)).obj F.op) F.op.ran :=
      ⟨F.op.lanAdjunction (Type v), F.op.ranAdjunction (Type v)⟩
    constructor
    · rintro ⟨_, _⟩
      let h := t.fullyFaithfulEquiv (Functor.FullyFaithful.ofFullyFaithful _)
      exact ⟨h.full, h.faithful⟩
    · rintro ⟨_, _⟩
      let h := t.fullyFaithfulEquiv.symm (Functor.FullyFaithful.ofFullyFaithful _)
      exact ⟨h.full, h.faithful⟩
  tfae_finish

section Universal

variable {U : Type u₃} [Category.{v} U]

/-- The bijection `Hom_U(L P, u) ≅ Hom_Ĉ(P, Hom_U(F−, u))` of 定理 45, for a pointwise left Kan
extension `⟨L, η⟩` of `F` along `y`: `k ↦ (x ↦ k ∘ L x̂ ∘ η_c)`. -/
noncomputable def universalHomEquiv (F : C ⥤ U) {L : (Cᵒᵖ ⥤ Type v) ⥤ U} {η : F ⟶ yoneda ⋙ L}
    (h : (LeftExtension.mk L η).IsPointwiseLeftKanExtension) (P : Cᵒᵖ ⥤ Type v) (u : U) :
    (L.obj P ⟶ u) ≃ (P ⟶ (restrictYoneda F).obj u) :=
  (Equiv.ofBijective _ ((isPointwise_iff_bijective L η).1 ⟨h⟩ P u)).trans
    ((yonedaPresheafIso P).symm.homCongr (Iso.refl _))

theorem universalHomEquiv_app (F : C ⥤ U) {L : (Cᵒᵖ ⥤ Type v) ⥤ U} {η : F ⟶ yoneda ⋙ L}
    (h : (LeftExtension.mk L η).IsPointwiseLeftKanExtension) (P : Cᵒᵖ ⥤ Type v) (u : U)
    (k : L.obj P ⟶ u) (c : Cᵒᵖ) (x : P.obj c) :
    (universalHomEquiv F h P u k).app c x = η.app c.unop ≫ L.map (yonedaEquiv.symm x) ≫ k := by
  simp [universalHomEquiv, Iso.homCongr, yonedaPresheafIso, presheafHom]

/-- The universal adjunction `y† F ⊣ F† y` of 定理 45. -/
noncomputable def universalAdjunction (F : C ⥤ U) {L : (Cᵒᵖ ⥤ Type v) ⥤ U}
    {η : F ⟶ yoneda ⋙ L} (h : (LeftExtension.mk L η).IsPointwiseLeftKanExtension) :
    L ⊣ restrictYoneda F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := universalHomEquiv F h
      homEquiv_naturality_left_symm := fun {P' P u} f g ↦ by
        rw [Equiv.symm_apply_eq]
        obtain ⟨k, rfl⟩ := (universalHomEquiv F h P u).surjective g
        rw [Equiv.symm_apply_apply]
        ext c x
        change (universalHomEquiv F h P u k).app c (f.app c x) =
          (universalHomEquiv F h P' u (L.map f ≫ k)).app c x
        rw [universalHomEquiv_app, universalHomEquiv_app, ← yonedaEquiv_symm_naturality_right,
          L.map_comp, Category.assoc]
      homEquiv_naturality_right := fun {P u u'} f g ↦ by
        ext c x
        change (universalHomEquiv F h P u' (f ≫ g)).app c x =
          ((restrictYoneda F).map g).app c ((universalHomEquiv F h P u f).app c x)
        rw [universalHomEquiv_app, universalHomEquiv_app]
        simp }

/-- `ALGD-C2-KAN-45` (定理 45, p.39–40).
For small `C`, `F : C → U` and a pointwise left Kan extension `⟨y† F, η⟩` of `F` along `y`, there
is an adjunction `y† F ⊣ F† y : Ĉ → U`, where `F† y = (u ↦ Hom_U(F−, u))` (系 28). -/
theorem universal_adjunction (F : C ⥤ U) {L : (Cᵒᵖ ⥤ Type v) ⥤ U} {η : F ⟶ yoneda ⋙ L}
    (h : (LeftExtension.mk L η).IsPointwiseLeftKanExtension) :
    Nonempty (L ⊣ restrictYoneda F) :=
  ⟨universalAdjunction F h⟩

/-- `ALGD-C2-KAN-46` (定理 46, p.40).
For small `C`, every adjunction `L ⊣ R : Ĉ → U` arises from 定理 45: with `F := L ∘ y`, `L` is a
pointwise left Kan extension `y† F` (with the identity unit) and `R ≅ F† y`. -/
theorem adjunction_eq_universal {L : (Cᵒᵖ ⥤ Type v) ⥤ U} {R : U ⥤ Cᵒᵖ ⥤ Type v} (adj : L ⊣ R) :
    Nonempty (LeftExtension.mk L (𝟙 (yoneda ⋙ L))).IsPointwiseLeftKanExtension ∧
    Nonempty (R ≅ restrictYoneda (yoneda ⋙ L)) := by
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  obtain ⟨h⟩ := isPointwise_of_preservesColimit (C := C) L
  exact ⟨⟨h⟩, ⟨adj.rightAdjointUniq (universalAdjunction (yoneda ⋙ L) h)⟩⟩

end Universal

/-- `ALGD-C2-KAN-50` (例 50, p.42).
For small `C`, `D` and `F : C → D`: (a) `F† : Ĉ → D̂` is a pointwise left Kan extension along `y`
of `F† ∘ y`, and `F† ∘ y ≅ y ∘ F` (定理 34), so `F† ≅ y†(yF)`; (b) `F⁻¹ ≅ (yF)† y`;
(c) `F⁻¹ : D̂ → Ĉ` is a pointwise left Kan extension along `y` of `F⁻¹ ∘ y = F† y`, so
`F⁻¹ ≅ y†(F† y)`; (d) `F‡ ≅ (F† y)† y`. -/
theorem presheaf_functors_as_kanExtensions {D : Type v} [SmallCategory D] (F : C ⥤ D) :
    (Nonempty (LeftExtension.mk F.op.lan (𝟙 (yoneda ⋙ F.op.lan))).IsPointwiseLeftKanExtension ∧
      Nonempty (yoneda ⋙ F.op.lan ≅ F ⋙ yoneda)) ∧
    Nonempty ((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)).obj F.op ≅ restrictYoneda (F ⋙ yoneda)) ∧
    Nonempty (LeftExtension.mk ((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)).obj F.op)
      (𝟙 (restrictYoneda F))).IsPointwiseLeftKanExtension ∧
    Nonempty (F.op.ran ≅ restrictYoneda (restrictYoneda F)) := by
  obtain ⟨hl, ⟨el⟩⟩ := adjunction_eq_universal (F.op.lanAdjunction (Type v))
  obtain ⟨e⟩ := (lan_yoneda F).2
  obtain ⟨hr, ⟨er⟩⟩ := adjunction_eq_universal (F.op.ranAdjunction (Type v))
  refine ⟨⟨hl, ⟨e⟩⟩, ⟨el ≪≫ isoWhiskerLeft yoneda
    ((whiskeringLeft _ _ _).mapIso (NatIso.op e.symm))⟩, hr, ⟨er⟩⟩

end Small

/-! ### §5: adjunctions between `Set` and `Set` or `Set^op` (例 47–49) -/

section SetAdjunctions

/-- The functor `− × x : Set → Set`. -/
def prodRight (x : Type v) : Type v ⥤ Type v where
  obj X := X × x
  map f := ↾ fun p ↦ (f p.1, p.2)

/-- `− × x ⊣ Hom_Set(x, −)` (currying). -/
def prodRightAdjunction (x : Type v) : prodRight x ⊣ coyoneda.obj (op x) :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ Y :=
        { toFun f := ↾ fun a ↦ ↾ fun b ↦ f (a, b)
          invFun g := ↾ fun p ↦ let h : x ⟶ Y := g p.1; h p.2
          left_inv _ := rfl
          right_inv _ := rfl }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

/-- For `L ⊣ R` out of `Set`, `R ≅ Hom(L 1, −)`. -/
noncomputable def rightAdjointIsoCoyoneda {V : Type u₄} [Category.{v} V] {L : Type v ⥤ V}
    {R : V ⥤ Type v} (adj : L ⊣ R) : R ≅ coyoneda.obj (op (L.obj PUnit)) :=
  (Functor.rightUnitor R).symm ≪≫ isoWhiskerLeft R Coyoneda.punitIso.symm ≪≫
    (adj.corepresentableBy PUnit).toIso.symm

/-- `ALGD-C2-KAN-47` (例 47, p.40–41).
Every adjunction `L ⊣ R : Set → Set` is `− × x ⊣ Hom_Set(x, −)` with `x := L(1)`: `R ≅ Hom(x, −)`
and `L ≅ − × x`. Hence every equivalence `Set → Set` is isomorphic to the identity. The source
derives the first part from 定理 46 with `C = 1`; here it follows from the uniqueness of
adjoints, and the second part from applying the first to the inverse adjunction. -/
theorem types_adjunction :
    (∀ {L R : Type v ⥤ Type v}, (L ⊣ R) →
      Nonempty (R ≅ coyoneda.obj (op (L.obj PUnit))) ∧ Nonempty (L ≅ prodRight (L.obj PUnit))) ∧
    ∀ e : Type v ≌ Type v, Nonempty (e.functor ≅ 𝟭 _) := by
  refine ⟨fun {L R} adj ↦ ⟨⟨rightAdjointIsoCoyoneda adj⟩,
    ⟨adj.leftAdjointUniq ((prodRightAdjunction _).ofNatIsoRight
      (rightAdjointIsoCoyoneda adj).symm)⟩⟩, fun e ↦ ?_⟩
  let eR : e.functor ≅ coyoneda.obj (op (e.inverse.obj PUnit)) :=
    rightAdjointIsoCoyoneda e.symm.toAdjunction
  have ht : IsTerminal (e.inverse.obj PUnit) :=
    IsTerminal.isTerminalObj e.inverse PUnit Types.isTerminalPUnit
  let i : e.inverse.obj PUnit ≅ PUnit := ht.uniqueUpToIso Types.isTerminalPUnit
  exact ⟨eR ≪≫ coyoneda.mapIso i.op.symm ≪≫ Coyoneda.punitIso⟩

/-- `Hom_Set(−, x) ⊣ Hom_Set(−, x) : Set → Set^op` (swap of arguments). -/
def yonedaSelfAdjunction (x : Type v) : (yoneda.obj x).rightOp ⊣ yoneda.obj x :=
  Adjunction.mkOfHomEquiv
    { homEquiv b a :=
        { toFun f := ↾ fun p ↦ ↾ fun q ↦ let h : b ⟶ x := f.unop q; h p
          invFun g := (↾ fun q ↦ ↾ fun p ↦ let h : unop a ⟶ x := g p; h q).op
          left_inv _ := rfl
          right_inv _ := rfl }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

/-- `ALGD-C2-KAN-48` (例 48, p.41).
Every adjunction `L ⊣ R : Set → Set^op` has `R ≅ Hom_Set(−, x)` and `L ≅ Hom_Set(−, x)` (as a
functor to `Set^op`), where `x := L(1)`. Footnote 6: more precisely `L ≅ R^op`. -/
theorem types_op_adjunction {L : Type v ⥤ (Type v)ᵒᵖ} {R : (Type v)ᵒᵖ ⥤ Type v} (adj : L ⊣ R) :
    Nonempty (R ≅ yoneda.obj (unop (L.obj PUnit))) ∧
    Nonempty (L ≅ (yoneda.obj (unop (L.obj PUnit))).rightOp) := by
  let e : coyoneda.obj (op (L.obj PUnit)) ≅ yoneda.obj (unop (L.obj PUnit)) :=
    NatIso.ofComponents (fun a ↦ Equiv.toIso (opEquiv _ _)) fun _ ↦ rfl
  let eR := rightAdjointIsoCoyoneda adj ≪≫ e
  exact ⟨⟨eR⟩, ⟨adj.leftAdjointUniq ((yonedaSelfAdjunction _).ofNatIsoRight eR.symm)⟩⟩

/-- `ALGD-C2-KAN-49` (例 49, p.41–42).
For small `J` and `T : J → Set`, `lim T ≅ Hom_{Set^J}(∆1, T)`. The source obtains this from the
adjunction `∆ ⊣ lim` and 定理 46; here it is the description of limits in `Set` by sections. -/
theorem limit_iso_hom_const {J : Type v} [SmallCategory J] (T : J ⥤ Type v) :
    Nonempty (limit T ≅ ((const J).obj PUnit ⟶ T)) :=
  ⟨Equiv.toIso ((Types.limitEquivSections T).trans (T.sectionsEquivHom PUnit))⟩

end SetAdjunctions

/-! ### §5: presheaf categories (定理 51) -/

section PresheafCategories

/-- `ALGD-C2-KAN-D12` (定義 (small projective), p.42).
An object `a ∈ C` is small projective iff `Hom_C(a, −) : C → Set` is cocontinuous (preserves
small colimits). -/
def IsSmallProjective {E : Type u₂} [Category.{v} E] (a : E) : Prop :=
  PreservesColimits (coyoneda.obj (op a))

/-- For `L ⊣ R`, `Hom(L X, −) ≅ Hom(X, R −)`. -/
def coyonedaLeftAdjointIso {X' : Type u₁} [Category.{v} X'] {E : Type u₂} [Category.{v} E]
    {L : X' ⥤ E} {R : E ⥤ X'} (adj : L ⊣ R) (X : X') :
    coyoneda.obj (op (L.obj X)) ≅ R ⋙ coyoneda.obj (op X) :=
  NatIso.ofComponents (fun Y ↦ Equiv.toIso (adj.homEquiv X Y)) fun g ↦ by
    ext f
    exact adj.homEquiv_naturality_right f g

variable {A : Type v} [SmallCategory A] {E : Type u₂} [Category.{v} E]

/-- `(⇐)` of 定理 51: if `E` is cocomplete and `F : A → E` is fully faithful, strongly generating,
and every `F a` is small projective, then `F † y = (c ↦ Hom_E(F−, c)) : E → Â` is an
equivalence. -/
theorem restrictYoneda_isEquivalence [HasColimits E] (F : A ⥤ E) [F.Full] [F.Faithful]
    (hsg : IsStronglyGenerating F) (hsp : ∀ a, IsSmallProjective (F.obj a)) :
    (restrictYoneda F).IsEquivalence := by
  let R := restrictYoneda F
  have : R.ReflectsIsomorphisms := hsg
  -- `R` preserves small colimits, since each `Hom(F a, −)` does.
  have hR : PreservesColimits R := by
    apply preservesColimits_of_evaluation
    intro a
    have : PreservesColimits (coyoneda.obj (op (F.obj a.unop))) := hsp a.unop
    exact preservesColimits_of_natIso (Iso.refl (coyoneda.obj (op (F.obj a.unop))))
  -- The unit `y ⇒ R F` is an isomorphism, since `F` is fully faithful.
  have hη : IsIso (restrictYonedaUnit F) := by
    have : ∀ c : A, IsIso ((restrictYonedaUnit F).app c) := fun c ↦ by
      have : ∀ a : Aᵒᵖ, IsIso (((restrictYonedaUnit F).app c).app a) := fun a ↦
        (isIso_iff_bijective _).2 ⟨F.map_injective, F.map_surjective⟩
      exact NatIso.isIso_of_isIso_app _
    exact NatIso.isIso_of_isIso_app _
  have hpt := (restrictYoneda_isPointwise F).1.some
  -- `F` is dense: the canonical cocone at `c` is a colimit.
  have hdense : F.IsDense := by
    rw [isDense_iff]
    refine ⟨fun c ↦ ?_⟩
    let κ := (LeftExtension.mk (𝟭 E) (Functor.rightUnitor F).inv).coconeAt c
    let h : colimit (CostructuredArrow.proj F c ⋙ F) ⟶ c := colimit.desc _ κ
    have hRκ : IsColimit (R.mapCocone κ) := by
      refine (IsColimit.precomposeHomEquiv
        (isoWhiskerLeft (CostructuredArrow.proj F c) (asIso (restrictYonedaUnit F)))
        (R.mapCocone κ)).1 (IsColimit.ofIsoColimit (hpt c) (Cocone.ext (Iso.refl _) ?_))
      intro g
      simp [κ, R, LeftExtension.coconeAt]
    have hRs : IsColimit (R.mapCocone (colimit.cocone (CostructuredArrow.proj F c ⋙ F))) :=
      isColimitOfPreserves R (colimit.isColimit _)
    have : IsIso (R.map h) := by
      let φ : R.mapCocone (colimit.cocone (CostructuredArrow.proj F c ⋙ F)) ⟶ R.mapCocone κ :=
        { hom := R.map h
          w := fun g ↦ by
            simp only [Functor.mapCocone_ι_app, colimit.cocone_ι, ← R.map_comp, h,
              colimit.ι_desc] }
      have := IsColimit.hom_isIso hRs hRκ φ
      exact (Cocone.forget _).map_isIso φ
    have : IsIso h := isIso_of_reflects_iso h R
    exact IsColimit.ofIsoColimit (colimit.isColimit _)
      (Cocone.ext (asIso h) fun g ↦ colimit.ι_desc _ _)
  obtain ⟨hfull, hfaith⟩ := ((isDense_tfae F).out 1 3).1 hdense
  -- `R` is essentially surjective: every presheaf is a colimit of representables.
  have hess : R.EssSurj := by
    refine ⟨fun P ↦ ⟨colimit (CostructuredArrow.proj yoneda P ⋙ F), ⟨?_⟩⟩⟩
    exact IsColimit.coconePointsIsoOfNatIso
      (isColimitOfPreserves R (colimit.isColimit (CostructuredArrow.proj yoneda P ⋙ F)))
      (Presheaf.isColimitTautologicalCocone P)
      (isoWhiskerLeft (CostructuredArrow.proj yoneda P) (asIso (restrictYonedaUnit F)).symm)
  exact {}

/-- `ALGD-C2-KAN-51` (定理 51, p.42–44).
A category `E` is equivalent to `Â` for a small category `A` iff `E` is cocomplete and there are
a small category `A` and a fully faithful `F : A → E` (a small full subcategory up to
equivalence) that is strongly generating and whose objects `F a` are small projective. In that
case `F † y : E → Â` is an equivalence. -/
theorem presheafCategory_iff :
    (∃ (A : Type v) (_ : SmallCategory A), Nonempty (E ≌ (Aᵒᵖ ⥤ Type v))) ↔
      HasColimits E ∧ ∃ (A : Type v) (_ : SmallCategory A) (F : A ⥤ E), F.Full ∧ F.Faithful ∧
        IsStronglyGenerating F ∧ ∀ a, IsSmallProjective (F.obj a) := by
  constructor
  · rintro ⟨A, _, ⟨e⟩⟩
    have : HasColimits E := Adjunction.has_colimits_of_equivalence e.functor
    let F : A ⥤ E := yoneda ⋙ e.inverse
    have : F.IsDense := inferInstance
    refine ⟨inferInstance, A, inferInstance, F, inferInstance, inferInstance,
      isStronglyGenerating_of_isDense F, fun a ↦ ?_⟩
    have : PreservesColimits (coyoneda.obj (op (yoneda.obj a))) :=
      ⟨fun {_} _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩
    have : PreservesColimits (e.functor ⋙ coyoneda.obj (op (yoneda.obj a))) :=
      comp_preservesColimits _ _
    have : PreservesColimits (coyoneda.obj (op (e.inverse.obj (yoneda.obj a)))) :=
      preservesColimits_of_natIso (coyonedaLeftAdjointIso e.symm.toAdjunction _).symm
    exact this
  · rintro ⟨_, A, _, F, _, _, hsg, hsp⟩
    have := restrictYoneda_isEquivalence F hsg hsp
    exact ⟨A, inferInstance, ⟨(restrictYoneda F).asEquivalence⟩⟩

end PresheafCategories

/-! ### §2: presheaves on a topological space (例 9) -/

section TopologicalSpaces

open TopologicalSpace TopCat

/-- `ALGD-C2-KAN-09` (例 9, p.9–10).
For a continuous `f : X → Y`, the direct image `f_* P (U) := P(f⁻¹ U)` is `F⁻¹` for
`F := (f⁻¹)^op : O_Y^op → O_X^op`, the inverse image `f^*` is the left Kan extension `F†`, and
`f^* ⊣ f_*`. In mathlib the first two are the definitions of `TopCat.Presheaf.pushforward` and
`TopCat.Presheaf.pullback`. -/
theorem pullback_pushforward {X Y : TopCat.{v}} (f : X ⟶ Y) :
    Presheaf.pushforward (Type v) f = (whiskeringLeft _ _ _).obj (Opens.map f).op ∧
    Presheaf.pullback (Type v) f = (Opens.map f).op.lan ∧
    Nonempty (Presheaf.pullback (Type v) f ⊣ Presheaf.pushforward (Type v) f) :=
  ⟨rfl, rfl, ⟨Presheaf.pullbackPushforwardAdjunction (Type v) f⟩⟩

/-- `ALGD-C2-KAN-10` (formula (10), p.10).
The inverse image is computed by the pointwise formula `f^* P(U) ≅ colim_{V ⊃ f(U)} P(V)`: the
value at `U` is the colimit over `F ↓ U`, and `⟨V, h⟩ ∈ F ↓ U` iff `V ⊃ f(U)`. -/
theorem pullback_obj_iso_colimit {X Y : TopCat.{v}} (f : X ⟶ Y) (P : Y.Presheaf (Type v))
    (U : Opens X) :
    Nonempty (((Presheaf.pullback (Type v) f).obj P).obj (op U) ≅
      colimit (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ P)) ∧
    ∀ V : Opens Y, Nonempty ((Opens.map f).op.obj (op V) ⟶ op U) ↔ f '' U ⊆ V := by
  refine ⟨⟨(Opens.map f).op.leftKanExtensionObjIsoColimit P (op U)⟩, fun V ↦ ?_⟩
  rw [Set.image_subset_iff]
  exact ⟨fun ⟨h⟩ ↦ leOfHom h.unop, fun h ↦ ⟨(homOfLE h).op⟩⟩

end TopologicalSpaces


/-! ## §5 The universal adjunction -/

/-- `ALGD-C2-KAN-54` (定理 54, p.45–51).
For a presheaf `P` on a small category `C` there is an equivalence `(y ↓ P)^ ≃ Ĉ/P`. In
particular, for `P = y(a)`, `y ↓ y(a) ≃ C/a` gives `(C/a)^ ≃ Ĉ/y(a)`. The source proves this
from 定理 51; mathlib's `overEquivPresheafCostructuredArrow` is a direct construction. -/
theorem over_presheaf_equivalence {C : Type v} [SmallCategory C] (P : Cᵒᵖ ⥤ Type v) :
    Nonempty (((CostructuredArrow yoneda P)ᵒᵖ ⥤ Type v) ≌ Over P) ∧
    ∀ a : C, Nonempty (((Over a)ᵒᵖ ⥤ Type v) ≌ Over (yoneda.obj a)) := by
  refine ⟨⟨(overEquivPresheafCostructuredArrow P).symm⟩, fun a ↦ ?_⟩
  let e : Over a ≌ CostructuredArrow yoneda (yoneda.obj a) :=
    (CostructuredArrow.post (𝟭 C) yoneda a).asEquivalence.trans
      (CostructuredArrow.mapNatIso (Functor.leftUnitor yoneda))
  exact ⟨e.op.congrLeft.trans (overEquivPresheafCostructuredArrow (yoneda.obj a)).symm⟩

/-! ## Axiom audit

Each verified declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. The
output is pinned with `#guard_msgs`, so `lake build` fails if it changes. -/

/-- info: 'ProjectEpisteme.AlgD.Kan.isLeftKanExtension_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.isLeftKanExtension_iff

/-- info: 'ProjectEpisteme.AlgD.Kan.isRightKanExtension_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.isRightKanExtension_iff

/-- info: 'ProjectEpisteme.AlgD.Kan.IsLeftKanLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.IsLeftKanLift

/-- info: 'ProjectEpisteme.AlgD.Kan.representable_iff_hasLeftKanExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.representable_iff_hasLeftKanExtension

/-- info: 'ProjectEpisteme.AlgD.Kan.lan_ran_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.lan_ran_adjunction

/-- info: 'ProjectEpisteme.AlgD.Kan.colimit_iff_isLeftKanExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.colimit_iff_isLeftKanExtension

/-- info: 'ProjectEpisteme.AlgD.Kan.pointwise_leftKanExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.pointwise_leftKanExtension

/-- info: 'ProjectEpisteme.AlgD.Kan.hasLeftKanExtension_of_cocomplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.hasLeftKanExtension_of_cocomplete

/-- info: 'ProjectEpisteme.AlgD.Kan.presheaf_hasLeftKanExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.presheaf_hasLeftKanExtension

/-- info: 'ProjectEpisteme.AlgD.Kan.presheaf_lan_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.presheaf_lan_adjunction

/-- info: 'ProjectEpisteme.AlgD.Kan.pointwise_rightKanExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.pointwise_rightKanExtension

/-- info: 'ProjectEpisteme.AlgD.Kan.hasRightKanExtension_of_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.hasRightKanExtension_of_complete

/-- info: 'ProjectEpisteme.AlgD.Kan.preimage_adjoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.preimage_adjoints

/-- info: 'ProjectEpisteme.AlgD.Kan.leftKanExtension_not_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.leftKanExtension_not_pointwise

/-- info: 'ProjectEpisteme.AlgD.Kan.coconeAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.coconeAt_eq

/-- info: 'ProjectEpisteme.AlgD.Kan.pointwiseLeftKanExtension_isPointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.pointwiseLeftKanExtension_isPointwise

/-- info: 'ProjectEpisteme.AlgD.Kan.isPointwise_isLeftKanExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.isPointwise_isLeftKanExtension

/-- info: 'ProjectEpisteme.AlgD.Kan.commutesWith_iff_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.commutesWith_iff_preserves

/-- info: 'ProjectEpisteme.AlgD.Kan.commutesWith_of_preservesColimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.commutesWith_of_preservesColimit

/-- info: 'ProjectEpisteme.AlgD.Kan.IsAbsoluteLeftKanExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.IsAbsoluteLeftKanExtension

/-- info: 'ProjectEpisteme.AlgD.Kan.isAbsoluteLeftKanExtension_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.isAbsoluteLeftKanExtension_iff

/-- info: 'ProjectEpisteme.AlgD.Kan.isLeftAdjoint_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.isLeftAdjoint_tfae

/-- info: 'ProjectEpisteme.AlgD.Kan.hasTerminal_iff_hasColimit_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.hasTerminal_iff_hasColimit_id

/-- info: 'ProjectEpisteme.AlgD.Kan.colimit_of_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.colimit_of_terminal

/-- info: 'ProjectEpisteme.AlgD.Kan.IsAbsoluteRightKanExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.IsAbsoluteRightKanExtension

/-- info: 'ProjectEpisteme.AlgD.Kan.isRightAdjoint_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.isRightAdjoint_tfae

/-- info: 'ProjectEpisteme.AlgD.Kan.isLeftAdjoint_tfae_kanLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.isLeftAdjoint_tfae_kanLift

/-- info: 'ProjectEpisteme.AlgD.Kan.isRightAdjoint_tfae_kanLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.isRightAdjoint_tfae_kanLift

/-- info: 'ProjectEpisteme.AlgD.Kan.leftAdjoint_commutesWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.leftAdjoint_commutesWith

/-- info: 'ProjectEpisteme.AlgD.Kan.yoneda_lan_yoneda' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.yoneda_lan_yoneda

/-- info: 'ProjectEpisteme.AlgD.Kan.yoneda_isLeftKanExtension_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.yoneda_isLeftKanExtension_id

/-- info: 'ProjectEpisteme.AlgD.Kan.presheaf_colimit_of_representables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.presheaf_colimit_of_representables

/-- info: 'ProjectEpisteme.AlgD.Kan.costructuredArrow_mk_isTerminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.costructuredArrow_mk_isTerminal

/-- info: 'ProjectEpisteme.AlgD.Kan.isRepresentable_iff_hasTerminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.isRepresentable_iff_hasTerminal

/-- info: 'ProjectEpisteme.AlgD.Kan.lan_yoneda' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.lan_yoneda

/-- info: 'ProjectEpisteme.AlgD.Kan.unit_isIso_of_fullyFaithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.unit_isIso_of_fullyFaithful

/-- info: 'ProjectEpisteme.AlgD.Kan.isDense_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.isDense_iff

/-- info: 'ProjectEpisteme.AlgD.Kan.yoneda_isDense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.yoneda_isDense

/-- info: 'ProjectEpisteme.AlgD.Kan.over_presheaf_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.over_presheaf_equivalence
/-- info: 'ProjectEpisteme.AlgD.Kan.coconeHomEquiv_natural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.coconeHomEquiv_natural

/-- info: 'ProjectEpisteme.AlgD.Kan.pointwise_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.pointwise_tfae

/-- info: 'ProjectEpisteme.AlgD.Kan.isPointwise_iff_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.isPointwise_iff_bijective

/-- info: 'ProjectEpisteme.AlgD.Kan.pointwiseRight_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.pointwiseRight_tfae

/-- info: 'ProjectEpisteme.AlgD.Kan.isPointwise_of_isAbsolute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.isPointwise_of_isAbsolute

/-- info: 'ProjectEpisteme.AlgD.Kan.restrictYoneda_isPointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.restrictYoneda_isPointwise

/-- info: 'ProjectEpisteme.AlgD.Kan.restrictYonedaUnit_yonedaEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.restrictYonedaUnit_yonedaEquiv

/-- info: 'ProjectEpisteme.AlgD.Kan.lan_comp_restrictYoneda' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.lan_comp_restrictYoneda

/-- info: 'ProjectEpisteme.AlgD.Kan.lan_yoneda_coyoneda' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.lan_yoneda_coyoneda

/-- info: 'ProjectEpisteme.AlgD.Kan.fullyFaithful_of_isIso_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.fullyFaithful_of_isIso_unit

/-- info: 'ProjectEpisteme.AlgD.Kan.restrictYonedaUnit_app_app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.restrictYonedaUnit_app_app

/-- info: 'ProjectEpisteme.AlgD.Kan.fullyFaithful_iff_isIso_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.fullyFaithful_iff_isIso_unit

/-- info: 'ProjectEpisteme.AlgD.Kan.lan_fullyFaithful_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.lan_fullyFaithful_tfae

/-- info: 'ProjectEpisteme.AlgD.Kan.IsStronglyGenerating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.IsStronglyGenerating

/-- info: 'ProjectEpisteme.AlgD.Kan.isDense_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.isDense_tfae

/-- info: 'ProjectEpisteme.AlgD.Kan.isStronglyGenerating_of_isDense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.isStronglyGenerating_of_isDense

/-- info: 'ProjectEpisteme.AlgD.Kan.universal_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.universal_adjunction

/-- info: 'ProjectEpisteme.AlgD.Kan.adjunction_eq_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.adjunction_eq_universal

/-- info: 'ProjectEpisteme.AlgD.Kan.types_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.types_adjunction

/-- info: 'ProjectEpisteme.AlgD.Kan.types_op_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.types_op_adjunction

/-- info: 'ProjectEpisteme.AlgD.Kan.limit_iso_hom_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.limit_iso_hom_const

/-- info: 'ProjectEpisteme.AlgD.Kan.presheaf_functors_as_kanExtensions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.presheaf_functors_as_kanExtensions

/-- info: 'ProjectEpisteme.AlgD.Kan.IsSmallProjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.IsSmallProjective

/-- info: 'ProjectEpisteme.AlgD.Kan.presheafCategory_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.presheafCategory_iff

/-- info: 'ProjectEpisteme.AlgD.Kan.pullback_pushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.pullback_pushforward

/-- info: 'ProjectEpisteme.AlgD.Kan.pullback_obj_iso_colimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Kan.pullback_obj_iso_colimit

end ProjectEpisteme.AlgD.Kan

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

/-- `ALGD-C2-KAN-17` (定理 17, p.19–20).
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

/-- `ALGD-C2-KAN-19` (命題 19, p.21).
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
end ProjectEpisteme.AlgD.Kan

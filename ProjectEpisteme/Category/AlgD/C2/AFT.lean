module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Generator.Type
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.CategoryTheory.Subobject.WellPowered
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Tactic.TFAE

/-!
# alg-d, Chapter 2: 随伴関手定理 (Adjoint functor theorems)

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 2, `aft.pdf`
(<https://alg-d.com/math/kan_extension/aft.pdf>), printed date 2026-07-16,
SHA-256 `05fbabffc4936126fc619d6090383175028c0491793f7a2e44ea84068608f635`,
retrieved 2026-11-26. Ledger: `docs/ledger/algd/C2-AFT.md`.

## Conventions

* Categories are locally small: `C : Type u` with `[Category.{v} C]`, and Set is `Type v`.
  Complete and cocomplete mean `HasLimits` and `HasColimits` (size `v`), and continuous and
  cocontinuous mean `PreservesLimits` and `PreservesColimits`.
* A subset `S ⊂ Ob(C)` is an `ObjectProperty C`; "S is a set" is `ObjectProperty.Small.{v} S`.
* The source's final functor (`IsFinalColim`) quantifies over all categories `C` and functors
  `F : J → C`. Lean fixes the universes of `C`; 命題 8 shows that for small `I` the notion agrees
  with mathlib's `Functor.Final` (connected comma categories).
* `c ↓ id_C` is mathlib's `Under c`. `Epi_c` is the full subcategory of epimorphisms out of `c`,
  and `Quot_c` is mathlib's `Skeleton` of it.
* The source derives the adjoint functor theorems from Kan extensions (定理 1 and 補題 4). Here
  定理 10 is proved by dualizing mathlib's general adjoint functor theorem, and 定理 18 and
  定理 20 are mathlib's special adjoint functor theorems, through bridges for well-copowered
  categories and generating sets.
* 補題 5 needs the added hypothesis that `H` commutes with `F†E` (for its pointwise clause, that
  `F†E` is pointwise); `commutesWith_comp_counterexample` shows that the statement as printed fails.
* 例 21 (CptHaus and the Stone–Čech compactification) is in `AFTTop.lean`, so that this module
  does not import topology.
* 定理 1, 命題 2 and 定理 3 restate results of 「Kan拡張」. Their rows point to the declarations in
  `ProjectEpisteme/Category/AlgD/C2/Kan.lean`, whose docstrings carry both IDs.
-/

@[expose] public section

namespace ProjectEpisteme.AlgD.AFT

open CategoryTheory Limits Functor Opposite

universe w w' v v₁ v₂ v₃ v₄ v₅ u u₁ u₂ u₃ u₄ u₅

/-! ## Final functors -/

section Final

variable {I : Type u₁} [Category.{v₁} I] {J : Type u₂} [Category.{v₂} J]

/-- `ALGD-C2-AFT-D01` (定義 (終関手), p.2–3, footnote 1).
`K : I → J` is final iff for every category `C` and functor `F : J → C`, if `colim FK` exists,
then `colim F` exists and the canonical morphism `colim FK → colim F` is an isomorphism. The
category `C` ranges over `Type w` with morphisms in `Type w'`. (Footnote 1: some texts say
cofinal.) -/
def IsFinalColim (K : I ⥤ J) : Prop :=
  ∀ (C : Type w) [Category.{w'} C] (F : J ⥤ C) [HasColimit (K ⋙ F)],
    ∃ _ : HasColimit F, IsIso (colimit.pre F K)

/-- A final functor in mathlib's sense (all `j ↓ K` connected) is final in the source's sense,
for categories `C` in every universe. -/
theorem isFinalColim_of_final (K : I ⥤ J) [K.Final] : IsFinalColim.{w, w'} K :=
  fun _ _ F _ ↦
    have : HasColimit F := Final.hasColimit_of_comp K
    ⟨this, inferInstance⟩

/-- `ALGD-C2-AFT-R01` (prose after 定義 (終関手), p.3).
In terms of Kan extensions, `K` is final iff for every `F : J → C` such that `colim FK` exists,
`colim F` exists and the restricted cocone `⟨colim F, νK⟩` is a left Kan extension of `FK`
along `! : I → 1`, i.e. a colimit of `FK`. -/
theorem isFinalColim_iff_isColimit_whisker (K : I ⥤ J) :
    IsFinalColim.{w, w'} K ↔ ∀ (C : Type w) [Category.{w'} C] (F : J ⥤ C) [HasColimit (K ⋙ F)],
      ∃ _ : HasColimit F, Nonempty (IsColimit ((colimit.cocone F).whisker K)) := by
  refine forall_congr' fun C ↦ forall_congr' fun _ ↦ forall_congr' fun F ↦
    forall_congr' fun _ ↦ exists_congr fun _ ↦ ?_
  constructor
  · intro h
    exact ⟨@IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (K ⋙ F)) h⟩
  · rintro ⟨hs⟩
    refine ⟨hs.desc (colimit.cocone (K ⋙ F)), ?_, ?_⟩
    · refine colimit.hom_ext fun i ↦ ?_
      rw [colimit.ι_pre_assoc, Category.comp_id]
      exact hs.fac _ i
    · refine hs.hom_ext fun i ↦ ?_
      rw [← Category.assoc, hs.fac]
      simp

/-- `ALGD-C2-AFT-06` (命題 6, p.5–6).
A right adjoint functor is final. -/
theorem isFinalColim_of_isRightAdjoint (K : I ⥤ J) [K.IsRightAdjoint] :
    IsFinalColim.{w, w'} K :=
  isFinalColim_of_final K

/-- `ALGD-C2-AFT-07` (例 7, p.6).
A functor that is an equivalence of categories is final. -/
theorem isFinalColim_of_isEquivalence (K : I ⥤ J) [K.IsEquivalence] :
    IsFinalColim.{w, w'} K :=
  isFinalColim_of_final K

/-- `ALGD-C2-AFT-D03` (定義 (連結), p.6).
A category is connected iff it is nonempty and any two objects are joined by a zigzag. -/
theorem isConnected_iff_zigzag (X : Type u₁) [Category.{v₁} X] :
    IsConnected X ↔ Nonempty X ∧ ∀ a b : X, Zigzag a b :=
  ⟨fun _ ↦ ⟨inferInstance, isPreconnected_zigzag⟩,
    fun ⟨_, h⟩ ↦ zigzag_isConnected h⟩

/-- `ALGD-C2-AFT-08` (命題 8, p.6–8).
For a small category `I`, a category `J` and `K : I → J` the following are equivalent:
(1) `K` is final; (2) for every `F : J → Set`, `colim F` exists and the canonical morphism
`colim FK → colim F` is an isomorphism; (3) `colim Hom_J(j, K−) ≅ 1` for every `j`;
(4) `j ↓ K` is connected for every `j`. In (1) the categories `C` range over `Type v`-sized
categories; by `isFinalColim_of_final`, (4) gives (1) for categories in every universe. -/
theorem isFinalColim_tfae {I : Type v} [SmallCategory I] {J : Type u} [Category.{v} J]
    (K : I ⥤ J) :
    List.TFAE [IsFinalColim.{v + 1, v} K,
      ∀ F : J ⥤ Type v, ∃ _ : HasColimit F, IsIso (colimit.pre F K),
      ∀ j : J, Nonempty (colimit (K ⋙ coyoneda.obj (op j)) ≅ PUnit),
      ∀ j : J, IsConnected (StructuredArrow j K)] := by
  tfae_have 1 → 2 := fun h F ↦ h (Type v) F
  tfae_have 2 → 3 := fun h j ↦ by
    obtain ⟨_, _⟩ := h (coyoneda.obj (op j))
    exact ⟨Final.colimitCompCoyonedaIso K j⟩
  tfae_have 3 → 4 := fun h ↦ (final_of_colimit_comp_coyoneda_iso_pUnit K fun j ↦ (h j).some).out
  tfae_have 4 → 1 := fun h ↦
    have : K.Final := ⟨h⟩
    isFinalColim_of_final K
  tfae_finish

/-- `ALGD-C2-AFT-09` (例 9, p.8–9).
For `c ∈ C`, let `K : 1 → C` pick `c`. Then `c` is terminal iff `K` is final. -/
theorem nonempty_isTerminal_iff_isFinalColim {C : Type u} [Category.{v} C] (c : C) :
    Nonempty (IsTerminal c) ↔ IsFinalColim.{v + 1, v} (Functor.fromPUnit.{v} c) := by
  constructor
  · rintro ⟨hc⟩
    have := final_fromPUnit_of_isTerminal hc
    exact isFinalColim_of_final _
  · intro h
    have hK := ((isFinalColim_tfae (Functor.fromPUnit.{v} c)).out 1 4).1 h
    refine ⟨IsTerminal.ofUniqueHom
      (fun a ↦ (have := hK a; Classical.arbitrary (StructuredArrow a (fromPUnit.{v} c))).hom)
      fun a f ↦ ?_⟩
    have := hK a
    exact constant_of_preserves_morphisms (α := a ⟶ c)
      (fun X : StructuredArrow a (Functor.fromPUnit.{v} c) ↦ X.hom)
      (fun X Y g ↦ by simpa using StructuredArrow.w g)
      (StructuredArrow.mk (Y := ⟨PUnit.unit⟩) f) _

end Final

/-! ## The general adjoint functor theorem -/

section GAFT

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-- The solution set condition for `F ↓ d` (定理 10): for every `d ∈ D` there is a set
`S ⊂ Ob(F ↓ d)`, here a family `⟨B i, k i⟩` indexed by `ι : Type v`, such that every
`⟨c, f⟩ ∈ F ↓ d` has a morphism `g : ⟨c, f⟩ → ⟨B i, k i⟩`, i.e. `k i ∘ F g = f`. -/
def LeftSolutionSetCondition (F : C ⥤ D) : Prop :=
  ∀ d : D, ∃ (ι : Type v) (B : ι → C) (k : ∀ i, F.obj (B i) ⟶ d),
    ∀ (c : C) (f : F.obj c ⟶ d), ∃ (i : ι) (g : c ⟶ B i), F.map g ≫ k i = f

lemma solutionSetCondition_op {F : C ⥤ D} (hF : LeftSolutionSetCondition F) :
    SolutionSetCondition.{v} F.op := fun A ↦ by
  obtain ⟨ι, B, k, hk⟩ := hF A.unop
  refine ⟨ι, fun i ↦ op (B i), fun i ↦ (k i).op, fun X h ↦ ?_⟩
  obtain ⟨i, g, hg⟩ := hk X.unop h.unop
  exact ⟨i, g.op, Quiver.Hom.unop_inj (by simpa using hg)⟩

/-- `ALGD-C2-AFT-10` (定理 10 (一般随伴関手定理), p.9–11).
Let `C` be cocomplete and `F : C → D` cocontinuous. If `F` satisfies the solution set condition
(for every `d ∈ D` a set `S ⊂ Ob(F ↓ d)` such that every object of `F ↓ d` has a morphism to some
member of `S`), then `F` is a left adjoint. -/
theorem isLeftAdjoint_of_leftSolutionSetCondition [HasColimits C] (F : C ⥤ D)
    [PreservesColimits F] (hF : LeftSolutionSetCondition F) : F.IsLeftAdjoint := by
  have := preservesLimits_op F
  have := isRightAdjoint_of_preservesLimits_of_solutionSetCondition F.op
    (solutionSetCondition_op hF)
  exact ⟨(F.op.leftAdjoint).unop, ⟨(Adjunction.ofIsRightAdjoint F.op).unop⟩⟩

end GAFT

/-! ## Kan extensions along a composite (補題 4) -/

section KanComp

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {B : Type u₃} [Category.{v₃} B] {U : Type u₄} [Category.{v₄} U]

/-- The universal property of a left Kan extension: `⟨T, η⟩` is a left Kan extension of `E`
along `F` iff every `θ : E ⇒ SF` factors as `θ = ρF ∘ η` for a unique `ρ : T ⇒ S`. -/
lemma isLeftKanExtension_iff_existsUnique {F : C ⥤ D} {E : C ⥤ U} (T : D ⥤ U)
    (η : E ⟶ F ⋙ T) :
    T.IsLeftKanExtension η ↔
      ∀ (S : D ⥤ U) (θ : E ⟶ F ⋙ S), ∃! ρ : T ⟶ S, η ≫ whiskerLeft F ρ = θ := by
  constructor
  · intro _ S θ
    refine ⟨T.descOfIsLeftKanExtension η S θ, T.descOfIsLeftKanExtension_fac η S θ,
      fun ρ hρ ↦ ?_⟩
    exact T.hom_ext_of_isLeftKanExtension η _ _ (by rw [hρ, descOfIsLeftKanExtension_fac])
  · intro h
    refine ⟨⟨IsInitial.ofUniqueHom
      (fun s ↦ StructuredArrow.homMk (h s.right s.hom).exists.choose
        (h s.right s.hom).exists.choose_spec) fun s m ↦ ?_⟩⟩
    ext1
    exact (h s.right s.hom).unique (StructuredArrow.w m) (h s.right s.hom).exists.choose_spec

/-- `ALGD-C2-AFT-04` (補題 4, p.3–5).
Let `⟨F†E, η⟩` be a left Kan extension of `E : C → U` along `F : C → D`, and `G : D → B`.
(⇒) If `⟨T, σ⟩` is a left Kan extension of `E` along `GF` and `τ : F†E ⇒ TG` is the morphism
with `σ = τF ∘ η`, then `⟨T, τ⟩` is a left Kan extension of `F†E` along `G`. (⇐) If `⟨T, τ⟩` is a
left Kan extension of `F†E` along `G`, then `⟨T, τF ∘ η⟩` is a left Kan extension of `E` along
`GF`. So `(GF)†E` exists iff `G†(F†E)` exists, and then `(GF)†E ≅ G†(F†E)`. -/
theorem isLeftKanExtension_comp_iff {F : C ⥤ D} {E : C ⥤ U} (L : D ⥤ U) (η : E ⟶ F ⋙ L)
    [L.IsLeftKanExtension η] (G : D ⥤ B) (T : B ⥤ U) (τ : L ⟶ G ⋙ T) :
    T.IsLeftKanExtension (η ≫ whiskerLeft F τ ≫ (Functor.associator F G T).inv) ↔
      T.IsLeftKanExtension τ := by
  rw [isLeftKanExtension_iff_existsUnique, isLeftKanExtension_iff_existsUnique]
  constructor
  · intro h S θ
    obtain ⟨ρ, hρ, hρu⟩ := h S (η ≫ whiskerLeft F θ ≫ (Functor.associator F G S).inv)
    refine ⟨ρ, L.hom_ext_of_isLeftKanExtension η _ _ ?_, fun ρ' hρ' ↦ hρu ρ' ?_⟩
    · ext c
      have := congr_app hρ c
      simp only [NatTrans.comp_app, whiskerLeft_app, Functor.associator_inv_app,
        Category.comp_id, Category.id_comp, Category.assoc] at this ⊢
      exact this
    · rw [← hρ']
      ext c
      simp
  · intro h S θ
    let μ : L ⟶ G ⋙ S :=
      L.descOfIsLeftKanExtension η (G ⋙ S) (θ ≫ (Functor.associator F G S).hom)
    have hμ := L.descOfIsLeftKanExtension_fac η (G ⋙ S) (θ ≫ (Functor.associator F G S).hom)
    obtain ⟨ρ, hρ, hρu⟩ := h S μ
    refine ⟨ρ, ?_, fun ρ' hρ' ↦ hρu ρ' ?_⟩
    · ext c
      have h1 := congr_app hμ c
      have h2 := congr_app hρ (F.obj c)
      simp only [NatTrans.comp_app, whiskerLeft_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.comp_id] at h1 h2 ⊢
      rw [← h1, ← h2, Category.assoc]
      rfl
    · refine L.hom_ext_of_isLeftKanExtension η _ _ ?_
      rw [hμ, ← hρ']
      ext c
      simp

/-- Under the hypotheses of `isLeftKanExtension_comp_iff`, the two extensions agree:
`(GF)†E ≅ G†(F†E)`. -/
noncomputable def leftKanExtensionCompIso {F : C ⥤ D} {E : C ⥤ U} (L : D ⥤ U)
    (η : E ⟶ F ⋙ L) [L.IsLeftKanExtension η] (G : D ⥤ B) (T : B ⥤ U) (σ : E ⟶ (F ⋙ G) ⋙ T)
    [T.IsLeftKanExtension σ] (T' : B ⥤ U) (τ : L ⟶ G ⋙ T') [T'.IsLeftKanExtension τ] :
    T ≅ T' :=
  have : T'.IsLeftKanExtension (η ≫ whiskerLeft F τ ≫ (Functor.associator F G T').inv) :=
    (isLeftKanExtension_comp_iff L η G T' τ).2 inferInstance
  leftKanExtensionUnique T σ T' (η ≫ whiskerLeft F τ ≫ (Functor.associator F G T').inv)

/-- With `⟨F†E, η⟩` a left Kan extension, `(GF)†E` exists iff `G†(F†E)` exists (補題 4). -/
theorem hasLeftKanExtension_comp_iff {F : C ⥤ D} {E : C ⥤ U} (L : D ⥤ U) (η : E ⟶ F ⋙ L)
    [L.IsLeftKanExtension η] (G : D ⥤ B) :
    (F ⋙ G).HasLeftKanExtension E ↔ G.HasLeftKanExtension L := by
  constructor
  · intro _
    let T := (F ⋙ G).leftKanExtension E
    let σ := (F ⋙ G).leftKanExtensionUnit E
    let τ : L ⟶ G ⋙ T := L.descOfIsLeftKanExtension η (G ⋙ T) (σ ≫ (Functor.associator F G T).hom)
    have hσ : η ≫ whiskerLeft F τ ≫ (Functor.associator F G T).inv = σ := by
      rw [← Category.assoc, descOfIsLeftKanExtension_fac, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have : T.IsLeftKanExtension τ := (isLeftKanExtension_comp_iff L η G T τ).1 (hσ ▸ inferInstance)
    exact HasLeftKanExtension.mk T τ
  · intro _
    have := (isLeftKanExtension_comp_iff L η G (G.leftKanExtension L)
      (G.leftKanExtensionUnit L)).2 inferInstance
    exact HasLeftKanExtension.mk _ (η ≫ whiskerLeft F (G.leftKanExtensionUnit L) ≫
      (Functor.associator F G (G.leftKanExtension L)).inv)

/-- `H : U → V` commutes with a left Kan extension `⟨T, η⟩` of `E` along `F` when `⟨HT, Hη⟩` is
a left Kan extension of `HE` along `F`. -/
def CommutesWith {V : Type u₅} [Category.{v₅} V] (H : U ⥤ V) {F : C ⥤ D} {E : C ⥤ U}
    (T : D ⥤ U) (η : E ⟶ F ⋙ T) : Prop :=
  (T ⋙ H).IsLeftKanExtension (whiskerRight η H ≫ (Functor.associator F T H).hom)

/-- `ALGD-C2-AFT-05` (補題 5, p.5), with a hypothesis added.
In the situation of 補題 4 (`⟨F†E, η⟩ = ⟨L, η⟩`, `σ = τF ∘ η`), let `H : U → V` commute with
`F†E`. Then `H` commutes with `⟨T, σ⟩` as `(GF)†E` iff it commutes with `⟨T, τ⟩` as `G†(F†E)`.
The source omits the hypothesis on `F†E`, without which the claim fails
(`commutesWith_comp_counterexample`); its "in particular" clause on pointwise extensions is
`isPointwiseLeftKanExtensionAt_comp_iff`, which assumes `F†E` pointwise. -/
theorem commutesWith_comp_iff {V : Type u₅} [Category.{v₅} V] (H : U ⥤ V) {F : C ⥤ D}
    {E : C ⥤ U} (L : D ⥤ U) (η : E ⟶ F ⋙ L) (hL : CommutesWith H L η) (G : D ⥤ B)
    (T : B ⥤ U) (τ : L ⟶ G ⋙ T) :
    CommutesWith H T (η ≫ whiskerLeft F τ ≫ (Functor.associator F G T).inv) ↔
      CommutesWith H T τ := by
  have : (L ⋙ H).IsLeftKanExtension (whiskerRight η H ≫ (Functor.associator F L H).hom) := hL
  have key := isLeftKanExtension_comp_iff (L ⋙ H)
    (whiskerRight η H ≫ (Functor.associator F L H).hom) G (T ⋙ H)
    (whiskerRight τ H ≫ (Functor.associator G T H).hom)
  have heq : whiskerRight (η ≫ whiskerLeft F τ ≫ (Functor.associator F G T).inv) H ≫
      (Functor.associator (F ⋙ G) T H).hom =
      (whiskerRight η H ≫ (Functor.associator F L H).hom) ≫
        whiskerLeft F (whiskerRight τ H ≫ (Functor.associator G T H).hom) ≫
        (Functor.associator F G (T ⋙ H)).inv := by
    ext c
    simp
  unfold CommutesWith
  rw [heq]
  exact key

/-- The "in particular" clause of 補題 5, with `F†E` pointwise: then `⟨T, τF ∘ η⟩` is a pointwise
left Kan extension along `GF` at `b` iff `⟨T, τ⟩` is one along `G` at `b`. -/
theorem isPointwiseLeftKanExtensionAt_comp_iff {F : C ⥤ D} {E : C ⥤ U} (L : D ⥤ U)
    (η : E ⟶ F ⋙ L) (hL : (LeftExtension.mk L η).IsPointwiseLeftKanExtension) (G : D ⥤ B)
    (T : B ⥤ U) (τ : L ⟶ G ⋙ T) (b : B) :
    Nonempty ((LeftExtension.mk T (η ≫ whiskerLeft F τ ≫
      (Functor.associator F G T).inv)).IsPointwiseLeftKanExtensionAt b) ↔
      Nonempty ((LeftExtension.mk T τ).IsPointwiseLeftKanExtensionAt b) := by
  let cσ := (LeftExtension.mk T (η ≫ whiskerLeft F τ ≫
    (Functor.associator F G T).inv)).coconeAt b
  let cτ := (LeftExtension.mk T τ).coconeAt b
  let cL := fun d ↦ (LeftExtension.mk L η).coconeAt d
  let toG : CostructuredArrow (F ⋙ G) b → CostructuredArrow G b :=
    fun x ↦ CostructuredArrow.mk (Y := F.obj x.left) x.hom
  let pair : ∀ j : CostructuredArrow G b, CostructuredArrow F j.left →
      CostructuredArrow (F ⋙ G) b :=
    fun j i ↦ CostructuredArrow.mk (Y := i.left) (G.map i.hom ≫ j.hom)
  have hσ : ∀ x, cσ.ι.app x = η.app x.left ≫ cτ.ι.app (toG x) := fun x ↦ by
    simp [cσ, cτ, toG, LeftExtension.coconeAt]
  have hLτ : ∀ j i, (cL j.left).ι.app i ≫ cτ.ι.app j = cσ.ι.app (pair j i) := fun j i ↦ by
    simp only [cL, cσ, cτ, pair, LeftExtension.coconeAt, LeftExtension.mk, Category.assoc]
    simp only [StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self, Functor.comp_obj,
      NatTrans.comp_app, whiskerLeft_app, Functor.associator_inv_app,
      CostructuredArrow.mk_left, CostructuredArrow.mk_hom_eq_self, Category.id_comp,
      Functor.map_comp, Category.assoc]
    rw [τ.naturality_assoc]
    rfl
  -- the morphism `toG x ⟶ j` induced by `i : x ⟶ ...`
  have hpair_toG : ∀ (s : Cocone (CostructuredArrow.proj G b ⋙ L)) (j : CostructuredArrow G b)
      (i : CostructuredArrow F j.left),
      L.map i.hom ≫ s.ι.app j = s.ι.app (toG (pair j i)) := fun s j i ↦
    s.w (CostructuredArrow.homMk i.hom (by simp [toG, pair]) : toG (pair j i) ⟶ j)
  constructor
  · rintro ⟨hσc⟩
    let α : Cocone (CostructuredArrow.proj G b ⋙ L) → Cocone (CostructuredArrow.proj (F ⋙ G) b ⋙ E) :=
      fun s ↦
      { pt := s.pt
        ι :=
          { app := fun x ↦ η.app x.left ≫ s.ι.app (toG x)
            naturality := fun x x' t ↦ by
              have := s.w (CostructuredArrow.homMk (F.map t.left) (CostructuredArrow.w t) :
                toG x ⟶ toG x')
              simp only [Functor.comp_obj, CostructuredArrow.proj_obj, Functor.comp_map,
                CostructuredArrow.proj_map, Functor.const_obj_obj, Functor.const_obj_map,
                Category.comp_id] at this ⊢
              rw [← Category.assoc, η.naturality, Category.assoc]
              exact congrArg (η.app x.left ≫ ·) this } }
    refine ⟨{ desc := fun s ↦ hσc.desc (α s), fac := fun s j ↦ ?_, uniq := fun s m hm ↦ ?_ }⟩
    · refine (hL j.left).hom_ext fun i ↦ ?_
      rw [← Category.assoc, hLτ, hσc.fac]
      change η.app i.left ≫ s.ι.app (toG (pair j i)) = (cL j.left).ι.app i ≫ s.ι.app j
      rw [← hpair_toG]
      simp [cL, LeftExtension.coconeAt]
    · refine hσc.uniq (α s) m fun x ↦ ?_
      rw [hσ, Category.assoc, hm]
  · rintro ⟨hτc⟩
    let β : Cocone (CostructuredArrow.proj (F ⋙ G) b ⋙ E) → Cocone (CostructuredArrow.proj G b ⋙ L) :=
      fun s ↦
      { pt := s.pt
        ι :=
          { app := fun j ↦ (hL j.left).desc
              { pt := s.pt
                ι :=
                  { app := fun i ↦ s.ι.app (pair j i)
                    naturality := fun i i' t ↦ by
                      have := s.w (CostructuredArrow.homMk t.left (by
                        simp only [pair, CostructuredArrow.mk_hom_eq_self, Functor.comp_map]
                        rw [← G.map_comp_assoc, CostructuredArrow.w t]) : pair j i ⟶ pair j i')
                      simpa using this } }
            naturality := fun j j' t ↦ by
              refine (hL j.left).hom_ext fun i ↦ ?_
              simp only [Functor.comp_obj, CostructuredArrow.proj_obj, Functor.comp_map,
                CostructuredArrow.proj_map, Functor.const_obj_obj, Functor.const_obj_map,
                Category.comp_id]
              rw [(hL j.left).fac]
              have e1 : (cL j.left).ι.app i ≫ L.map t.left =
                  (cL j'.left).ι.app (CostructuredArrow.mk (Y := i.left) (i.hom ≫ t.left)) := by
                simp [cL, LeftExtension.coconeAt]
              rw [← Category.assoc, e1, (hL j'.left).fac]
              have := s.w (CostructuredArrow.homMk (𝟙 i.left) (by
                simp only [pair, CostructuredArrow.mk_hom_eq_self, Functor.comp_map,
                  Functor.map_comp, Category.assoc, CostructuredArrow.w t]
                erw [F.map_id, G.map_id, Category.id_comp]) :
                  pair j' (CostructuredArrow.mk (Y := i.left) (i.hom ≫ t.left)) ⟶ pair j i)
              erw [E.map_id, Category.id_comp] at this
              exact this.symm } }
    have hβ : ∀ s j i, (cL j.left).ι.app i ≫ (β s).ι.app j = s.ι.app (pair j i) :=
      fun s j i ↦ (hL j.left).fac _ i
    refine ⟨{ desc := fun s ↦ hτc.desc (β s), fac := fun s x ↦ ?_, uniq := fun s m hm ↦ ?_ }⟩
    · rw [hσ, Category.assoc, hτc.fac]
      have h0 : η.app x.left = (cL (toG x).left).ι.app (CostructuredArrow.mk (𝟙 (F.obj x.left))) := by
        simp [cL, toG, LeftExtension.coconeAt]
      rw [h0, hβ]
      have := s.w (CostructuredArrow.homMk (𝟙 x.left) (by simp [pair, toG]) :
        pair (toG x) (CostructuredArrow.mk (𝟙 (F.obj x.left))) ⟶ x)
      erw [E.map_id, Category.id_comp] at this
      exact this.symm
    · refine hτc.uniq (β s) m fun j ↦ (hL j.left).hom_ext fun i ↦ ?_
      rw [← Category.assoc, hLτ, hm, hβ]

/-- The source's 補題 5 fails without the added hypothesis: for `F : ∅ → 1`, `E : ∅ → Set`,
`F†E = ∅` (the initial object), `G = id_1` and `H` the constant functor at `1`, the functor `H`
commutes with `G†(F†E)` (an extension along the identity) but not with `(GF)†E = F†E`. -/
theorem commutesWith_comp_counterexample :
    ∃ (F : Discrete PEmpty.{1} ⥤ Discrete PUnit.{1}) (E : Discrete PEmpty.{1} ⥤ Type)
      (L : Discrete PUnit.{1} ⥤ Type) (η : E ⟶ F ⋙ L) (_ : L.IsLeftKanExtension η)
      (τ : L ⟶ 𝟭 _ ⋙ L) (_ : L.IsLeftKanExtension τ) (H : Type ⥤ Type),
      CommutesWith H L τ ∧
        ¬ CommutesWith H L (η ≫ whiskerLeft F τ ≫ (Functor.associator F (𝟭 _) L).inv) := by
  let F : Discrete PEmpty.{1} ⥤ Discrete PUnit.{1} := Functor.empty _
  let E : Discrete PEmpty.{1} ⥤ Type := Functor.empty _
  let L : Discrete PUnit.{1} ⥤ Type := (Functor.const _).obj PEmpty
  let η : E ⟶ F ⋙ L := { app := fun x ↦ x.as.elim }
  have hL : L.IsLeftKanExtension η := by
    rw [isLeftKanExtension_iff_existsUnique]
    intro S θ
    refine ⟨{ app := fun _ ↦ ↾fun x ↦ x.elim }, by ext x; exact x.as.elim, fun ρ _ ↦ ?_⟩
    ext d x
    exact x.elim
  -- every functor commutes with an extension along the identity whose unit is the identity
  have hid : ∀ X : Discrete PUnit.{1} ⥤ Type, X.IsLeftKanExtension (Functor.leftUnitor X).inv :=
    fun X ↦ by
      rw [isLeftKanExtension_iff_existsUnique]
      intro S θ
      refine ⟨θ ≫ (Functor.leftUnitor S).hom, by ext; simp, fun ρ hρ ↦ ?_⟩
      rw [← hρ]
      ext
      simp
  let H : Type ⥤ Type := (Functor.const _).obj PUnit
  refine ⟨F, E, L, η, hL, (Functor.leftUnitor L).inv, hid L, H, ?_, ?_⟩
  · unfold CommutesWith
    have : whiskerRight (Functor.leftUnitor L).inv H ≫
        (Functor.associator (𝟭 _) L H).hom = (Functor.leftUnitor (L ⋙ H)).inv := by
      ext
      simp
    rw [this]
    exact hid _
  · intro h
    unfold CommutesWith at h
    rw [isLeftKanExtension_iff_existsUnique] at h
    obtain ⟨ρ, -, -⟩ := h ((Functor.const _).obj PEmpty) { app := fun x ↦ x.as.elim }
    exact (ρ.app ⟨PUnit.unit⟩ PUnit.unit).elim

end KanComp

/-! ## Well-copowered categories -/

section WellCopowered

variable {C : Type u} [Category.{v} C]

/-- The objects `⟨a, f⟩` of `c ↓ id_C` whose structure morphism `f : c → a` is an epimorphism. -/
def epiProp (c : C) : ObjectProperty (Under c) := fun X ↦ Epi X.hom

instance (c : C) : (epiProp c).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    have : Epi X.hom := hX
    change Epi Y.hom
    rw [← Under.w e.hom]
    infer_instance

/-- `ALGD-C2-AFT-D04` (prose, §3, p.12).
`Epi_c ⊂ c ↓ id_C` is the full subcategory of the objects `⟨a, f⟩` with `f : c → a` an
epimorphism. Here `c ↓ id_C` is mathlib's `Under c`. -/
abbrev EpiUnder (c : C) : Type _ := (epiProp c).FullSubcategory

/-- `ALGD-C2-AFT-12` (命題 12, p.12).
`Epi_c` is a preorder, not necessarily a set: between two objects there is at most one
morphism. -/
theorem epiUnder_hom_subsingleton {c : C} (X Y : EpiUnder c) : Subsingleton (X ⟶ Y) :=
  ⟨fun f g ↦ by
    have : Epi X.obj.hom := X.property
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    exact (cancel_epi X.obj.hom).1 ((Under.w f.hom).trans (Under.w g.hom).symm)⟩

instance (c : C) : Quiver.IsThin (EpiUnder c) := fun X Y ↦ epiUnder_hom_subsingleton X Y

/-- `ALGD-C2-AFT-D05` (prose, §3, p.12).
`Quot_c` is a skeleton of `Epi_c`. Since `Epi_c` is a preorder (命題 12), `Quot_c` is a partial
order, though not necessarily a set. -/
abbrev Quotients (c : C) : Type _ := Skeleton (EpiUnder c)

/-- The source's well-copowered categories (定義, p.12): `Quot_c` is a set for every `c`. -/
def IsWellCopowered (C : Type u) [Category.{v} C] : Prop :=
  ∀ c : C, Small.{v} (Quotients c)

/-- `MonoOver (op c)` in `C^op` is equivalent to `Epi_c^op`. -/
noncomputable def monoOverOpEquiv (c : C) : MonoOver (op c) ≌ (EpiUnder c)ᵒᵖ :=
  ((Over.opEquivOpUnder c).congrFullSubcategory (Q := (epiProp c).op) (by
      ext X
      change Epi X.hom.unop ↔ Mono X.hom
      exact unop_epi_iff X.hom)).trans (epiProp c).opEquivalence

lemma essentiallySmall_epiUnder_iff (c : C) :
    EssentiallySmall.{v} (EpiUnder c) ↔ EssentiallySmall.{v} (MonoOver (op c)) := by
  rw [essentiallySmall_congr (monoOverOpEquiv c)]
  exact ⟨fun _ ↦ inferInstance,
    fun _ ↦ (essentiallySmall_congr (opOpEquivalence (EpiUnder c))).1 inferInstance⟩

/-- `ALGD-C2-AFT-D06` (定義 (well-copowered), p.12, footnote 2).
`C` is well-copowered iff `Quot_c` is a set for every `c ∈ C`. This is mathlib's
`WellPowered Cᵒᵖ`. (Footnote 2: many texts say cowell-powered; the source follows nLab.) -/
theorem isWellCopowered_iff : IsWellCopowered C ↔ WellPowered.{v} Cᵒᵖ := by
  constructor
  · intro h
    exact wellPowered_of_essentiallySmall_monoOver fun X ↦
      (essentiallySmall_epiUnder_iff X.unop).1 (essentiallySmall_iff_of_thin.2 (h X.unop))
  · intro _ c
    exact essentiallySmall_iff_of_thin.1 ((essentiallySmall_epiUnder_iff c).2 inferInstance)

/-- `ALGD-C2-AFT-13` (例 13, p.12).
A small category is well-copowered. -/
theorem isWellCopowered_of_smallCategory (C : Type v) [SmallCategory C] : IsWellCopowered C :=
  isWellCopowered_iff.2 inferInstance

/-- `ALGD-C2-AFT-14` (例 14, p.12–13).
Set is well-copowered: every epimorphism `f : x → z` is isomorphic in `Epi_x` to the quotient map
`x → x/R` for the equivalence relation `R` with `aRb ⇔ f(a) = f(b)`, so the quotient maps by
equivalence relations on `x` give all of `Quot_x`. -/
theorem isWellCopowered_type : IsWellCopowered (Type v) := fun x ↦ by
  let φ : Setoid x → Quotients x := fun s ↦
    toSkeleton (⟨Under.mk (↾(Quotient.mk s)),
      (epi_iff_surjective _).2 Quotient.mk_surjective⟩ : EpiUnder x)
  refine small_of_surjective (f := φ) fun Y ↦ ?_
  obtain ⟨X, rfl⟩ : ∃ X, toSkeleton X = Y := ⟨_, toSkeleton_fromSkeleton_obj Y⟩
  have hs : Function.Surjective X.obj.hom := (epi_iff_surjective _).1 X.property
  let e : Quotient (Setoid.ker X.obj.hom) ≃ X.obj.right :=
    Setoid.quotientKerEquivOfSurjective _ hs
  refine ⟨Setoid.ker X.obj.hom, congr_toSkeleton_of_iso ?_⟩
  exact (epiProp x).fullyFaithfulι.preimageIso (Under.isoMk e.toIso (by ext a; rfl))

end WellCopowered

/-! ## Quotient objects have coproducts (命題 15) and 補題 17 -/

section Coproducts

variable {U : Type u} [Category.{v} U]

/-- The construction in the proof of 命題 15: in a well-copowered cocomplete category, any family
of epimorphisms `f i : X → K i` (indexed by a type in any universe) has a wide pushout
`⟨P, head, π⟩`, whose leg `head : X → P` is an epimorphism. Only a set of representatives of the
classes of the `⟨K i, f i⟩` in `Quot_X` is used. -/
theorem exists_widePushout_of_epi [HasColimits U] (hU : IsWellCopowered U) {X : U}
    {ι : Type w} (K : ι → U) (f : ∀ i, X ⟶ K i) [hf : ∀ i, Epi (f i)] :
    ∃ (P : U) (head : X ⟶ P) (π : ∀ i, K i ⟶ P), (∀ i, f i ≫ π i = head) ∧ Epi head ∧
      ∀ (W : U) (m : X ⟶ W) (h : ∀ i, K i ⟶ W), (∀ i, f i ≫ h i = m) →
        ∃ u : P ⟶ W, head ≫ u = m ∧ ∀ i, π i ≫ u = h i := by
  let E : ι → EpiUnder X := fun i ↦ ⟨Under.mk (f i), hf i⟩
  let S : Set (Quotients X) := Set.range fun i ↦ toSkeleton (E i)
  have : Small.{v} (Quotients X) := hU X
  let J := Shrink.{v} S
  let rep : J → EpiUnder X := fun k ↦ (fromSkeleton _).obj ((equivShrink S).symm k).1
  let a : ∀ k, X ⟶ (rep k).obj.right := fun k ↦ (rep k).obj.hom
  have ha : ∀ k, Epi (a k) := fun k ↦ (rep k).property
  let idx : ι → J := fun i ↦ equivShrink S ⟨toSkeleton (E i), i, rfl⟩
  have hidx : ∀ i, Nonempty (E i ≅ rep (idx i)) := fun i ↦ by
    refine toSkeleton_eq_iff.1 ?_
    simp [idx]
  have hrep : ∀ k, ∃ i, Nonempty (rep k ≅ E i) := fun k ↦ by
    obtain ⟨i, hi⟩ := ((equivShrink S).symm k).2
    exact ⟨i, ⟨(toSkeleton_eq_iff.1 hi).some.symm⟩⟩
  let π : ∀ i, K i ⟶ widePushout X (fun k ↦ (rep k).obj.right) a :=
    fun i ↦ (hidx i).some.hom.hom.right ≫ WidePushout.ι a (idx i)
  have hπ : ∀ i, f i ≫ π i = WidePushout.head a := fun i ↦ by
    simp only [π, ← Category.assoc]
    rw [show f i ≫ (hidx i).some.hom.hom.right = a (idx i) from Under.w (hidx i).some.hom.hom]
    exact WidePushout.arrow_ι a (idx i)
  have hhead : Epi (WidePushout.head a) := ⟨fun g₁ g₂ hg ↦ by
    refine WidePushout.hom_ext a _ _ (fun k ↦ ?_) hg
    rw [← cancel_epi (a k), ← Category.assoc, ← Category.assoc, WidePushout.arrow_ι, hg]⟩
  refine ⟨_, WidePushout.head a, π, hπ, hhead, fun W m h hh ↦ ?_⟩
  choose j hj using hrep
  let h' : ∀ k, (rep k).obj.right ⟶ W := fun k ↦ (hj k).some.hom.hom.right ≫ h (j k)
  have hh' : ∀ k, a k ≫ h' k = m := fun k ↦ by
    simp only [h', ← Category.assoc]
    rw [show a k ≫ (hj k).some.hom.hom.right = f (j k) from Under.w (hj k).some.hom.hom]
    exact hh (j k)
  refine ⟨WidePushout.desc m h' hh', WidePushout.head_desc a m h' hh', fun i ↦ ?_⟩
  rw [← cancel_epi (f i), ← Category.assoc, hπ, WidePushout.head_desc, hh]

/-- `ALGD-C2-AFT-15` (命題 15, p.13–14).
If `C` is well-copowered and cocomplete, then for `c ∈ C` the category `Quot_c` has all coproducts:
every functor `T : I → Quot_c` from a discrete category `I` has a colimit. -/
theorem hasColimitsOfShape_discrete_quotients [HasColimits U] (hU : IsWellCopowered U) (c : U)
    (I : Type w) : HasColimitsOfShape (Discrete I) (Quotients c) := by
  have : HasColimitsOfShape (Discrete I) (EpiUnder c) := ⟨fun T ↦ by
    have : ∀ i, Epi (T.obj ⟨i⟩).obj.hom := fun i ↦ (T.obj ⟨i⟩).property
    obtain ⟨P, head, π, hπ, hhead, huniv⟩ :=
      exists_widePushout_of_epi hU (fun i ↦ (T.obj ⟨i⟩).obj.right) (fun i ↦ (T.obj ⟨i⟩).obj.hom)
    let s : EpiUnder c := ⟨Under.mk head, hhead⟩
    let leg : ∀ i : Discrete I, T.obj i ⟶ s := fun i ↦
      (epiProp c).fullyFaithfulι.preimage (Under.homMk (π i.as) (hπ i.as))
    refine HasColimit.mk ⟨⟨s, Discrete.natTrans leg⟩, ?_⟩
    exact
      { desc := fun t ↦ (epiProp c).fullyFaithfulι.preimage (Under.homMk
          (huniv t.pt.obj.right t.pt.obj.hom (fun i ↦ (t.ι.app ⟨i⟩).hom.right)
            (fun i ↦ Under.w (t.ι.app ⟨i⟩).hom)).choose
          (huniv t.pt.obj.right t.pt.obj.hom (fun i ↦ (t.ι.app ⟨i⟩).hom.right)
            (fun i ↦ Under.w (t.ι.app ⟨i⟩).hom)).choose_spec.1)
        fac := fun _ _ ↦ Subsingleton.elim _ _
        uniq := fun _ _ _ ↦ Subsingleton.elim _ _ }⟩
  exact Adjunction.hasColimitsOfShape_of_equivalence (fromSkeleton (EpiUnder c))

/-- `ALGD-C2-AFT-17` (補題 17, p.15–17).
Let `U` be well-copowered and cocomplete, `F : C → D`, `S, T : C → U` and `φ : S ⇒ T` an
epimorphism. If the pointwise left Kan extension `F†S` exists, so does the pointwise `F†T`:
`F†T(d)` is the wide pushout over `F†S(d)` of the pushouts of `φ_c` along the colimit legs. -/
theorem hasPointwiseLeftKanExtension_of_epi {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] [HasColimits U] (hU : IsWellCopowered U) (F : C ⥤ D) {S T : C ⥤ U}
    (φ : S ⟶ T) [Epi φ] [F.HasPointwiseLeftKanExtension S] :
    F.HasPointwiseLeftKanExtension T := fun d ↦ by
  let A := CostructuredArrow.proj F d ⋙ S
  let B := CostructuredArrow.proj F d ⋙ T
  have : HasColimit A := inferInstanceAs (F.HasPointwiseLeftKanExtensionAt S d)
  let μ : ∀ j : CostructuredArrow F d, S.obj j.left ⟶ colimit A := fun j ↦ colimit.ι A j
  have hμw : ∀ {j j' : CostructuredArrow F d} (t : j ⟶ j'), S.map t.left ≫ μ j' = μ j :=
    fun t ↦ colimit.w A t
  let K : CostructuredArrow F d → U := fun j ↦ pushout (μ j) (φ.app j.left)
  let g : ∀ j, colimit A ⟶ K j := fun j ↦ pushout.inl _ _
  let r : ∀ j, T.obj j.left ⟶ K j := fun j ↦ pushout.inr _ _
  have hcond : ∀ j, μ j ≫ g j = φ.app j.left ≫ r j := fun j ↦ pushout.condition
  have : ∀ j, Epi (g j) := fun j ↦ inferInstanceAs (Epi (pushout.inl (μ j) (φ.app j.left)))
  obtain ⟨P, head, π, hπ, hhead, huniv⟩ := exists_widePushout_of_epi hU K g
  have hnat : ∀ {j j' : CostructuredArrow F d} (t : j ⟶ j'),
      T.map t.left ≫ r j' ≫ π j' = r j ≫ π j := fun {j j'} t ↦ by
    have hw : μ j ≫ g j' = φ.app j.left ≫ T.map t.left ≫ r j' := by
      rw [← hμw t, Category.assoc, hcond, ← Category.assoc, φ.naturality, Category.assoc]
    let k : K j ⟶ K j' := pushout.desc (g j') (T.map t.left ≫ r j') hw
    have hgk : g j ≫ k = g j' := pushout.inl_desc _ _ _
    have hrk : r j ≫ k = T.map t.left ≫ r j' := pushout.inr_desc _ _ _
    have hk : k ≫ π j' = π j := by
      rw [← cancel_epi (g j), ← Category.assoc, hgk, hπ, hπ]
    calc T.map t.left ≫ r j' ≫ π j' = (r j ≫ k) ≫ π j' := by rw [hrk, Category.assoc]
      _ = r j ≫ π j := by rw [Category.assoc, hk]
  let cB : Cocone B :=
    { pt := P
      ι :=
        { app := fun j ↦ r j ≫ π j
          naturality := fun j j' t ↦ (hnat t).trans (Category.comp_id _).symm } }
  refine HasColimit.mk ⟨cB, ?_⟩
  have key : ∀ s : Cocone B, ∃ u : P ⟶ s.pt, (∀ j, (r j ≫ π j) ≫ u = s.ι.app j) ∧
      ∀ u' : P ⟶ s.pt, (∀ j, (r j ≫ π j) ≫ u' = s.ι.app j) → u' = u := fun s ↦ by
    let m : colimit A ⟶ s.pt :=
      colimit.desc A ((Cocone.precompose (whiskerLeft (CostructuredArrow.proj F d) φ)).obj s)
    have hm : ∀ j, μ j ≫ m = φ.app j.left ≫ s.ι.app j := fun j ↦ colimit.ι_desc _ j
    let h : ∀ j, K j ⟶ s.pt := fun j ↦ pushout.desc m (s.ι.app j) (hm j)
    have hh : ∀ j, g j ≫ h j = m := fun j ↦ pushout.inl_desc _ _ _
    have hr : ∀ j, r j ≫ h j = s.ι.app j := fun j ↦ pushout.inr_desc _ _ _
    obtain ⟨u, hu₁, hu₂⟩ := huniv s.pt m h hh
    refine ⟨u, fun j ↦ by rw [Category.assoc, hu₂, hr], fun u' hu' ↦ ?_⟩
    rw [← cancel_epi head, hu₁]
    refine colimit.hom_ext fun j ↦ ?_
    change μ j ≫ head ≫ u' = μ j ≫ m
    rw [← hπ j, Category.assoc, ← Category.assoc (μ j), hcond, hm, Category.assoc,
      ← Category.assoc (r j), hu' j]
  exact
    { desc := fun s ↦ (key s).choose
      fac := fun s j ↦ (key s).choose_spec.1 j
      uniq := fun s u' hu' ↦ (key s).choose_spec.2 u' hu' }

end Coproducts

/-! ## Generating sets -/

section Generating

variable {C : Type u} [Category.{v} C]

/-- The source's generating sets (定義, p.14): `S ⊂ Ob(C)` is a set, and for `f ≠ g : a → b`
there are `s ∈ S` and `h : s → a` with `f ∘ h ≠ g ∘ h`. -/
def IsGeneratingSet (S : ObjectProperty C) : Prop :=
  ObjectProperty.Small.{v} S ∧
    ∀ ⦃a b : C⦄ (f g : a ⟶ b), f ≠ g → ∃ s, S s ∧ ∃ h : s ⟶ a, h ≫ f ≠ h ≫ g

/-- `ALGD-C2-AFT-D07` (定義 (generating set), p.14, and the ※ on p.14–15).
`S ⊂ Ob(C)` is a generating set iff it is a set and separates morphisms; this is mathlib's
`ObjectProperty.IsSeparating` with `ObjectProperty.Small`. (※: nLab says separator, since a
generating set need not generate anything.) -/
theorem isGeneratingSet_iff (S : ObjectProperty C) :
    IsGeneratingSet S ↔ ObjectProperty.Small.{v} S ∧ S.IsSeparating := by
  refine and_congr_right fun _ ↦ ⟨fun h a b f g hfg ↦ by_contra fun hne ↦ ?_,
    fun h a b f g hne ↦ by_contra fun hn ↦ hne (h f g fun s hs k ↦ by_contra fun hk ↦
      hn ⟨s, hs, k, hk⟩)⟩
  obtain ⟨s, hs, k, hk⟩ := h f g hne
  exact hk (hfg s hs k)

/-- `ALGD-C2-AFT-D08` (定義 (generator), p.14).
`c ∈ C` is a generator iff `{c}` is a generating set; this is mathlib's `IsSeparator c`. -/
theorem isGeneratingSet_singleton_iff (c : C) :
    IsGeneratingSet (ObjectProperty.singleton c) ↔ IsSeparator c := by
  rw [isGeneratingSet_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨inferInstance, h⟩⟩

/-- The source's well-powered categories (定義, p.18): `C^op` is well-copowered. -/
def IsWellPowered (C : Type u) [Category.{v} C] : Prop := IsWellCopowered Cᵒᵖ

/-- `ALGD-C2-AFT-D09` (定義 (well-powered), p.18).
`C` is well-powered iff `C^op` is well-copowered; this is mathlib's `WellPowered C`. -/
theorem isWellPowered_iff : IsWellPowered C ↔ WellPowered.{v} C :=
  isWellCopowered_iff.trans (wellPowered_congr.{v} (opOpEquivalence C))

/-- The source's cogenerating sets (定義, p.19): `S ⊂ Ob(C^op)` is a generating set. -/
def IsCogeneratingSet (S : ObjectProperty C) : Prop := IsGeneratingSet S.op

/-- `ALGD-C2-AFT-D10` (定義 (cogenerating set), p.19).
`S ⊂ Ob(C)` is a cogenerating set iff `S ⊂ Ob(C^op)` is a generating set; this is mathlib's
`ObjectProperty.IsCoseparating` with `ObjectProperty.Small`. -/
theorem isCogeneratingSet_iff (S : ObjectProperty C) :
    IsCogeneratingSet S ↔ ObjectProperty.Small.{v} S ∧ S.IsCoseparating :=
  (isGeneratingSet_iff S.op).trans (and_congr S.small_op_iff S.isSeparating_op_iff)

/-- `ALGD-C2-AFT-D11` (定義 (cogenerator), p.19).
`c ∈ C` is a cogenerator iff `c ∈ C^op` is a generator; this is mathlib's `IsCoseparator c`. -/
theorem isGeneratingSet_singleton_op_iff (c : C) :
    IsGeneratingSet (ObjectProperty.singleton (op c)) ↔ IsCoseparator c :=
  (isGeneratingSet_singleton_iff (op c)).trans (isSeparator_op_iff c)

end Generating

/-! ## The special adjoint functor theorems and representability -/

section SAFT

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-- `ALGD-C2-AFT-18` (定理 18 (特殊随伴関手定理), p.17–18).
Let `C` be well-copowered and cocomplete with a generating set `S`. Then `F : C → D` is
cocontinuous iff it is a left adjoint. -/
theorem preservesColimits_iff_isLeftAdjoint [HasColimits C] (hC : IsWellCopowered C)
    {S : ObjectProperty C} (hS : IsGeneratingSet S) (F : C ⥤ D) :
    PreservesColimits F ↔ F.IsLeftAdjoint := by
  constructor
  · intro _
    have := isWellCopowered_iff.1 hC
    obtain ⟨_, hsep⟩ := (isGeneratingSet_iff S).1 hS
    exact isLeftAdjoint_of_preservesColimits_of_isSeparating hsep F
  · intro _
    exact (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits

/-- `ALGD-C2-AFT-20` (定理 20 (特殊随伴関手定理), p.19).
Let `D` be well-powered and complete with a cogenerating set `S`. Then `G : D → C` is
continuous iff it is a right adjoint. -/
theorem preservesLimits_iff_isRightAdjoint [HasLimits D] (hD : IsWellPowered D)
    {S : ObjectProperty D} (hS : IsCogeneratingSet S) (G : D ⥤ C) :
    PreservesLimits G ↔ G.IsRightAdjoint := by
  constructor
  · intro _
    have := isWellPowered_iff.1 hD
    obtain ⟨_, hcosep⟩ := (isCogeneratingSet_iff S).1 hS
    exact isRightAdjoint_of_preservesLimits_of_isCoseparating hcosep G
  · intro _
    exact (Adjunction.ofIsRightAdjoint G).rightAdjoint_preservesLimits

/-- A right adjoint `G : D → Set` is representable: `Hom_D(F(1), −) ≅ Hom_Set(1, G−) ≅ G`. -/
lemma isCorepresentable_of_isRightAdjoint (G : D ⥤ Type v) [G.IsRightAdjoint] :
    G.IsCorepresentable :=
  (((Adjunction.ofIsRightAdjoint G).corepresentableBy PUnit).ofIso
    (isoWhiskerLeft G Coyoneda.punitIso ≪≫ G.rightUnitor)).isCorepresentable

/-- `ALGD-C2-AFT-22` (定理 22, p.19–20).
Let `D` be complete and `G : D → Set` continuous with the solution set condition. Then `G` is
representable: `G ≅ Hom_D(d, −)` for some `d` (mathlib's `IsCorepresentable`). -/
theorem isCorepresentable_of_solutionSetCondition [HasLimits D] (G : D ⥤ Type v)
    [PreservesLimits G] (hG : SolutionSetCondition.{v} G) : G.IsCorepresentable :=
  have := isRightAdjoint_of_preservesLimits_of_solutionSetCondition G hG
  isCorepresentable_of_isRightAdjoint G

/-- `ALGD-C2-AFT-23` (定理 23, p.20).
Let `D` be well-powered and complete with a cogenerating set. For `G : D → Set` the following
are equivalent: (1) `G` is continuous; (2) `G` is a right adjoint; (3) `G` is representable. -/
theorem preservesLimits_tfae [HasLimits D] (hD : IsWellPowered D) {S : ObjectProperty D}
    (hS : IsCogeneratingSet S) (G : D ⥤ Type v) :
    List.TFAE [PreservesLimits G, G.IsRightAdjoint, G.IsCorepresentable] := by
  tfae_have 1 ↔ 2 := preservesLimits_iff_isRightAdjoint hD hS G
  tfae_have 2 → 3 := fun _ ↦ isCorepresentable_of_isRightAdjoint G
  tfae_have 3 → 1 := fun h ↦ by
    obtain ⟨X, ⟨e⟩⟩ := h.has_corepresentation
    have : PreservesLimits (coyoneda.obj (op X)) := ⟨fun {_} _ ↦ inferInstance⟩
    exact preservesLimits_of_natIso e.toIso
  tfae_finish

/-- `ALGD-C2-AFT-24` (定理 24, p.20).
Let `C` be cocomplete and `K : A → C` a dense functor from a small category, for example the
inclusion of a small dense subcategory `A ⊂ C`. Then `F : C → D` is cocontinuous iff it is a left
adjoint. -/
theorem preservesColimits_iff_isLeftAdjoint_of_isDense [HasColimits C] {A : Type v}
    [SmallCategory A] (K : A ⥤ C) [K.IsDense] (F : C ⥤ D) :
    PreservesColimits F ↔ F.IsLeftAdjoint := by
  constructor
  · intro _
    refine isLeftAdjoint_of_leftSolutionSetCondition F fun d ↦ ?_
    let P := CostructuredArrow.proj (K ⋙ F) d ⋙ K
    let cd : Cocone (P ⋙ F) :=
      { pt := d
        ι :=
          { app := fun j ↦ j.hom
            naturality := fun j j' t ↦ by simpa [P] using CostructuredArrow.w t } }
    let hF := isColimitOfPreserves F (colimit.isColimit P)
    let k : F.obj (colimit P) ⟶ d := hF.desc cd
    have hk : ∀ j, F.map (colimit.ι P j) ≫ k = j.hom := fun j ↦ hF.fac cd j
    refine ⟨PUnit, fun _ ↦ colimit P, fun _ ↦ k, fun c f ↦ ⟨PUnit.unit, ?_⟩⟩
    let jc : CostructuredArrow K c → CostructuredArrow (K ⋙ F) d :=
      fun u ↦ CostructuredArrow.mk (Y := u.left) (F.map u.hom ≫ f)
    let cc : Cocone (CostructuredArrow.proj K c ⋙ K) :=
      { pt := colimit P
        ι :=
          { app := fun u ↦ colimit.ι P (jc u)
            naturality := fun u u' t ↦ by
              have := colimit.w P (CostructuredArrow.homMk t.left (by
                simp only [jc, CostructuredArrow.mk_hom_eq_self, Functor.comp_map]
                rw [← F.map_comp_assoc, CostructuredArrow.w t]) : jc u ⟶ jc u')
              simpa [P] using this } }
    refine ⟨(K.denseAt c).desc cc, ?_⟩
    refine (isColimitOfPreserves F (K.denseAt c)).hom_ext fun u ↦ ?_
    have hu := (K.denseAt c).fac cc u
    simp only [Functor.mapCocone_ι_app, ← F.map_comp_assoc, hu]
    simpa [cc, jc, LeftExtension.coconeAt] using hk (jc u)
  · intro _
    exact (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits

end SAFT

/-! ## Axiom audit

Each verified declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. The
output is pinned with `#guard_msgs`, so `lake build` fails if it changes. -/

/-- info: 'ProjectEpisteme.AlgD.AFT.IsFinalColim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.IsFinalColim

/-- info: 'ProjectEpisteme.AlgD.AFT.isFinalColim_of_isRightAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isFinalColim_of_isRightAdjoint

/-- info: 'ProjectEpisteme.AlgD.AFT.isFinalColim_of_isEquivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isFinalColim_of_isEquivalence

/-- info: 'ProjectEpisteme.AlgD.AFT.isConnected_iff_zigzag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isConnected_iff_zigzag

/-- info: 'ProjectEpisteme.AlgD.AFT.isFinalColim_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isFinalColim_tfae

/-- info: 'ProjectEpisteme.AlgD.AFT.nonempty_isTerminal_iff_isFinalColim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.nonempty_isTerminal_iff_isFinalColim

/-- info: 'ProjectEpisteme.AlgD.AFT.isLeftAdjoint_of_leftSolutionSetCondition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isLeftAdjoint_of_leftSolutionSetCondition

/-- info: 'ProjectEpisteme.AlgD.AFT.isLeftKanExtension_comp_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isLeftKanExtension_comp_iff

/-- info: 'ProjectEpisteme.AlgD.AFT.EpiUnder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.EpiUnder

/-- info: 'ProjectEpisteme.AlgD.AFT.epiUnder_hom_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.epiUnder_hom_subsingleton

/-- info: 'ProjectEpisteme.AlgD.AFT.Quotients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.Quotients

/-- info: 'ProjectEpisteme.AlgD.AFT.isWellCopowered_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isWellCopowered_iff

/-- info: 'ProjectEpisteme.AlgD.AFT.isWellCopowered_of_smallCategory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isWellCopowered_of_smallCategory

/-- info: 'ProjectEpisteme.AlgD.AFT.isWellCopowered_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isWellCopowered_type

/-- info: 'ProjectEpisteme.AlgD.AFT.isGeneratingSet_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isGeneratingSet_iff

/-- info: 'ProjectEpisteme.AlgD.AFT.isGeneratingSet_singleton_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isGeneratingSet_singleton_iff

/-- info: 'ProjectEpisteme.AlgD.AFT.isWellPowered_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isWellPowered_iff

/-- info: 'ProjectEpisteme.AlgD.AFT.isCogeneratingSet_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isCogeneratingSet_iff

/-- info: 'ProjectEpisteme.AlgD.AFT.isGeneratingSet_singleton_op_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isGeneratingSet_singleton_op_iff

/-- info: 'ProjectEpisteme.AlgD.AFT.preservesColimits_iff_isLeftAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.preservesColimits_iff_isLeftAdjoint

/-- info: 'ProjectEpisteme.AlgD.AFT.preservesLimits_iff_isRightAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.preservesLimits_iff_isRightAdjoint

/-- info: 'ProjectEpisteme.AlgD.AFT.isCorepresentable_of_solutionSetCondition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isCorepresentable_of_solutionSetCondition

/-- info: 'ProjectEpisteme.AlgD.AFT.preservesLimits_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.preservesLimits_tfae

/-- info: 'ProjectEpisteme.AlgD.AFT.isFinalColim_iff_isColimit_whisker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isFinalColim_iff_isColimit_whisker

/-- info: 'ProjectEpisteme.AlgD.AFT.commutesWith_comp_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.commutesWith_comp_iff

/-- info: 'ProjectEpisteme.AlgD.AFT.isPointwiseLeftKanExtensionAt_comp_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.isPointwiseLeftKanExtensionAt_comp_iff

/-- info: 'ProjectEpisteme.AlgD.AFT.commutesWith_comp_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.commutesWith_comp_counterexample

/-- info: 'ProjectEpisteme.AlgD.AFT.hasColimitsOfShape_discrete_quotients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.hasColimitsOfShape_discrete_quotients

/-- info: 'ProjectEpisteme.AlgD.AFT.hasPointwiseLeftKanExtension_of_epi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.hasPointwiseLeftKanExtension_of_epi

/-- info: 'ProjectEpisteme.AlgD.AFT.preservesColimits_iff_isLeftAdjoint_of_isDense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.preservesColimits_iff_isLeftAdjoint_of_isDense

end ProjectEpisteme.AlgD.AFT

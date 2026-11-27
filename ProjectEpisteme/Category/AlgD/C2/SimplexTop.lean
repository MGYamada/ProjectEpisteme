/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Category.TopCat.Sphere

/-!
# alg-d, Chapter 2: 例：単体的集合 (Example: simplicial sets), geometric realization

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 2, `simplex.pdf`
(<https://alg-d.com/math/kan_extension/simplex.pdf>), printed date 2026-10-18,
SHA-256 `728b18894d57b7471bec403811b6cfa6f93cc79de302e08e2d67b2210989a894`,
retrieved 2026-11-26. Ledger: `docs/ledger/algd/C2-SIMPLEX.md`.

This module holds the rows about the topological simplices `F[n]`, the geometric realization
and the singular functor (§1 and §3 of the source), so that
`ProjectEpisteme.Category.AlgD.C2.Simplex` does not import topology. The conventions are those of
that module; `Top` is `TopCat.{u}`.

* `F[n]` is `Convexity.StdSimplex ℝ (Fin (n + 1))`, and `|Δ^n| ≅ F[n]` is mathlib's
  `SimplexCategory.toTopHomeo`.
* For `A ⊆ Δ^n`, `realMap A : |A| → F[n]` is the realization of the inclusion followed by
  `|Δ^n| ≅ F[n]`; it is the source's `k_I` (`A = Δ^n_{I↓}`) and `h_U` (`A = Δ^n_U`).
* `Δ^n_U` (`simplexSub U`) is the union of the faces `I ∈ U`, and `M_U` (`simplexM U`) is the
  set of points whose support lies in `U`.
-/

@[expose] public section

namespace ProjectEpisteme.AlgD.Simplex

open CategoryTheory Limits Opposite Simplicial SSet SimplexCategory Topology

universe u

/-- `ALGD-C2-SIMPLEX-D03` (prose, p.2–3).
`F[n] = {⟨x₀, …, xₙ⟩ ∈ [0, 1]^{n+1} | x₀ + ⋯ + xₙ = 1}` with the subspace topology of
`ℝ^{n+1}` (mathlib's `StdSimplex ℝ (Fin (n + 1))`, through its weights), and for
`β : [m] → [n]`, `Fβ(x)_j = Σ_{i ∈ β⁻¹(j)} x_i`. This gives `F : Δ → Top`; the geometric
realization `|−| := y†F` is mathlib's `SSet.toTop`, the left Kan extension of `F` along `y`;
`Sing := F†y` has `Sing(S)_n ≅ Hom_Top(F[n], S)`; and `|−| ⊣ Sing`. -/
theorem realization_singular :
    (∀ n : ℕ, (toTop₀.obj ⦋n⦌ : Type) = Convexity.StdSimplex ℝ (Fin (n + 1))) ∧
    (∀ n : ℕ, IsEmbedding (fun t ↦ ⇑t.weights : Convexity.StdSimplex ℝ (Fin (n + 1)) →
      Fin (n + 1) → ℝ) ∧
      Set.range (fun t ↦ ⇑t.weights : Convexity.StdSimplex ℝ (Fin (n + 1)) → Fin (n + 1) → ℝ) =
        {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}) ∧
    (∀ {m n : ℕ} (β : ⦋m⦌ ⟶ ⦋n⦌) (x : Convexity.StdSimplex ℝ (Fin (m + 1))) (j : Fin (n + 1)),
      (toTop₀.map β x : Convexity.StdSimplex ℝ (Fin (n + 1))).weights j =
        ∑ i ∈ Finset.univ.filter (fun i ↦ β.toOrderHom i = j), x.weights i) ∧
    SSet.toTop.{u} = stdSimplex.{u}.leftKanExtension SimplexCategory.toTop.{u} ∧
    (∀ (S : TopCat.{u}) (n : ℕ),
      Nonempty ((TopCat.toSSet.obj S) _⦋n⦌ ≃ C(Convexity.StdSimplex ℝ (Fin (n + 1)), S))) ∧
    Nonempty (SSet.toTop.{u} ⊣ TopCat.toSSet) := by
  refine ⟨fun _ ↦ rfl, fun n ↦ ⟨Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _, ?_⟩,
    fun β x j ↦ ?_, rfl, fun S n ↦ ⟨TopCat.toSSetObjEquiv S (op ⦋n⦌)⟩, ⟨sSetTopAdj⟩⟩
  · rw [Convexity.StdSimplex.range_toFun_comp_weights]
    ext x
    simp
  · change (Convexity.StdSimplex.map β.toOrderHom x).weights j = _
    rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_fintype, Finsupp.finsetSum_apply,
      Finset.sum_filter]
    simp [Finsupp.single_apply]

/-- `ALGD-C2-SIMPLEX-R02` (prose, p.3).
Since `y` is fully faithful, `|Δ^n| ≅ F[n]`; and `|−|` preserves colimits (it is a left adjoint),
so `|colim Δ^{n_j}| ≅ colim F[n_j]`. -/
theorem realization_stdSimplex (n : ℕ) :
    Nonempty (SSet.toTop.{u}.obj Δ[n] ≅ SimplexCategory.toTop.obj ⦋n⦌) ∧
    PreservesColimitsOfSize.{u, u} SSet.toTop.{u} :=
  ⟨⟨SSet.toTopSimplex.app ⦋n⦌⟩, sSetTopAdj.leftAdjoint_preservesColimits⟩

/-! ### The realization of `∂Δ^n` (§3) -/

section Realization

variable {n : ℕ}

/-- `ALGD-C2-SIMPLEX-07` (condition (7), p.8).
`U ⊆ P_0([n])` is closed under nonempty subsets: `I ∈ U` and `∅ ≠ J ⊆ I` imply `J ∈ U`. -/
def IsDownClosed (U : Set (Finset (Fin (n + 1)))) : Prop :=
  (∀ I ∈ U, I.Nonempty) ∧ ∀ ⦃I⦄, I ∈ U → ∀ ⦃J : Finset (Fin (n + 1))⦄, J.Nonempty → J ⊆ I → J ∈ U

/-- The source's `Δ^n_U`, as the union of the faces `I ∈ U`. -/
def simplexSub (U : Set (Finset (Fin (n + 1)))) : (Δ[n] : SSet.{u}).Subcomplex :=
  ⨆ I ∈ U, stdSimplex.face I

/-- The source's `M_U`: the points of `F[n]` whose support lies in `U`. -/
def simplexM (U : Set (Finset (Fin (n + 1)))) : Set (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  {x | x.weights.support ∈ U}

/-- The source's `I↓`. -/
def down (J : Finset (Fin (n + 1))) : Set (Finset (Fin (n + 1))) := {I | I.Nonempty ∧ I ⊆ J}

lemma isDownClosed_down (J : Finset (Fin (n + 1))) : IsDownClosed (down J) :=
  ⟨fun _ h ↦ h.1, fun _ hI _ hJ hJI ↦ ⟨hJ, hJI.trans hI.2⟩⟩

lemma mem_simplexSub_iff {U : Set (Finset (Fin (n + 1)))} (hU : IsDownClosed U) {d : ℕ}
    (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∈ (simplexSub U).obj (op ⦋d⦌) ↔ Finset.univ.image (fun i ↦ x i) ∈ U := by
  simp only [simplexSub, Subfunctor.iSup_obj, Set.mem_iUnion, stdSimplex.mem_face_iff,
    exists_prop]
  refine ⟨fun ⟨I, hI, hx⟩ ↦ hU.2 hI ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ 0)⟩
    (fun j hj ↦ ?_), fun h ↦ ⟨_, h, fun i ↦ Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩⟩
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hj
  exact hx i

lemma simplexSub_down (J : Finset (Fin (n + 1))) :
    simplexSub.{u} (down J) = stdSimplex.face J := by
  apply le_antisymm
  · exact iSup₂_le fun I hI ↦ (stdSimplex.face_le_face_iff _ _).2 hI.2
  · rcases J.eq_empty_or_nonempty with rfl | hJ
    · simp
    · exact le_iSup₂_of_le J ⟨hJ, subset_rfl⟩ le_rfl

/-- `ALGD-C2-SIMPLEX-D09` (prose, p.8).
For `U` satisfying (7), `(Δ^n_U)_k = {β : [k] → [n] ∣ Im β ∈ U}` and
`M_U = {x ∈ F[n] ∣ {i ∣ x_i ≠ 0} ∈ U}`; for `U ⊆ V` there are inclusions `Δ^n_U ⊆ Δ^n_V` and
`M_U ⊆ M_V`; and `Δ^n_{I↓}` is the face `I`. -/
theorem simplexSub_spec {U V : Set (Finset (Fin (n + 1)))} (hU : IsDownClosed U) :
    (∀ {d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d⦌),
      x ∈ (simplexSub U).obj (op ⦋d⦌) ↔ Finset.univ.image (fun i ↦ x i) ∈ U) ∧
    (∀ x, x ∈ simplexM U ↔ x.weights.support ∈ U) ∧
    (U ⊆ V → simplexSub.{u} U ≤ simplexSub V ∧ simplexM U ⊆ simplexM V) ∧
    (∀ J : Finset (Fin (n + 1)), simplexSub.{u} (down J) = stdSimplex.face J) :=
  ⟨mem_simplexSub_iff hU, fun _ ↦ Iff.rfl,
    fun h ↦ ⟨iSup₂_le fun I hI ↦ le_iSup₂_of_le I (h hI) le_rfl, fun _ hx ↦ h hx⟩,
    simplexSub_down⟩


instance t2Space_stdSimplex (k : ℕ) : T2Space (Convexity.StdSimplex ℝ (Fin (k + 1))) :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).t2Space

/-- The map `|A| → |Δ^n| ≅ F[n]` for a subset `A ⊆ Δ^n` (the source's `k_I` and `h_U`). -/
noncomputable def realMap (A : (Δ[n] : SSet.{u}).Subcomplex) :
    SSet.toTop.obj (A : SSet.{u}) → Convexity.StdSimplex ℝ (Fin (n + 1)) :=
  fun p ↦ SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map A.ι p)

lemma continuous_realMap (A : (Δ[n] : SSet.{u}).Subcomplex) : Continuous (realMap A) :=
  (SimplexCategory.toTopHomeo ⦋n⦌).continuous.comp (SSet.toTop.map A.ι).hom.continuous

/-- `ALGD-C2-SIMPLEX-09` (補題 9, p.9).
For `A ⊆ B ⊆ Δ^n` (in particular `Δ^n_{J↓} ⊆ Δ^n_{I↓}` for `J ⊆ I`), the maps to `F[n]` commute
with the inclusions: `h_B ∘ |inc| = h_A`. -/
theorem realMap_homOfLE {A B : (Δ[n] : SSet.{u}).Subcomplex} (h : A ≤ B)
    (p : SSet.toTop.obj (A : SSet.{u})) :
    realMap B (SSet.toTop.map (Subcomplex.homOfLE h) p) = realMap A p := by
  simp only [realMap]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subcomplex.homOfLE_ι]

lemma range_stdSimplex_map {m : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (hf : Function.Injective f) :
    Set.range (Convexity.StdSimplex.map (R := ℝ) f) =
      {x | (x.weights.support : Set (Fin (n + 1))) ⊆ Set.range f} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ i hi
    rw [Convexity.StdSimplex.weights_map] at hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hi)
    exact ⟨j, rfl⟩
  · intro hx
    have hmap : Finsupp.mapDomain f (Finsupp.comapDomain f x.weights hf.injOn) = x.weights :=
      Finsupp.mapDomain_comapDomain f hf x.weights hx
    refine ⟨⟨Finsupp.comapDomain f x.weights hf.injOn, fun i ↦ ?_, ?_⟩, ?_⟩
    · simp
    · have h := Finsupp.sum_mapDomain_index_inj (h := fun (_ : Fin (n + 1)) (r : ℝ) ↦ r) hf
        (s := Finsupp.comapDomain f x.weights hf.injOn)
      rw [hmap] at h
      exact h.symm.trans x.total
    · ext1
      rw [Convexity.StdSimplex.weights_map]
      exact hmap

/-- `ALGD-C2-SIMPLEX-08` (補題 8, p.8).
For nonempty `I ⊆ [n]`, `h : |Δ^n_{I↓}| → F[n]` is a closed embedding with image `M_{I↓}`, so
`|Δ^n_{I↓}| ≅ M_{I↓}`. -/
theorem realMap_face {J : Finset (Fin (n + 1))} (hJ : J.Nonempty) :
    IsClosedEmbedding (realMap (simplexSub.{u} (down J))) ∧
    Set.range (realMap (simplexSub.{u} (down J))) = simplexM (down J) := by
  rw [simplexSub_down]
  obtain ⟨m, hm⟩ : ∃ m, J.card = m + 1 := ⟨J.card - 1, by have := hJ.card_pos; omega⟩
  let e := J.orderIsoOfFin hm
  let f : Fin (m + 1) →o Fin (n + 1) :=
    (OrderHom.Subtype.val (· ∈ J)).comp e.toOrderEmbedding.toOrderHom
  have hf : Function.Injective f := fun a b h ↦ e.injective (Subtype.ext h)
  have hrange : Set.range f = J := by
    ext x
    refine ⟨fun ⟨a, ha⟩ ↦ ha ▸ (e a).2, fun hx ↦ ⟨e.symm ⟨x, hx⟩, ?_⟩⟩
    change ((e (e.symm ⟨x, hx⟩)) : Fin (n + 1)) = x
    rw [OrderIso.apply_symm_apply]
  let iso := stdSimplex.isoOfRepresentableBy.{u} (stdSimplex.faceRepresentableBy J m e)
  have hcomp : iso.hom ≫ (stdSimplex.face J).ι = SSet.stdSimplex.map (mkHom f) := by
    apply SSet.yonedaEquiv.injective
    rfl
  let φ : Convexity.StdSimplex ℝ (Fin (m + 1)) → Convexity.StdSimplex ℝ (Fin (n + 1)) :=
    Convexity.StdSimplex.map f
  have key : ∀ q, realMap (stdSimplex.face J) (SSet.toTop.map iso.hom q) =
      φ (SimplexCategory.toTopHomeo ⦋m⦌ q) := fun q ↦ by
    have nat := ConcreteCategory.congr_hom (SSet.toTopSimplex.hom.naturality (mkHom f)) q
    change (SimplexCategory.toTopHomeo ⦋n⦌) (SSet.toTop.map (stdSimplex.face J).ι
      (SSet.toTop.map iso.hom q)) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hcomp]
    exact congr_arg ULift.down nat
  have hreal : realMap (stdSimplex.face J) =
      (φ ∘ SimplexCategory.toTopHomeo ⦋m⦌) ∘ (SSet.toTop.map iso.inv) := by
    funext p
    simp only [Function.comp_apply, ← key, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  have hφ : IsClosedEmbedding φ :=
    (Convexity.StdSimplex.continuous_map ℝ f).isClosedEmbedding
      (fun a b h ↦ by
        rw [← Convexity.StdSimplex.weights_inj] at h ⊢
        simpa [Convexity.StdSimplex.weights_map] using Finsupp.mapDomain_injective hf h)
  refine ⟨?_, ?_⟩
  · rw [hreal]
    exact (hφ.comp (SimplexCategory.toTopHomeo ⦋m⦌).isClosedEmbedding).comp
      (TopCat.homeoOfIso (SSet.toTop.mapIso iso.symm)).isClosedEmbedding
  · have hs : Function.Surjective (SSet.toTop.map iso.inv) := fun q ↦
      ⟨SSet.toTop.map iso.hom q, by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.hom_inv_id,
          CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]⟩
    rw [hreal, Set.range_comp, hs.range_eq, Set.image_univ, Set.range_comp, (SimplexCategory.toTopHomeo ⦋m⦌).surjective.range_eq,
      Set.image_univ, range_stdSimplex_map f hf, hrange]
    ext x
    exact ⟨fun h ↦ ⟨x.support_weights_nonempty, fun i hi ↦ h hi⟩, fun h i hi ↦ h.2 hi⟩


lemma isEmpty_toTop_bot :
    IsEmpty (SSet.toTop.obj ((⊥ : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u})) := by
  have : PreservesColimitsOfSize.{u, u} SSet.toTop.{u} := sSetTopAdj.leftAdjoint_preservesColimits
  have h : IsInitial (SSet.toTop.obj ((⊥ : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u})) :=
    IsInitial.isInitialObj SSet.toTop _ Subcomplex.isInitialBot
  exact ⟨fun p ↦ ((h.to (TopCat.of (ULift.{u} PEmpty))) p).down.elim⟩

/-- Gluing: if `A_4 = A_2 ∪ A_3` and `A_1 = A_2 ∩ A_3`, and `h_{A_2}`, `h_{A_3}` are closed
embeddings whose images meet inside the image of `h_{A_1}`, then `h_{A_4}` is a closed embedding
with image the union of the two images. -/
lemma realMap_isClosedEmbedding_of_bicartSq {A₁ A₂ A₃ A₄ : (Δ[n] : SSet.{u}).Subcomplex}
    (sq : Subcomplex.BicartSq A₁ A₂ A₃ A₄) (h₂ : IsClosedEmbedding (realMap A₂))
    (h₃ : IsClosedEmbedding (realMap A₃))
    (h₁ : Set.range (realMap A₂) ∩ Set.range (realMap A₃) ⊆ Set.range (realMap A₁)) :
    IsClosedEmbedding (realMap A₄) ∧
      Set.range (realMap A₄) = Set.range (realMap A₂) ∪ Set.range (realMap A₃) := by
  have : PreservesColimitsOfSize.{u, u} SSet.toTop.{u} := sSetTopAdj.leftAdjoint_preservesColimits
  have sqT := sq.isPushout.map SSet.toTop
  have sqF := sqT.map (forget TopCat)
  have joint : ∀ p, (∃ a, SSet.toTop.map (Subcomplex.homOfLE sq.le₂₄) a = p) ∨
      ∃ b, SSet.toTop.map (Subcomplex.homOfLE sq.le₃₄) b = p :=
    fun p ↦ Types.eq_or_eq_of_isPushout sqF p
  have w : ∀ c, SSet.toTop.map (Subcomplex.homOfLE sq.le₂₄)
      (SSet.toTop.map (Subcomplex.homOfLE sq.le₁₂) c) =
      SSet.toTop.map (Subcomplex.homOfLE sq.le₃₄) (SSet.toTop.map (Subcomplex.homOfLE sq.le₁₃) c) :=
    fun c ↦ ConcreteCategory.congr_hom sqT.w c
  have hrange : Set.range (realMap A₄) = Set.range (realMap A₂) ∪ Set.range (realMap A₃) := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      rcases joint p with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact Or.inl ⟨a, (realMap_homOfLE _ a).symm⟩
      · exact Or.inr ⟨b, (realMap_homOfLE _ b).symm⟩
    · rintro (⟨a, rfl⟩ | ⟨b, rfl⟩)
      · exact ⟨_, realMap_homOfLE sq.le₂₄ a⟩
      · exact ⟨_, realMap_homOfLE sq.le₃₄ b⟩
  have hinj : Function.Injective (realMap A₄) := by
    have cross : ∀ a b, realMap A₂ a = realMap A₃ b →
        SSet.toTop.map (Subcomplex.homOfLE sq.le₂₄) a =
          SSet.toTop.map (Subcomplex.homOfLE sq.le₃₄) b := fun a b hab ↦ by
      obtain ⟨c, hc⟩ := h₁ ⟨⟨a, rfl⟩, ⟨b, hab.symm⟩⟩
      have ha : SSet.toTop.map (Subcomplex.homOfLE sq.le₁₂) c = a :=
        h₂.injective ((realMap_homOfLE _ c).trans hc)
      have hb : SSet.toTop.map (Subcomplex.homOfLE sq.le₁₃) c = b :=
        h₃.injective ((realMap_homOfLE _ c).trans (hc.trans hab))
      rw [← ha, ← hb, w]
    intro p q hpq
    rcases joint p with ⟨a, rfl⟩ | ⟨b, rfl⟩ <;> rcases joint q with ⟨a', rfl⟩ | ⟨b', rfl⟩
    · rw [realMap_homOfLE, realMap_homOfLE] at hpq; rw [h₂.injective hpq]
    · rw [realMap_homOfLE, realMap_homOfLE] at hpq; exact cross a b' hpq
    · rw [realMap_homOfLE, realMap_homOfLE] at hpq; exact (cross a' b hpq.symm).symm
    · rw [realMap_homOfLE, realMap_homOfLE] at hpq; rw [h₃.injective hpq]
  have hclosed : IsClosedMap (realMap A₄) := by
    intro C hC
    have : realMap A₄ '' C =
        realMap A₂ '' (SSet.toTop.map (Subcomplex.homOfLE sq.le₂₄) ⁻¹' C) ∪
          realMap A₃ '' (SSet.toTop.map (Subcomplex.homOfLE sq.le₃₄) ⁻¹' C) := by
      ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        rcases joint p with ⟨a, rfl⟩ | ⟨b, rfl⟩
        · exact Or.inl ⟨a, hp, (realMap_homOfLE _ a).symm⟩
        · exact Or.inr ⟨b, hp, (realMap_homOfLE _ b).symm⟩
      · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
        · exact ⟨_, ha, realMap_homOfLE _ a⟩
        · exact ⟨_, hb, realMap_homOfLE _ b⟩
    rw [this]
    exact (h₂.isClosedMap _ (hC.preimage (SSet.toTop.map _).hom.continuous)).union
      (h₃.isClosedMap _ (hC.preimage (SSet.toTop.map _).hom.continuous))
  exact ⟨.of_continuous_injective_isClosedMap (continuous_realMap A₄) hinj hclosed, hrange⟩

lemma simplexSub_union (U V : Set (Finset (Fin (n + 1)))) :
    simplexSub.{u} (U ∪ V) = simplexSub U ⊔ simplexSub V := by
  simp only [simplexSub, iSup_union]

/-- `ALGD-C2-SIMPLEX-10` (補題 10, p.9–13).
For `U` satisfying (7), `h_U : |Δ^n_U| → F[n]` is a closed embedding with image `M_U`, so
`|Δ^n_U| ≅ M_U`, compatibly with the inclusions (補題 9). -/
theorem realMap_simplexSub {U : Set (Finset (Fin (n + 1)))} (hU : IsDownClosed U) :
    IsClosedEmbedding (realMap (simplexSub.{u} U)) ∧
      Set.range (realMap (simplexSub.{u} U)) = simplexM U := by
  induction h : U.ncard using Nat.strong_induction_on generalizing U with
  | _ N ih =>
  rcases U.eq_empty_or_nonempty with rfl | hne
  · have hbot : simplexSub.{u} (∅ : Set (Finset (Fin (n + 1)))) = ⊥ := by simp [simplexSub]
    rw [hbot]
    have := isEmpty_toTop_bot.{u} (n := n)
    refine ⟨(continuous_realMap _).isClosedEmbedding fun a ↦ isEmptyElim a, ?_⟩
    rw [Set.range_eq_empty]
    exact Set.ext fun x ↦ ⟨fun h ↦ h.elim, fun h ↦ h⟩
  obtain ⟨J, hJU, hJmax⟩ := Set.exists_max_image U Finset.card U.toFinite hne
  have hJ : J.Nonempty := hU.1 J hJU
  have hdown : down J ⊆ U := fun I hI ↦ hU.2 hJU hI.1 hI.2
  have heqJ : ∀ I ∈ U, J ⊆ I → I = J := fun I hI hJI ↦
    (Finset.eq_of_subset_of_card_le hJI (hJmax I hI)).symm
  by_cases hUJ : U = down J
  · subst hUJ
    exact realMap_face hJ
  let U' := U \ {J}
  let W : Set (Finset (Fin (n + 1))) := {I | I.Nonempty ∧ I ⊆ J ∧ I ≠ J}
  have hU' : IsDownClosed U' := ⟨fun I hI ↦ hU.1 I hI.1, fun I hI K hK hKI ↦
    ⟨hU.2 hI.1 hK hKI, fun hKJ ↦ hI.2 (heqJ I hI.1 (Set.mem_singleton_iff.1 hKJ ▸ hKI))⟩⟩
  have hW : IsDownClosed W := ⟨fun I hI ↦ hI.1, fun I hI K hK hKI ↦
    ⟨hK, hKI.trans hI.2.1, fun hKJ ↦ hI.2.2
      (Finset.Subset.antisymm hI.2.1 (hKJ ▸ hKI))⟩⟩
  have hlt' : U'.ncard < N := h ▸ Set.ncard_sdiff_singleton_lt_of_mem hJU U.toFinite
  have hWU' : W ⊆ U' := fun I hI ↦ ⟨hdown ⟨hI.1, hI.2.1⟩, hI.2.2⟩
  have hltW : W.ncard < N := lt_of_le_of_lt (Set.ncard_le_ncard hWU' (U.toFinite.sdiff)) hlt'
  have hsup : U' ∪ down J = U := by
    ext I
    refine ⟨fun h ↦ h.elim (fun h ↦ h.1) (fun h ↦ hdown h), fun hI ↦ ?_⟩
    by_cases hIJ : I = J
    · subst hIJ
      exact Or.inr ⟨hJ, subset_rfl⟩
    · exact Or.inl ⟨hI, hIJ⟩
  have sq : Subcomplex.BicartSq (simplexSub.{u} W) (simplexSub U') (simplexSub (down J))
      (simplexSub U) := by
    refine ⟨by rw [← simplexSub_union, hsup], ?_⟩
    ext ⟨m⟩ x
    induction m using SimplexCategory.rec with | _ m => ?_
    simp only [Subfunctor.min_obj, Set.mem_inter_iff, mem_simplexSub_iff hU', mem_simplexSub_iff hW,
      mem_simplexSub_iff (isDownClosed_down J)]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨h₃.1, h₃.2, h₂⟩
    · rintro ⟨h₁, h₂, h₃⟩
      exact ⟨⟨hdown ⟨h₁, h₂⟩, h₃⟩, h₁, h₂⟩
  obtain ⟨hc', hr'⟩ := ih _ hlt' hU' rfl
  obtain ⟨-, hrW⟩ := ih _ hltW hW rfl
  obtain ⟨hcJ, hrJ⟩ := realMap_face.{u} hJ
  obtain ⟨hc, hr⟩ := realMap_isClosedEmbedding_of_bicartSq sq hc' hcJ (by
    rw [hr', hrJ, hrW]
    rintro x ⟨hx₁, hx₂⟩
    exact ⟨hx₂.1, hx₂.2, hx₁.2⟩)
  refine ⟨hc, ?_⟩
  rw [hr, hr', hrJ]
  ext x
  change x.weights.support ∈ U' ∨ x.weights.support ∈ down J ↔ x.weights.support ∈ U
  rw [← hsup]
  rfl

/-- `|Δ^n_U| ≅ M_U` as spaces. -/
noncomputable def simplexSubHomeo {U : Set (Finset (Fin (n + 1)))} (hU : IsDownClosed U) :
    SSet.toTop.obj (simplexSub.{u} U : SSet.{u}) ≃ₜ simplexM U :=
  (realMap_simplexSub hU).1.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (realMap_simplexSub hU).2)

end Realization

/-! ### The boundary of the topological simplex is a sphere -/

section Sphere

variable (n : ℕ)

/-- `F[n + 1] → ℝ^{n+1}`, forgetting the coordinate `x_0`. -/
noncomputable def dropZero (x : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 fun i ↦ x.weights i.succ

lemma dropZero_apply (x : Convexity.StdSimplex ℝ (Fin (n + 2))) (i : Fin (n + 1)) :
    dropZero n x i = x.weights i.succ := rfl

lemma continuous_dropZero : Continuous (dropZero n) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ (continuous_apply i.succ).comp
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous)

lemma weights_zero_eq (x : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    x.weights 0 = 1 - ∑ i, dropZero n x i := by
  have := x.total_of_fintype
  rw [Fin.sum_univ_succ] at this
  simp only [dropZero_apply]
  linarith

/-- The corner simplex `K = {y ∈ ℝ^{n+1} ∣ y_i ≥ 0, Σ y_i ≤ 1}`. -/
def corner : Set (EuclideanSpace ℝ (Fin (n + 1))) := {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}

/-- The interior of the corner simplex. -/
def cornerInt : Set (EuclideanSpace ℝ (Fin (n + 1))) := {y | (∀ i, 0 < y i) ∧ ∑ i, y i < 1}

lemma isClosedEmbedding_dropZero : IsClosedEmbedding (dropZero n) := by
  refine (continuous_dropZero n).isClosedEmbedding fun x y h ↦ ?_
  have hi : ∀ i : Fin (n + 1), x.weights i.succ = y.weights i.succ := fun i ↦
    congr_arg (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z i) h
  rw [← Convexity.StdSimplex.weights_inj]
  ext j
  refine Fin.cases ?_ (fun i ↦ hi i) j
  rw [weights_zero_eq, weights_zero_eq, h]

lemma range_dropZero : Set.range (dropZero n) = corner n := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨fun i ↦ x.weights_nonneg _, ?_⟩
    have := x.weights_nonneg 0
    rw [weights_zero_eq] at this
    linarith
  · rintro ⟨h₁, h₂⟩
    have hmem : Fin.cons (1 - ∑ i, y i) (fun i ↦ y i) ∈
        Set.range (fun t ↦ ⇑t.weights : Convexity.StdSimplex ℝ (Fin (n + 2)) → Fin (n + 2) → ℝ) := by
      rw [Convexity.StdSimplex.range_toFun_comp_weights]
      refine ⟨Set.mem_iInter.2 fun j ↦ ?_, ?_⟩
      · refine Fin.cases ?_ (fun i ↦ ?_) j
        · simp only [Set.mem_ofPred_eq, Fin.cons_zero]; linarith
        · simpa using h₁ i
      · simp [Fin.sum_univ_succ]
    obtain ⟨x, hx⟩ := hmem
    refine ⟨x, ?_⟩
    ext i
    exact congr_fun hx i.succ

lemma isCompact_corner : IsCompact (corner n) :=
  range_dropZero n ▸ isCompact_range (continuous_dropZero n)

lemma interior_corner : interior (corner n) = cornerInt n := by
  apply le_antisymm
  · intro y hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
    have hK : ∀ z, dist z y < ε → z ∈ corner n := fun z hz ↦
      interior_subset (hball (Metric.mem_ball.2 hz))
    have hnorm : ∀ (i : Fin (n + 1)) (c : ℝ), dist (y + PiLp.single 2 i c) y = |c| := by
      intro i c
      rw [dist_eq_norm, add_sub_cancel_left, PiLp.norm_single, Real.norm_eq_abs]
    refine ⟨fun i ↦ ?_, ?_⟩
    · have := (hK _ (by rw [hnorm i (-(ε / 2))]; rw [abs_neg, abs_of_pos (by linarith)]; linarith)).1 i
      simp at this
      linarith
    · have := (hK _ (by rw [hnorm 0 (ε / 2)]; rw [abs_of_pos (by linarith)]; linarith)).2
      simp [PiLp.single_apply, Finset.sum_add_distrib] at this
      linarith
  · refine interior_maximal (fun y hy ↦ ⟨fun i ↦ (hy.1 i).le, hy.2.le⟩) ?_
    have hc : ∀ i : Fin (n + 1), Continuous fun y : EuclideanSpace ℝ (Fin (n + 1)) ↦ y i :=
      fun i ↦ (EuclideanSpace.proj i).continuous
    have : cornerInt n = (⋂ i, {y | 0 < y i}) ∩ {y | ∑ i, y i < 1} := by
      ext y
      simp [cornerInt]
    rw [this]
    exact (isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (hc i)).inter
      (isOpen_lt (continuous_finsetSum _ fun i _ ↦ hc i) continuous_const)


lemma convex_corner : Convex ℝ (corner n) := by
  have : corner n = (⋂ i, {y | 0 ≤ y i}) ∩ {y | ∑ i, y i ≤ 1} := by
    ext y
    simp [corner]
  rw [this]
  refine (convex_iInter fun i ↦ ?_).inter ?_
  · exact convex_halfSpace_ge (EuclideanSpace.proj (𝕜 := ℝ) i).toLinearMap.isLinear 0
  · refine convex_halfSpace_le ⟨fun x y ↦ ?_, fun c x ↦ ?_⟩ 1
    · simp [Finset.sum_add_distrib]
    · simp [Finset.mul_sum]

lemma interior_corner_nonempty : (interior (corner n)).Nonempty := by
  rw [interior_corner]
  refine ⟨WithLp.toLp 2 fun _ ↦ 1 / (2 * (n + 1)), fun i ↦ ?_, ?_⟩
  · positivity
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
    norm_num

lemma dropZero_mem_cornerInt_iff (x : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    dropZero n x ∈ cornerInt n ↔ x.weights.support = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  simp only [Finsupp.mem_support_iff]
  have h0 := weights_zero_eq n x
  constructor
  · rintro ⟨h₁, h₂⟩ j
    refine Fin.cases ?_ (fun i ↦ (h₁ i).ne') j
    rw [h0]
    linarith
  · intro h
    have hpos : ∀ j, 0 < x.weights j := fun j ↦ lt_of_le_of_ne (x.weights_nonneg j) (h j).symm
    refine ⟨fun i ↦ hpos i.succ, ?_⟩
    have := hpos 0
    rw [h0] at this
    linarith

/-- The proper nonempty subsets of `[n]`. -/
def properSubsets (n : ℕ) : Set (Finset (Fin (n + 1))) := {I | I.Nonempty ∧ I ≠ Finset.univ}

lemma isDownClosed_properSubsets (n : ℕ) : IsDownClosed (properSubsets n) :=
  ⟨fun _ h ↦ h.1, fun _ hI _ hJ hJI ↦ ⟨hJ, fun h ↦ hI.2 (Finset.eq_univ_of_forall fun x ↦
    hJI (h ▸ Finset.mem_univ x))⟩⟩

lemma boundary_eq_simplexSub (n : ℕ) :
    (∂Δ[n] : (Δ[n] : SSet.{u}).Subcomplex) = simplexSub (properSubsets n) := by
  ext ⟨m⟩ x
  induction m using SimplexCategory.rec with | _ m => ?_
  rw [mem_simplexSub_iff (isDownClosed_properSubsets n)]
  change ¬ Function.Surjective (stdSimplex.asOrderHom x) ↔ _
  simp only [properSubsets, Set.mem_ofPred_eq, Finset.univ_nonempty, Finset.image_nonempty,
    true_and, ne_eq, Finset.eq_univ_iff_forall, Finset.mem_image, Finset.mem_univ]
  rfl

lemma image_dropZero_boundary :
    dropZero n '' simplexM (properSubsets (n + 1)) = frontier (corner n) := by
  rw [← closure_sdiff_interior, (isCompact_corner n).isClosed.closure_eq, interior_corner,
    ← range_dropZero]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, fun h ↦ hx.2 ((dropZero_mem_cornerInt_iff n x).1 h)⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, ⟨x.support_weights_nonempty, fun h ↦ hx ((dropZero_mem_cornerInt_iff n x).2 h)⟩, rfl⟩

end Sphere

/-- `ALGD-C2-SIMPLEX-11` (定理 11, p.13).
`|∂Δ^n| ≅ S^{n−1}` (stated for `n + 1`): by 補題 10 for the proper subsets of `[n + 1]`,
`|∂Δ^{n+1}| ≅ M_U`, the boundary of `F[n + 1]`, which is homeomorphic to the `n`-sphere. -/
theorem boundary_realization_sphere (n : ℕ) :
    Nonempty (SSet.toTop.obj (∂Δ[n + 1] : SSet.{u}) ≅ TopCat.sphere.{u} n) := by
  obtain ⟨h, -, -, hfr⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_corner n) (interior_corner_nonempty n) (isCompact_corner n).isBounded
  let e₁ : SSet.toTop.obj (∂Δ[n + 1] : SSet.{u}) ≃ₜ simplexM (properSubsets (n + 1)) :=
    (TopCat.homeoOfIso (SSet.toTop.mapIso (Subcomplex.eqToIso (boundary_eq_simplexSub (n + 1))))).trans
      (simplexSubHomeo (isDownClosed_properSubsets (n + 1)))
  let e₂ : simplexM (properSubsets (n + 1)) ≃ₜ frontier (corner n) :=
    ((isClosedEmbedding_dropZero n).isEmbedding.comp IsEmbedding.subtypeVal).toHomeomorph.trans
      (Homeomorph.setCongr (by rw [Set.range_comp, Subtype.range_coe, image_dropZero_boundary]))
  let e₃ : frontier (corner n) ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    (h.image _).trans (Homeomorph.setCongr hfr)
  exact ⟨TopCat.isoOfHomeo (e₁.trans (e₂.trans (e₃.trans Homeomorph.ulift.symm)))⟩

/-! ### Singular simplicial sets are Kan complexes -/

section Kan

variable {n : ℕ}

/-- The faces of the horn `Λ^{n+1,k}`: the nonempty `I` that miss some `j ≠ k`. -/
def hornSets (k : Fin (n + 2)) : Set (Finset (Fin (n + 2))) :=
  {I | I.Nonempty ∧ ∃ j ≠ k, j ∉ I}

lemma isDownClosed_hornSets (k : Fin (n + 2)) : IsDownClosed (hornSets k) :=
  ⟨fun _ h ↦ h.1, fun _ hI _ hJ hJI ↦
    ⟨hJ, hI.2.imp fun _ hj ↦ ⟨hj.1, fun h ↦ hj.2 (hJI h)⟩⟩⟩

lemma horn_eq_simplexSub (k : Fin (n + 2)) :
    (Λ[n + 1, k] : (Δ[n + 1] : SSet.{u}).Subcomplex) = simplexSub (hornSets k) := by
  ext ⟨m⟩ x
  induction m using SimplexCategory.rec with | _ m => ?_
  rw [mem_simplexSub_iff (isDownClosed_hornSets k), SSet.mem_horn_iff]
  constructor
  · intro h
    obtain ⟨j, hj⟩ : ∃ j, j ∉ Set.range ⇑(stdSimplex.asOrderHom x) ∪ {k} := by
      by_contra hc
      push Not at hc
      exact h (Set.eq_univ_of_forall hc)
    rw [Set.mem_union, not_or, Set.mem_singleton_iff] at hj
    refine ⟨⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ 0)⟩, j, hj.2, fun hjI ↦ hj.1 ?_⟩
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hjI
    exact ⟨i, hi⟩
  · rintro ⟨-, j, hjk, hj⟩ h
    have : j ∈ Set.range ⇑(stdSimplex.asOrderHom x) ∪ {k} := h ▸ Set.mem_univ j
    rcases this with ⟨i, hi⟩ | hjk'
    · exact hj (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)
    · exact hjk (Set.mem_singleton_iff.1 hjk')

/-- The minimum of the coordinates `x_j`, `j ≠ k`. -/
noncomputable def hornMin (k : Fin (n + 2)) (x : Convexity.StdSimplex ℝ (Fin (n + 2))) : ℝ :=
  (Finset.univ.erase k).inf' ⟨_, Finset.mem_erase.2 ⟨(Fin.succAbove_ne k 0), Finset.mem_univ _⟩⟩
    fun j ↦ x.weights j

lemma hornMin_nonneg (k : Fin (n + 2)) (x : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    0 ≤ hornMin k x :=
  Finset.le_inf' _ _ fun j _ ↦ x.weights_nonneg j

lemma hornMin_le (k : Fin (n + 2)) (x : Convexity.StdSimplex ℝ (Fin (n + 2))) {j : Fin (n + 2)}
    (hj : j ≠ k) : hornMin k x ≤ x.weights j :=
  Finset.inf'_le _ (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)

/-- The coordinates of the retraction of `F[n + 1]` onto the horn: subtract the minimum `m` of the
`x_j` (`j ≠ k`) from every coordinate and add `(n + 2) m` to `x_k`. -/
noncomputable def hornRetractFun (k : Fin (n + 2)) (x : Convexity.StdSimplex ℝ (Fin (n + 2)))
    (j : Fin (n + 2)) : ℝ :=
  x.weights j - hornMin k x + if j = k then (n + 2) * hornMin k x else 0

lemma hornRetractFun_nonneg (k : Fin (n + 2)) (x : Convexity.StdSimplex ℝ (Fin (n + 2)))
    (j : Fin (n + 2)) : 0 ≤ hornRetractFun k x j := by
  unfold hornRetractFun
  have h0 := hornMin_nonneg k x
  split_ifs with h
  · subst h
    have := x.weights_nonneg j
    nlinarith
  · have := hornMin_le k x h
    linarith

lemma sum_hornRetractFun (k : Fin (n + 2)) (x : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    ∑ j, hornRetractFun k x j = 1 := by
  simp only [hornRetractFun, Finset.sum_add_distrib, Finset.sum_sub_distrib, x.total_of_fintype,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  push_cast
  ring

/-- The retraction `r : F[n + 1] → M_{Λ^{n+1,k}}`. -/
noncomputable def hornRetract (k : Fin (n + 2)) (x : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    Convexity.StdSimplex ℝ (Fin (n + 2)) where
  weights := Finsupp.equivFunOnFinite.symm (hornRetractFun k x)
  nonneg j := hornRetractFun_nonneg k x j
  total := by rw [Finsupp.sum_fintype _ _ (by simp)]; exact sum_hornRetractFun k x

lemma hornRetract_weights (k : Fin (n + 2)) (x : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    ⇑(hornRetract k x).weights = hornRetractFun k x := rfl

lemma continuous_hornRetract (k : Fin (n + 2)) : Continuous (hornRetract k) := by
  have hemb := Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))
  have hw : ∀ j : Fin (n + 2), Continuous fun x : Convexity.StdSimplex ℝ (Fin (n + 2)) ↦
      x.weights j := fun j ↦ (continuous_apply j).comp hemb.continuous
  have hm : Continuous (hornMin k) := Continuous.finset_inf'_apply _ fun j _ ↦ hw j
  rw [hemb.continuous_iff]
  refine continuous_pi fun j ↦ ?_
  change Continuous fun x ↦ hornRetractFun k x j
  unfold hornRetractFun
  split_ifs
  · exact ((hw j).sub hm).add (continuous_const.mul hm)
  · exact ((hw j).sub hm).add continuous_const

lemma hornRetract_mem (k : Fin (n + 2)) (x : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    hornRetract k x ∈ simplexM (hornSets k) := by
  obtain ⟨j, hj, hjm⟩ := Finset.exists_mem_eq_inf' ⟨_, Finset.mem_erase.2
    ⟨(Fin.succAbove_ne k 0), Finset.mem_univ _⟩⟩ fun j ↦ x.weights j
  have hjk := (Finset.mem_erase.1 hj).1
  refine ⟨(hornRetract k x).support_weights_nonempty, j, hjk, ?_⟩
  rw [Finsupp.mem_support_iff, not_not]
  change hornRetractFun k x j = 0
  simp only [hornRetractFun, hjk, ↓reduceIte, add_zero]
  rw [hornMin, hjm, sub_self]

lemma hornRetract_eq_self (k : Fin (n + 2)) {x : Convexity.StdSimplex ℝ (Fin (n + 2))}
    (hx : x ∈ simplexM (hornSets k)) : hornRetract k x = x := by
  obtain ⟨-, j, hjk, hj⟩ := hx
  rw [Finsupp.mem_support_iff, not_not] at hj
  have h0 : hornMin k x = 0 :=
    le_antisymm (hj ▸ hornMin_le k x hjk) (hornMin_nonneg k x)
  rw [← Convexity.StdSimplex.weights_inj]
  ext i
  change hornRetractFun k x i = x.weights i
  simp [hornRetractFun, h0]

/-- `Sing(S)` has fillers for all horns. -/
lemma exists_filler_sing (S : TopCat.{u}) (k : Fin (n + 2))
    (f : (Λ[n + 1, k] : SSet.{u}) ⟶ TopCat.toSSet.obj S) :
    ∃ h : Δ[n + 1] ⟶ TopCat.toSSet.obj S, Λ[n + 1, k].ι ≫ h = f := by
  obtain ⟨hemb, hrange⟩ :
      IsClosedEmbedding (realMap (Λ[n + 1, k] : (Δ[n + 1] : SSet.{u}).Subcomplex)) ∧
        Set.range (realMap (Λ[n + 1, k] : (Δ[n + 1] : SSet.{u}).Subcomplex)) =
          simplexM (hornSets k) := by
    rw [horn_eq_simplexSub]
    exact realMap_simplexSub (isDownClosed_hornSets k)
  let g := (sSetTopAdj.homEquiv _ _).symm f
  let ψ := hemb.isEmbedding.toHomeomorph.symm
  let H : C(SSet.toTop.obj (Δ[n + 1] : SSet.{u}), S) :=
    ⟨fun p ↦ g (ψ ⟨hornRetract k (SimplexCategory.toTopHomeo ⦋n + 1⦌ p),
      hrange ▸ hornRetract_mem k _⟩),
      g.hom.continuous.comp (ψ.continuous.comp
        (((continuous_hornRetract k).comp (SimplexCategory.toTopHomeo _).continuous).subtype_mk
          _))⟩
  refine ⟨sSetTopAdj.homEquiv _ _ (TopCat.ofHom H), ?_⟩
  rw [← Adjunction.homEquiv_naturality_left, ← Equiv.eq_symm_apply]
  ext p
  change g (ψ _) = g p
  congr 1
  rw [Homeomorph.symm_apply_eq]
  apply Subtype.ext
  change hornRetract k (realMap _ p) = realMap _ p
  exact hornRetract_eq_self k (hrange ▸ ⟨p, rfl⟩)

/-- `ALGD-C2-SIMPLEX-12` (定理 12, p.13–14).
For `S ∈ Top`, `Sing(S)` is a Kan complex: a horn `f : Λ^{n,k} → Sing(S)` corresponds to
`|Λ^{n,k}| → S`, which extends to `|Δ^n|` along the retraction of `|Δ^n| ≅ F[n]` onto
`|Λ^{n,k}| ≅ M_U` (補題 10); its transpose is the filler. -/
theorem sing_kanComplex (S : TopCat.{u}) : (TopCat.toSSet.obj S).KanComplex := by
  refine KanComplex.iff.2 fun n k f hf ↦ ?_
  obtain ⟨h, hh⟩ := exists_filler_sing S k hf.desc
  exact ⟨h, fun j hj ↦ by rw [← horn.ι_ι k j hj, Category.assoc, hh, hf.ι_desc]⟩

end Kan

/-! ## Axiom audit

Each verified declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. The
output is pinned with `#guard_msgs`, so `lake build` fails if it changes. -/

/-- info: 'ProjectEpisteme.AlgD.Simplex.realization_singular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Simplex.realization_singular

/-- info: 'ProjectEpisteme.AlgD.Simplex.realization_stdSimplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Simplex.realization_stdSimplex

/-- info: 'ProjectEpisteme.AlgD.Simplex.IsDownClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Simplex.IsDownClosed

/-- info: 'ProjectEpisteme.AlgD.Simplex.simplexSub_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Simplex.simplexSub_spec

/-- info: 'ProjectEpisteme.AlgD.Simplex.realMap_homOfLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Simplex.realMap_homOfLE

/-- info: 'ProjectEpisteme.AlgD.Simplex.realMap_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Simplex.realMap_face

/-- info: 'ProjectEpisteme.AlgD.Simplex.realMap_simplexSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Simplex.realMap_simplexSub

/-- info: 'ProjectEpisteme.AlgD.Simplex.boundary_realization_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Simplex.boundary_realization_sphere

/-- info: 'ProjectEpisteme.AlgD.Simplex.sing_kanComplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Simplex.sing_kanComplex

end ProjectEpisteme.AlgD.Simplex

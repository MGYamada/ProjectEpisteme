module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# alg-d, Chapter 2: フィルター圏, 例 12 (a counterexample in `Top`)

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 2, `filtered.pdf`
(<https://alg-d.com/math/kan_extension/filtered.pdf>), printed date 2026-08-11, 例 12.

The source builds a diagram `T : ℕ × (0 ⇉ 1) → Top`:

* `T (i, 0) := [0, 1/(i+1)]`;
* `T (i, 1) := (T (i, 0) ⊔ T (i, 0))/∼`, where `∼` glues the two copies of `0` and the two
  copies of `1/(i+1)` (a circle);
* `f i, g i : T (i, 0) → T (i, 1)` are the two canonical injections;
* `h i : T (i, 0) → T (i+1, 0)` is `x ↦ min x (1/(i+2))`, and `k i := h i ⊔ h i` on the quotient.

It then shows that `colim_i lim_j T (i, j)` is the two-point discrete space, while
`lim_j colim_i T (i, j)` is the Sierpiński space, so the two are not isomorphic: in `Top`,
finite limits need not commute with filtered colimits.

Here `T` is the curried functor `diagram : ℕ ⥤ WalkingParallelPair ⥤ TopCat`, built with
`Functor.ofSequence`. The quotient `T (i, 1)` is the quotient of the topological sum by the
kernel of `φ i`, which remembers the coordinate and whether the point is an interior point
of the second copy. This kernel is exactly the source's relation `∼`.

The proof uses a topological invariant instead of the source's explicit computation of both
spaces:

* each `lim_j T (i, j)` is discrete (the equalizer of `f i` and `g i` lies over the two
  endpoints), so the colimit, which carries the final topology, is discrete
  (`discreteTopology_colimLim`);
* the colimit inclusions give a continuous map `[0, 1] → lim_j colim_i T (i, j)` that sends
  `0` and `1` to different points (a cocone to the Sierpiński space `Prop` separates them),
  so that space is not discrete (`not_discreteTopology_limColim`).
-/

@[expose] public section

noncomputable section

namespace ProjectEpisteme.AlgD.Filtered.TopExample

open CategoryTheory Limits Topology WalkingParallelPair WalkingParallelPairHom

/-- The right endpoint `1/(i+1)` of `T (i, 0)`. -/
def r (i : ℕ) : ℝ := 1 / (i + 1)

lemma r_pos (i : ℕ) : 0 < r i := by unfold r; positivity

lemma r_zero : r 0 = 1 := by simp [r]

lemma r_succ_lt (i : ℕ) : r (i + 1) < r i := by
  unfold r
  apply one_div_lt_one_div_of_lt (by positivity)
  push_cast
  linarith

lemma r_antitone : Antitone r := fun i j hij ↦ by
  unfold r
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hij 1

/-- `T (i, 0) = [0, 1/(i+1)]`. -/
abbrev T0 (i : ℕ) : TopCat.{0} := TopCat.of (Set.Icc (0 : ℝ) (r i))

/-- The map whose kernel is the source's relation `∼` on `T (i, 0) ⊔ T (i, 0)`: it keeps the
coordinate and records whether the point is an interior point of the second copy. -/
def φ (i : ℕ) : Set.Icc (0 : ℝ) (r i) ⊕ Set.Icc (0 : ℝ) (r i) → ℝ × Prop :=
  Sum.elim (fun x ↦ ((x : ℝ), False)) (fun x ↦ ((x : ℝ), 0 < (x : ℝ) ∧ (x : ℝ) < r i))

/-- `T (i, 1) = (T (i, 0) ⊔ T (i, 0))/∼`, a circle. -/
abbrev T1 (i : ℕ) : TopCat.{0} := TopCat.of (Quotient (Setoid.ker (φ i)))

/-- The first canonical injection `f i : T (i, 0) → T (i, 1)`. -/
def f (i : ℕ) : T0 i ⟶ T1 i :=
  TopCat.ofHom ⟨fun x ↦ Quotient.mk _ (Sum.inl x), continuous_quotient_mk'.comp continuous_inl⟩

/-- The second canonical injection `g i : T (i, 0) → T (i, 1)`. -/
def g (i : ℕ) : T0 i ⟶ T1 i :=
  TopCat.ofHom ⟨fun x ↦ Quotient.mk _ (Sum.inr x), continuous_quotient_mk'.comp continuous_inr⟩

/-- The underlying function of `h i`, `x ↦ min x (1/(i+2))`. -/
def hFun (i : ℕ) (x : Set.Icc (0 : ℝ) (r i)) : Set.Icc (0 : ℝ) (r (i + 1)) :=
  ⟨min (x : ℝ) (r (i + 1)), le_min x.2.1 (r_pos _).le, min_le_right _ _⟩

lemma continuous_hFun (i : ℕ) : Continuous (hFun i) :=
  (continuous_subtype_val.min continuous_const).subtype_mk _

/-- `h i : T (i, 0) → T (i+1, 0)`. -/
def h (i : ℕ) : T0 i ⟶ T0 (i + 1) := TopCat.ofHom ⟨hFun i, continuous_hFun i⟩

/-- How `φ` changes along `h i ⊔ h i`. -/
def ψ (i : ℕ) (p : ℝ × Prop) : ℝ × Prop := (min p.1 (r (i + 1)), p.2 ∧ p.1 < r (i + 1))

lemma φ_sumMap (i : ℕ) (a : Set.Icc (0 : ℝ) (r i) ⊕ Set.Icc (0 : ℝ) (r i)) :
    φ (i + 1) (Sum.map (hFun i) (hFun i) a) = ψ i (φ i a) := by
  rcases a with x | x
  · exact Prod.ext rfl (propext ⟨False.elim, fun hx ↦ hx.1⟩)
  · refine Prod.ext rfl (propext ⟨fun ⟨h1, h2⟩ ↦ ?_, fun ⟨⟨h1, _⟩, h3⟩ ↦ ?_⟩)
    · have hx : 0 < (x : ℝ) := (lt_min_iff.1 h1).1
      have hx' : (x : ℝ) < r (i + 1) := by
        rcases min_lt_iff.1 h2 with h | h
        · exact h
        · exact absurd h (lt_irrefl _)
      exact ⟨⟨hx, hx'.trans (r_succ_lt i)⟩, hx'⟩
    · have h3' : (x : ℝ) < r (i + 1) := h3
      change 0 < min (x : ℝ) (r (i + 1)) ∧ min (x : ℝ) (r (i + 1)) < r (i + 1)
      rw [min_eq_left h3'.le]
      exact ⟨h1, h3'⟩

lemma k_resp (i : ℕ) (a b : Set.Icc (0 : ℝ) (r i) ⊕ Set.Icc (0 : ℝ) (r i))
    (hab : (Setoid.ker (φ i)).r a b) :
    (Setoid.ker (φ (i + 1))).r (Sum.map (hFun i) (hFun i) a) (Sum.map (hFun i) (hFun i) b) :=
  show φ (i + 1) _ = φ (i + 1) _ by rw [φ_sumMap, φ_sumMap, show φ i a = φ i b from hab]

/-- `k i := h i ⊔ h i : T (i, 1) → T (i+1, 1)`. -/
def k (i : ℕ) : T1 i ⟶ T1 (i + 1) :=
  TopCat.ofHom
    ⟨Quotient.map' (s₁ := Setoid.ker (φ i)) (s₂ := Setoid.ker (φ (i + 1)))
        (Sum.map (hFun i) (hFun i)) (k_resp i),
      Continuous.quotient_map' ((continuous_hFun i).sumMap (continuous_hFun i)) (k_resp i)⟩

lemma f_comp_k (i : ℕ) : f i ≫ k i = h i ≫ f (i + 1) := TopCat.ext fun _ ↦ rfl

lemma g_comp_k (i : ℕ) : g i ≫ k i = h i ≫ g (i + 1) := TopCat.ext fun _ ↦ rfl

/-- The source's diagram `T`, curried: `diagram.obj i` is the parallel pair `f i, g i`. -/
def diagram : ℕ ⥤ WalkingParallelPair ⥤ TopCat.{0} :=
  Functor.ofSequence fun i ↦
    parallelPairHom (f i) (g i) (f (i + 1)) (g (i + 1)) (h i) (k i) (f_comp_k i) (g_comp_k i)

lemma diagram_map_succ_app_zero (i : ℕ) :
    (diagram.map (homOfLE (Nat.le_add_right i 1))).app zero = h i := by
  dsimp only [diagram]
  rw [Functor.ofSequence_map_homOfLE_succ, parallelPairHom_app_zero]

lemma diagram_map_succ_app_one (i : ℕ) :
    (diagram.map (homOfLE (Nat.le_add_right i 1))).app one = k i := by
  dsimp only [diagram]
  rw [Functor.ofSequence_map_homOfLE_succ, parallelPairHom_app_one]

/-- `f i x = g i x` exactly at the two endpoints. -/
lemma f_eq_g_iff (i : ℕ) (x : Set.Icc (0 : ℝ) (r i)) :
    f i x = g i x ↔ (x : ℝ) = 0 ∨ (x : ℝ) = r i := by
  constructor
  · intro he
    have h2 : (False : Prop) = (0 < (x : ℝ) ∧ (x : ℝ) < r i) :=
      congrArg Prod.snd (Quotient.exact he : φ i (Sum.inl x) = φ i (Sum.inr x))
    have hn : ¬ (0 < (x : ℝ) ∧ (x : ℝ) < r i) := fun hp ↦ by rw [← h2] at hp; exact hp
    rcases x.2.1.eq_or_lt with h0 | h0
    · exact Or.inl h0.symm
    · rcases x.2.2.eq_or_lt with h1 | h1
      · exact Or.inr h1
      · exact absurd ⟨h0, h1⟩ hn
  · intro hx
    refine Quotient.sound (show φ i (Sum.inl x) = φ i (Sum.inr x) from
      Prod.ext rfl (propext ⟨False.elim, fun hp ↦ ?_⟩))
    rcases hx with hx | hx
    · exact hp.1.ne' hx
    · exact hp.2.ne hx

/-! ### `colim_i lim_j T (i, j)` is discrete -/

lemma discreteTopology_limit_stage (i : ℕ) :
    DiscreteTopology (limit (diagram.obj i) : TopCat.{0}) := by
  let F := diagram.obj i
  let π0 : limit F ⟶ T0 i := limit.π F zero
  have hc : ∀ y : (limit F : TopCat.{0}), f i (π0 y) = g i (π0 y) := fun y ↦
    ConcreteCategory.congr_hom ((limit.w F left).trans (limit.w F right).symm) y
  have hinj : ∀ y z : (limit F : TopCat.{0}), π0 y = π0 z → y = z := fun y z hyz ↦
    Concrete.limit_ext F y z fun j ↦ by
      cases j
      · exact hyz
      · rw [← limit.w F left]
        exact congrArg (F.map left) hyz
  have hend : ∀ y : (limit F : TopCat.{0}), ((π0 y : ℝ) = 0 ∨ (π0 y : ℝ) = r i) := fun y ↦
    (f_eq_g_iff i (π0 y)).1 (hc y)
  refine discreteTopology_iff_isOpen_singleton.2 fun x ↦ ?_
  rcases hend x with hx | hx
  · have hU : IsOpen (π0 ⁻¹' {y | (y : ℝ) < r i}) :=
      (isOpen_lt continuous_subtype_val continuous_const).preimage π0.hom.continuous
    convert hU using 1
    ext y
    constructor
    · rintro rfl
      change (π0 y : ℝ) < r i
      rw [hx]
      exact r_pos i
    · intro hy
      change (π0 y : ℝ) < r i at hy
      refine hinj y x (Subtype.ext ?_)
      rcases hend y with h0 | h0
      · rw [h0, hx]
      · exact absurd h0 hy.ne
  · have hU : IsOpen (π0 ⁻¹' {y | 0 < (y : ℝ)}) :=
      (isOpen_lt continuous_const continuous_subtype_val).preimage π0.hom.continuous
    convert hU using 1
    ext y
    constructor
    · rintro rfl
      change 0 < (π0 y : ℝ)
      rw [hx]
      exact r_pos i
    · intro hy
      change 0 < (π0 y : ℝ) at hy
      refine hinj y x (Subtype.ext ?_)
      rcases hend y with h0 | h0
      · exact absurd h0 hy.ne'
      · rw [h0, hx]

lemma discreteTopology_colimLim : DiscreteTopology (colimit (diagram ⋙ lim) : TopCat.{0}) :=
  discreteTopology_iff_isOpen_singleton.2 fun _ ↦
    (TopCat.colimit_isOpen_iff _ _).2 fun i ↦
      @isOpen_discrete _ _ (discreteTopology_limit_stage i) _

/-! ### `lim_j colim_i T (i, j)` is not discrete -/

/-- The diagram `i ↦ T (i, 0)`. -/
abbrev P : ℕ ⥤ TopCat.{0} := diagram.flip.obj zero

/-- The diagram `i ↦ T (i, 1)`. -/
abbrev Q : ℕ ⥤ TopCat.{0} := diagram.flip.obj one

lemma ιQ_succ (i : ℕ) (y : T1 i) :
    colimit.ι Q i y = colimit.ι Q (i + 1) (k i y) := by
  have h1 := ConcreteCategory.congr_hom (colimit.w Q (homOfLE (Nat.le_add_right i 1))) y
  have h2 : Q.map (homOfLE (Nat.le_add_right i 1)) = k i := diagram_map_succ_app_one i
  rw [← h1, h2]
  rfl

/-- In `colim_i T (i, 1)`, the images of `f i x` and `g i x` agree once `h` has pushed `x`
to an endpoint. -/
lemma ιQ_f_eq_ιQ_g (n : ℕ) : ∀ (i : ℕ) (x : Set.Icc (0 : ℝ) (r i)),
    ((x : ℝ) = 0 ∨ r (i + n) ≤ x) → colimit.ι Q i (f i x) = colimit.ι Q i (g i x) := by
  induction n with
  | zero =>
    intro i x hx
    refine congrArg (colimit.ι Q i) ((f_eq_g_iff i x).2 ?_)
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (le_antisymm x.2.2 hx)
  | succ n ih =>
    intro i x hx
    rw [ιQ_succ i (f i x), ιQ_succ i (g i x)]
    refine ih (i + 1) (hFun i x) ?_
    change min (x : ℝ) (r (i + 1)) = 0 ∨ r (i + 1 + n) ≤ min (x : ℝ) (r (i + 1))
    rcases hx with hx | hx
    · left
      rw [hx]
      exact min_eq_left (r_pos _).le
    · right
      rw [show i + 1 + n = i + (n + 1) by omega]
      exact le_min hx (r_antitone (by omega))

lemma ιQ_f_eq_ιQ_g_zero : f 0 ≫ colimit.ι Q 0 = g 0 ≫ colimit.ι Q 0 := by
  refine TopCat.ext fun x ↦ ?_
  rcases x.2.1.eq_or_lt with hx | hx
  · exact ιQ_f_eq_ιQ_g 0 0 x (Or.inl hx.symm)
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
    refine ιQ_f_eq_ιQ_g n 0 x (Or.inr ?_)
    change 1 / ((0 + n : ℕ) + 1 : ℝ) ≤ x
    simpa using hn.le

/-- The cone over `j ↦ colim_i T (i, j)` with apex `T (0, 0) = [0, 1]` given by the colimit
inclusions at stage `0`. -/
def pathCone : Cone (diagram.flip ⋙ colim) :=
  (Cone.postcompose (diagramIsoParallelPair (diagram.flip ⋙ colim)).inv).obj
    (Fork.ofι (colimit.ι P 0) (by
      change colimit.ι P 0 ≫ colimMap (diagram.flip.map left) =
        colimit.ι P 0 ≫ colimMap (diagram.flip.map right)
      rw [ι_colimMap, ι_colimMap]
      exact ιQ_f_eq_ιQ_g_zero))

/-- The map `T (i, 0) → Prop`, `x ↦ (0 < x)`, to the Sierpiński space. -/
def sApp (i : ℕ) : T0 i ⟶ TopCat.of Prop :=
  TopCat.ofHom ⟨fun x ↦ 0 < (x : ℝ),
    continuous_Prop.2 (isOpen_lt continuous_const continuous_subtype_val)⟩

lemma h_comp_sApp (i : ℕ) : h i ≫ sApp (i + 1) = sApp i :=
  TopCat.ext fun x ↦ show (0 < min (x : ℝ) (r (i + 1))) = (0 < (x : ℝ)) from
    propext ⟨fun hx ↦ (lt_min_iff.1 hx).1, fun hx ↦ lt_min hx (r_pos _)⟩

/-- The Sierpiński-valued cocone on `i ↦ T (i, 0)`, `x ↦ (0 < x)`. -/
def sierpinskiCocone : Cocone P where
  pt := TopCat.of Prop
  ι := NatTrans.ofSequence (F := P) (G := (Functor.const ℕ).obj (TopCat.of Prop)) sApp
    (fun i ↦ (congrArg (· ≫ sApp (i + 1)) (diagram_map_succ_app_zero i)).trans
      ((h_comp_sApp i).trans (Category.comp_id _).symm))

lemma not_discreteTopology_limColim :
    ¬ DiscreteTopology (limit (diagram.flip ⋙ colim) : TopCat.{0}) := by
  intro hD
  let ψ : T0 0 ⟶ limit (diagram.flip ⋙ colim) := limit.lift _ pathCone
  have hconn : PreconnectedSpace (Set.Icc (0 : ℝ) (r 0)) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  let a : Set.Icc (0 : ℝ) (r 0) := ⟨0, le_rfl, (r_pos 0).le⟩
  let b : Set.Icc (0 : ℝ) (r 0) := ⟨1, zero_le_one, r_zero.ge⟩
  have hab : ψ a = ψ b := hconn.constant ψ.hom.continuous
  have hπ : ∀ x, limit.π (diagram.flip ⋙ colim) zero (ψ x) = colimit.ι P 0 x := fun x ↦
    (ConcreteCategory.congr_hom (limit.lift_π pathCone zero) x).trans rfl
  have hP : colimit.ι P 0 a = colimit.ι P 0 b := by
    rw [← hπ, ← hπ, hab]
  have hd : ∀ x : Set.Icc (0 : ℝ) (r 0),
      (colimit.desc P sierpinskiCocone (colimit.ι P 0 x) : Prop) = (0 < (x : ℝ)) := fun x ↦
    ConcreteCategory.congr_hom (colimit.ι_desc sierpinskiCocone 0) x
  have hS := congrArg (colimit.desc P sierpinskiCocone) hP
  rw [hd, hd] at hS
  change (0 < (0 : ℝ)) = (0 < (1 : ℝ)) at hS
  exact lt_irrefl (0 : ℝ) (hS ▸ zero_lt_one)

/-- `ALGD-C2-FILTERED-12` (alg-d `filtered.pdf`, 例 12): in `Top`, finite limits and filtered
colimits need not commute. For the source's diagram `T : ℕ × (0 ⇉ 1) → Top`,
`colim_i lim_j T (i, j)` and `lim_j colim_i T (i, j)` are not isomorphic. -/
theorem isEmpty_colimLim_iso_limColim :
    IsEmpty (colimit (diagram ⋙ lim) ≅ limit (diagram.flip ⋙ colim)) :=
  ⟨fun e ↦ by
    have := discreteTopology_colimLim
    exact not_discreteTopology_limColim (TopCat.homeoOfIso e).discreteTopology⟩

/-! ## Axiom audit -/

/-- info: 'ProjectEpisteme.AlgD.Filtered.TopExample.isEmpty_colimLim_iso_limColim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Filtered.TopExample.isEmpty_colimLim_iso_limColim

end ProjectEpisteme.AlgD.Filtered.TopExample

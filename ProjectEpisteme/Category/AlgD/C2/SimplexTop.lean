module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# alg-d, Chapter 2: 例：単体的集合 (Example: simplicial sets), geometric realization

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 2, `simplex.pdf`
(<https://alg-d.com/math/kan_extension/simplex.pdf>), printed date 2026-10-18,
SHA-256 `728b18894d57b7471bec403811b6cfa6f93cc79de302e08e2d67b2210989a894`,
retrieved 2026-11-26. Ledger: `docs/ledger/algd/C2-SIMPLEX.md`.

This module holds the rows about the topological simplices `F[n]`, the geometric realization
and the singular functor, so that `ProjectEpisteme.Category.AlgD.C2.Simplex` does not import
topology. The conventions are those of that module; `Top` is `TopCat.{u}`.
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

/-! ## Axiom audit

Each verified declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. The
output is pinned with `#guard_msgs`, so `lake build` fails if it changes. -/

/-- info: 'ProjectEpisteme.AlgD.Simplex.realization_singular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Simplex.realization_singular

/-- info: 'ProjectEpisteme.AlgD.Simplex.realization_stdSimplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Simplex.realization_stdSimplex

end ProjectEpisteme.AlgD.Simplex

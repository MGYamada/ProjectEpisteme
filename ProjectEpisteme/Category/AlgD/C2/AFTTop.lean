/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Balanced
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.UrysohnsLemma

/-!
# alg-d, Chapter 2: 随伴関手定理, 例 21 (Stone–Čech compactification via SAFT)

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 2, `aft.pdf`
(<https://alg-d.com/math/kan_extension/aft.pdf>), printed date 2026-07-16, 例 21.
Ledger: `docs/ledger/algd/C2-AFT.md`.

The source applies the special adjoint functor theorem (定理 20) to the inclusion
`U : CptHaus → Top`. It checks that `CptHaus` is well-powered and complete, that `U` is
continuous, and that `[0, 1]` is a cogenerator by Urysohn's lemma. Hence `U` has a left adjoint,
the Stone–Čech compactification.

Here `CptHaus` is mathlib's `CompHaus` and `U` is `compHausToTop`. Well-powered and cogenerator
are mathlib's `WellPowered` and `IsCoseparator`; they agree with the source's notions by
ALGD-C2-AFT-D09 and -D11 (`ProjectEpisteme/Category/AlgD/C2/AFT.lean`). Well-poweredness comes
from mathlib's criterion for balanced categories with a separator (the point). The module
imports only mathlib, so it uses mathlib's special adjoint functor theorem directly.
-/

@[expose] public section

namespace ProjectEpisteme.AlgD.AFT.CompHausExample

open CategoryTheory Limits

universe u

/-- `CompHaus` is balanced: a monomorphism that is an epimorphism is bijective, hence an
isomorphism of compact Hausdorff spaces. -/
instance balanced : Balanced CompHaus.{u} where
  isIso_of_mono_of_epi f _ _ :=
    CompHausLike.isIso_of_bijective f
      ⟨(CompHausLike.mono_iff_injective f).1 inferInstance,
        (CompHaus.epi_iff_surjective f).1 inferInstance⟩

/-- The one-point space is a separator of `CompHaus`. -/
lemma isSeparator_punit : IsSeparator (CompHaus.of PUnit.{u + 1}) := by
  intro X Y f g h
  ext x
  have := h (CompHaus.of PUnit) (by simp)
    (CompHausLike.ofHom _ ⟨fun _ ↦ x, continuous_const⟩)
  exact ConcreteCategory.congr_hom this PUnit.unit

/-- `CompHaus` is well-powered. -/
theorem wellPowered : WellPowered.{u} CompHaus.{u} :=
  wellPowered_of_isSeparator _ isSeparator_punit

/-- The closed interval `[0, 1]`, as an object of `CompHaus.{u}`. -/
abbrev unitIntervalObj : CompHaus.{u} := CompHaus.of (ULift.{u} unitInterval)

/-- `[0, 1]` is a cogenerator of `CompHaus` (Urysohn's lemma). -/
theorem isCoseparator_unitInterval : IsCoseparator unitIntervalObj.{u} := by
  intro X Y f g h
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ g x := by
    by_contra hall
    exact hne (ConcreteCategory.hom_ext _ _ fun x ↦ not_not.1 fun hx ↦ hall ⟨x, hx⟩)
  obtain ⟨φ, hφ₀, hφ₁, hφI⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton (x := f x)) (isClosed_singleton (x := g x))
    (Set.disjoint_singleton.2 hx)
  let k : Y ⟶ unitIntervalObj :=
    CompHausLike.ofHom _ ⟨fun y ↦ ULift.up ⟨φ y, hφI y⟩,
      continuous_uliftUp.comp (φ.continuous.subtype_mk _)⟩
  have hk := ConcreteCategory.congr_hom (h unitIntervalObj (by simp) k) x
  have h0 : φ (f x) = 0 := hφ₀ rfl
  have h1 : φ (g x) = 1 := hφ₁ rfl
  have := congrArg (fun z : ULift.{u} unitInterval ↦ (z.down : ℝ)) hk
  simp only [ConcreteCategory.comp_apply] at this
  change φ (f x) = φ (g x) at this
  rw [h0, h1] at this
  exact zero_ne_one this

/-- `ALGD-C2-AFT-21` (例 21, p.19).
`CptHaus` is well-powered and complete, the inclusion `U : CptHaus → Top` is continuous, and
`[0, 1]` is a cogenerator; hence, by the special adjoint functor theorem, `U` is a right adjoint.
Its left adjoint is the Stone–Čech compactification (`leftAdjointIsoReflector`). -/
theorem compHausToTop_isRightAdjoint :
    WellPowered.{u} CompHaus.{u} ∧ HasLimits CompHaus.{u} ∧
      PreservesLimits compHausToTop.{u} ∧ IsCoseparator unitIntervalObj.{u} ∧
      compHausToTop.{u}.IsRightAdjoint := by
  have := wellPowered.{u}
  refine ⟨this, inferInstance, inferInstance, isCoseparator_unitInterval, ?_⟩
  exact isRightAdjoint_of_preservesLimits_of_isCoseparating.{u}
    (P := ObjectProperty.singleton unitIntervalObj.{u}) isCoseparator_unitInterval.{u}
    compHausToTop.{u}

/-- The left adjoint given by the special adjoint functor theorem is isomorphic to mathlib's
reflector `Top → CompHaus`, which mathlib builds from the Stone–Čech compactification. -/
noncomputable def leftAdjointIsoReflector :
    have := compHausToTop_isRightAdjoint.{u}.2.2.2.2
    compHausToTop.{u}.leftAdjoint ≅ reflector compHausToTop.{u} :=
  have := compHausToTop_isRightAdjoint.{u}.2.2.2.2
  (Adjunction.ofIsRightAdjoint compHausToTop).leftAdjointUniq
    (reflectorAdjunction compHausToTop)

/-! ## Axiom audit -/

/-- info: 'ProjectEpisteme.AlgD.AFT.CompHausExample.compHausToTop_isRightAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.AFT.CompHausExample.compHausToTop_isRightAdjoint

end ProjectEpisteme.AlgD.AFT.CompHausExample

/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Fubini
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Tactic.TFAE
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Topology.Category.TopCat.Adjunctions
public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.Algebra.Category.Grp.CartesianMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# alg-d, Chapter 1: 随伴関手 (Adjoint functors)

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 1, `adjoint.pdf`
(<https://alg-d.com/math/kan_extension/adjoint.pdf>), printed date 2026-06-29,
SHA-256 `8b0c83b4b42c888fa87737d0e7cb32205a7ba62463f3a4e90fff083d4d5ede95`,
retrieved 2026-11-26. Ledger: `docs/ledger/algd/C1-ADJOINT.md`.

## Conventions

* The source composes as `g ∘ f` and writes `GF`; mathlib writes `f ≫ g` and `F ⋙ G`.
* The source defines an adjunction by natural bijections of hom-sets (`HomSetAdjunction` below).
  mathlib's `Adjunction` is the unit–counit form with the triangle identities, which the source
  derives in §2. `HomSetAdjunction.equivAdjunction` identifies the two.
* "Set" is `Type v` for the hom universe `v` of the category in question.
* A universal arrow from `c` to `G` is stated as unique factorization through `η : c ⟶ G d`.
  Its equivalence with initial objects of `StructuredArrow c G` is `ALGD-C1-LIMIT-D07`.
* "Fully faithful" is the proposition `F.Full ∧ F.Faithful`; mathlib's `F.FullyFaithful` is data.
* In §3, `C0` and `D0` are `unitFixed adj` and `counitFixed adj`, and `C1` and `D1` are the
  essential images of `G` and `F`. The conditions of 定理 31 on whiskered transformations are
  stated componentwise.
* In §4, finite products are a chosen `CartesianMonoidalCategory` and `− × a` is `tensorRight a`.
  定理 41 is stated for the curried functor `X ⥤ C ⥤ D` with the parameter first.
* 例 50 is stated for commutative rings and 例 51 with injective morphisms in `Dom`; the source
  leaves both hypotheses implicit.
* Not formalized (mathlib lacks the prerequisites; see the ledger): 例 52, 53 and 55.
-/

@[expose] public section

namespace ProjectEpisteme.AlgD.Adjoint

open CategoryTheory Limits Opposite

universe w w' v₁ v₂ v₃ u u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-! ## §1 Adjunctions and universal arrows -/

/-- `ALGD-C1-ADJOINT-D01` (定義, §1, p.1).
An adjunction `⟨F, G, φ⟩` in the source's sense: bijections
`φ_cd : Hom_D(Fc, d) → Hom_C(c, Gd)` natural in `c ∈ C` and `d ∈ D`. -/
structure HomSetAdjunction (F : C ⥤ D) (G : D ⥤ C) where
  /-- The bijections `φ_cd`. -/
  φ : ∀ c d, (F.obj c ⟶ d) ≃ (c ⟶ G.obj d)
  /-- Naturality in `c`: `φ_{c'd}(f ∘ Fp) = φ_{cd}(f) ∘ p`. -/
  natural_left : ∀ {c' c : C} {d : D} (p : c' ⟶ c) (f : F.obj c ⟶ d),
    φ c' d (F.map p ≫ f) = p ≫ φ c d f
  /-- Naturality in `d`: `φ_{cd'}(q ∘ f) = Gq ∘ φ_{cd}(f)`. -/
  natural_right : ∀ {c : C} {d d' : D} (f : F.obj c ⟶ d) (q : d ⟶ d'),
    φ c d' (f ≫ q) = φ c d f ≫ G.map q

namespace HomSetAdjunction

variable {F : C ⥤ D} {G : D ⥤ C}

/-- The mathlib adjunction with the same bijections. -/
def toAdjunction (h : HomSetAdjunction F G) : F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := h.φ
      homEquiv_naturality_left_symm := fun f g ↦ by
        rw [Equiv.symm_apply_eq, h.natural_left, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f g ↦ h.natural_right f g }

@[simp]
theorem toAdjunction_homEquiv (h : HomSetAdjunction F G) : h.toAdjunction.homEquiv = h.φ :=
  Adjunction.mkOfHomEquiv_homEquiv _

/-- The hom-set adjunction underlying a mathlib adjunction. -/
def ofAdjunction (adj : F ⊣ G) : HomSetAdjunction F G where
  φ := adj.homEquiv
  natural_left p f := adj.homEquiv_naturality_left p f
  natural_right f q := adj.homEquiv_naturality_right f q

/-- Hom-set adjunctions in the source's sense correspond bijectively to mathlib adjunctions, and
the correspondence keeps the bijections `φ_cd`. -/
def equivAdjunction : HomSetAdjunction F G ≃ (F ⊣ G) where
  toFun := toAdjunction
  invFun := ofAdjunction
  left_inv h := by
    obtain ⟨φ, nl, nr⟩ := h
    simp only [ofAdjunction, HomSetAdjunction.mk.injEq]
    exact Adjunction.mkOfHomEquiv_homEquiv _
  right_inv adj := by
    refine Adjunction.ext (NatTrans.ext (funext fun c ↦ ?_))
    rw [← Adjunction.homEquiv_id, toAdjunction_homEquiv]
    exact adj.homEquiv_id c

end HomSetAdjunction

variable {F : C ⥤ D} {G : D ⥤ C}

/-- `ALGD-C1-ADJOINT-01` (命題 1, p.3).
For `f : Fc → d`, `h : Fc' → d'`, `p : c → c'` and `q : d → d'`, the square `q ∘ f = h ∘ Fp`
in `D` commutes iff its transpose `Gq ∘ f̃ = h̃ ∘ p` in `C` commutes. -/
theorem square_iff (adj : F ⊣ G) {c c' : C} {d d' : D} (f : F.obj c ⟶ d) (h : F.obj c' ⟶ d')
    (p : c ⟶ c') (q : d ⟶ d') :
    f ≫ q = F.map p ≫ h ↔ adj.homEquiv c d f ≫ G.map q = p ≫ adj.homEquiv c' d' h := by
  rw [eq_comm, ← adj.homEquiv_naturality_left_square_iff p h f q, eq_comm]

/-- `ALGD-C1-ADJOINT-02` (命題 2, p.3).
For `f : Fc → d`, `h : Fc' → d'`, `p : c → c'` and `q : d' → d`, `f = q ∘ h ∘ Fp` iff
`f̃ = Gq ∘ h̃ ∘ p`. -/
theorem factor_iff (adj : F ⊣ G) {c c' : C} {d d' : D} (f : F.obj c ⟶ d) (h : F.obj c' ⟶ d')
    (p : c ⟶ c') (q : d' ⟶ d) :
    f = F.map p ≫ h ≫ q ↔ adj.homEquiv c d f = p ≫ adj.homEquiv c' d' h ≫ G.map q := by
  rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left, Equiv.apply_eq_iff_eq]

/-- `ALGD-C1-ADJOINT-D03` (prose, pp.3–4).
The unit component is the right adjunct of the identity: `η_c = φ_{c,Fc}(id_{Fc})`. -/
theorem unit_app_eq (adj : F ⊣ G) (c : C) :
    adj.unit.app c = adj.homEquiv c (F.obj c) (𝟙 (F.obj c)) :=
  (adj.homEquiv_id c).symm

/-- `ALGD-C1-ADJOINT-03` (定理 3, p.4).
`⟨Fc, η_c⟩` is a universal arrow from `c` to `G`: every `g : c → Gd` is `Gh ∘ η_c` for a unique
`h : Fc → d`, namely `h = g̃`. -/
theorem unit_universal (adj : F ⊣ G) (c : C) (d : D) (g : c ⟶ G.obj d) :
    ∃! h : F.obj c ⟶ d, adj.unit.app c ≫ G.map h = g := by
  refine ⟨(adj.homEquiv c d).symm g, ?_, fun h hh ↦ ?_⟩ <;> beta_reduce at *
  · exact (adj.homEquiv_unit c d _).symm.trans ((adj.homEquiv c d).apply_symm_apply g)
  · rw [← hh]
    exact ((adj.homEquiv c d).symm_apply_apply h).symm.trans
      (congrArg _ (adj.homEquiv_unit c d h))

/-- `ALGD-C1-ADJOINT-04` ((4), p.4; recalled from 「極限」).
A universal arrow from `c` to `G` exists iff `Hom_C(c, G(−)) : D → Set` is representable
(corepresentable in mathlib's terminology for covariant functors). -/
theorem universalArrow_exists_iff (G : D ⥤ C) (c : C) :
    (∃ (d : D) (η : c ⟶ G.obj d), ∀ (e : D) (g : c ⟶ G.obj e), ∃! h : d ⟶ e, η ≫ G.map h = g) ↔
      (G ⋙ coyoneda.obj (op c)).IsCorepresentable := by
  constructor
  · rintro ⟨d, η, hη⟩
    exact ⟨d, ⟨{ homEquiv := fun {e} ↦ Equiv.ofBijective (fun h : d ⟶ e ↦ η ≫ G.map h)
                  ((Function.bijective_iff_existsUnique _).2 (hη e))
                 homEquiv_comp := fun g f ↦ by simp }⟩⟩
  · rintro ⟨d, ⟨r⟩⟩
    refine ⟨d, r.homEquiv (𝟙 d), fun e g ↦ ?_⟩
    have key : ∀ h : d ⟶ e, r.homEquiv (𝟙 d) ≫ G.map h = r.homEquiv h := fun h ↦ by
      simpa using (r.homEquiv_comp h (𝟙 d)).symm
    refine ⟨r.homEquiv.symm g, ?_, fun h hh ↦ ?_⟩ <;> beta_reduce at *
    · rw [key, Equiv.apply_symm_apply]
    · rw [← hh, key, Equiv.symm_apply_apply]

/-- `ALGD-C1-ADJOINT-05` (系 5, p.5).
The bijection `Hom_D(Fc, d) → Hom_C(c, Gd)` is `f ↦ Gf ∘ η_c`. -/
theorem homEquiv_eq_unit (adj : F ⊣ G) (c : C) (d : D) (f : F.obj c ⟶ d) :
    adj.homEquiv c d f = adj.unit.app c ≫ G.map f :=
  adj.homEquiv_unit c d f

/-- The bijection `Hom_D(d_c, e) → Hom_C(c, Ge)`, `h ↦ Gh ∘ η_c`, of a universal arrow. -/
noncomputable def universalArrowEquiv (G : D ⥤ C) (d : C → D) (η : ∀ c, c ⟶ G.obj (d c))
    (univ : ∀ c (e : D) (g : c ⟶ G.obj e), ∃! h : d c ⟶ e, η c ≫ G.map h = g) (c : C) (e : D) :
    (d c ⟶ e) ≃ (c ⟶ G.obj e) :=
  Equiv.ofBijective (fun h ↦ η c ≫ G.map h) ((Function.bijective_iff_existsUnique _).2 (univ c e))

/-- The functor `F` of 定理 6: the left adjoint built from a family of universal arrows. -/
noncomputable def leftAdjointOfUniversalArrows (G : D ⥤ C) (d : C → D)
    (η : ∀ c, c ⟶ G.obj (d c))
    (univ : ∀ c (e : D) (g : c ⟶ G.obj e), ∃! h : d c ⟶ e, η c ≫ G.map h = g) : C ⥤ D :=
  Adjunction.leftAdjointOfEquiv (universalArrowEquiv G d η univ) fun c e e' q h ↦ by
    simp [universalArrowEquiv]

/-- The adjunction of 定理 6. -/
noncomputable def adjunctionOfUniversalArrows (G : D ⥤ C) (d : C → D)
    (η : ∀ c, c ⟶ G.obj (d c))
    (univ : ∀ c (e : D) (g : c ⟶ G.obj e), ∃! h : d c ⟶ e, η c ≫ G.map h = g) :
    leftAdjointOfUniversalArrows G d η univ ⊣ G :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- `ALGD-C1-ADJOINT-06` (定理 6, pp.5–6).
If every `c ∈ C` has a universal arrow `η_c : c → G d_c` from `c` to `G`, then `c ↦ d_c` extends
to a functor `F` with `GFp ∘ η_c = η_{c'} ∘ p`, the `η_c` form the unit of an adjunction `F ⊣ G`,
and `φ_cd(f) = Gf ∘ η_c`. -/
theorem universalArrows_leftAdjoint (G : D ⥤ C) (d : C → D) (η : ∀ c, c ⟶ G.obj (d c))
    (univ : ∀ c (e : D) (g : c ⟶ G.obj e), ∃! h : d c ⟶ e, η c ≫ G.map h = g) :
    (∀ c, (leftAdjointOfUniversalArrows G d η univ).obj c = d c) ∧
    (∀ {c c' : C} (p : c ⟶ c'),
      η c ≫ G.map ((leftAdjointOfUniversalArrows G d η univ).map p) = p ≫ η c') ∧
    (∀ c, (adjunctionOfUniversalArrows G d η univ).unit.app c = η c) ∧
    (∀ c e (f : d c ⟶ e), (adjunctionOfUniversalArrows G d η univ).homEquiv c e f =
      η c ≫ G.map f) := by
  have hη : ∀ c, (adjunctionOfUniversalArrows G d η univ).unit.app c = η c := fun c ↦ by
    simp only [adjunctionOfUniversalArrows, Adjunction.adjunctionOfEquivLeft_unit_app,
      universalArrowEquiv, Equiv.ofBijective_apply]
    exact (congrArg (η c ≫ ·) (G.map_id (d c))).trans (Category.comp_id (η c))
  have hφ : ∀ c e (f : d c ⟶ e), (adjunctionOfUniversalArrows G d η univ).homEquiv c e f =
      η c ≫ G.map f := fun c e f ↦
    (Adjunction.homEquiv_unit _ c e f).trans (by erw [hη])
  refine ⟨fun c ↦ rfl, fun {c c'} p ↦ ?_, hη, hφ⟩
  have := (adjunctionOfUniversalArrows G d η univ).unit.naturality p
  simp only [Functor.id_map, Functor.comp_map, hη] at this
  exact this.symm

/-- `ALGD-C1-ADJOINT-R01` (※ box after 定理 6, p.6).
`G : D → C` has a left adjoint iff `Hom_C(c, G(−))` is representable for every `c ∈ C`. -/
theorem isRightAdjoint_iff_corepresentable (G : D ⥤ C) :
    G.IsRightAdjoint ↔ ∀ c : C, (G ⋙ coyoneda.obj (op c)).IsCorepresentable := by
  rw [Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top]
  constructor
  · intro h c
    rw [← Functor.leftAdjointObjIsDefined_iff, h]
    trivial
  · intro h
    exact top_unique fun c _ ↦ (Functor.leftAdjointObjIsDefined_iff G c).2 (h c)

/-- `ALGD-C1-ADJOINT-D04` (prose, p.6).
The unit `η : id_C ⇒ GF` is natural: `GFp ∘ η_c = η_{c'} ∘ p`. -/
theorem unit_naturality (adj : F ⊣ G) {c c' : C} (p : c ⟶ c') :
    adj.unit.app c ≫ G.map (F.map p) = p ≫ adj.unit.app c' :=
  adj.unit_naturality p

/-- `ALGD-C1-ADJOINT-07` (定理 7, pp.6–7).
A left adjoint is unique up to natural isomorphism. -/
theorem leftAdjoint_unique {F' : C ⥤ D} (adj : F ⊣ G) (adj' : F' ⊣ G) : Nonempty (F ≅ F') :=
  ⟨adj.leftAdjointUniq adj'⟩

/-- `ALGD-C1-ADJOINT-08` (定理 8, pp.7–8).
Left adjoints preserve colimits: if `⟨c, μ⟩` is a colimit of `T : J → C`, then `⟨Fc, Fμ⟩` is a
colimit of `FT`. -/
theorem leftAdjoint_preserves_colimit (adj : F ⊣ G) {J : Type w} [Category.{w'} J] {T : J ⥤ C}
    {s : Cocone T} (hs : IsColimit s) : Nonempty (IsColimit (F.mapCocone s)) :=
  haveI := adj.leftAdjoint_preservesColimits.{w', w}
  ⟨isColimitOfPreserves F hs⟩

/-- `ALGD-C1-ADJOINT-09` (命題 9, p.8).
If `F ⊣ G` then `G^op ⊣ F^op`. -/
theorem op_adjunction (adj : F ⊣ G) : Nonempty (G.op ⊣ F.op) :=
  ⟨adj.op⟩

/-- The bijection `Hom_C(c', c_d) → Hom_D(F c', d)`, `g ↦ ε_d ∘ Fg`, of a universal arrow from
`F` to `d`, inverted. -/
noncomputable def universalArrowFromEquiv (F : C ⥤ D) (c : D → C) (ε : ∀ d, F.obj (c d) ⟶ d)
    (univ : ∀ d (c' : C) (f : F.obj c' ⟶ d), ∃! g : c' ⟶ c d, F.map g ≫ ε d = f) (c' : C) (d : D) :
    (F.obj c' ⟶ d) ≃ (c' ⟶ c d) :=
  (Equiv.ofBijective (fun g : c' ⟶ c d ↦ F.map g ≫ ε d)
    ((Function.bijective_iff_existsUnique _).2 (univ d c'))).symm

theorem universalArrowFromEquiv_naturality (F : C ⥤ D) (c : D → C) (ε : ∀ d, F.obj (c d) ⟶ d)
    (univ : ∀ d (c' : C) (f : F.obj c' ⟶ d), ∃! g : c' ⟶ c d, F.map g ≫ ε d = f)
    (X' X : C) (Y : D) (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    universalArrowFromEquiv F c ε univ X' Y (F.map f ≫ g) =
      f ≫ universalArrowFromEquiv F c ε univ X Y g := by
  rw [universalArrowFromEquiv, Equiv.symm_apply_eq]
  simp only [Equiv.ofBijective_apply, F.map_comp, Category.assoc]
  congr 1
  exact ((Equiv.ofBijective (fun g : X ⟶ c Y ↦ F.map g ≫ ε Y)
    ((Function.bijective_iff_existsUnique _).2 (univ Y X))).apply_symm_apply g).symm

/-- The right adjoint built from a family of universal arrows `ε_d : F c_d → d` from `F`. -/
noncomputable def rightAdjointOfUniversalArrows (F : C ⥤ D) (c : D → C)
    (ε : ∀ d, F.obj (c d) ⟶ d)
    (univ : ∀ d (c' : C) (f : F.obj c' ⟶ d), ∃! g : c' ⟶ c d, F.map g ≫ ε d = f) : D ⥤ C :=
  Adjunction.rightAdjointOfEquiv (universalArrowFromEquiv F c ε univ)
    (universalArrowFromEquiv_naturality F c ε univ)

/-- The adjunction `F ⊣ rightAdjointOfUniversalArrows F c ε univ`. -/
noncomputable def adjunctionOfUniversalArrowsFrom (F : C ⥤ D) (c : D → C)
    (ε : ∀ d, F.obj (c d) ⟶ d)
    (univ : ∀ d (c' : C) (f : F.obj c' ⟶ d), ∃! g : c' ⟶ c d, F.map g ≫ ε d = f) :
    F ⊣ rightAdjointOfUniversalArrows F c ε univ :=
  Adjunction.adjunctionOfEquivRight _ _

theorem adjunctionOfUniversalArrowsFrom_counit_app (F : C ⥤ D) (c : D → C)
    (ε : ∀ d, F.obj (c d) ⟶ d)
    (univ : ∀ d (c' : C) (f : F.obj c' ⟶ d), ∃! g : c' ⟶ c d, F.map g ≫ ε d = f) (d : D) :
    (adjunctionOfUniversalArrowsFrom F c ε univ).counit.app d = ε d := by
  simp only [adjunctionOfUniversalArrowsFrom, Adjunction.adjunctionOfEquivRight_counit_app,
    universalArrowFromEquiv, Equiv.symm_symm, Equiv.ofBijective_apply]
  exact (congrArg (· ≫ ε d) (F.map_id (c d))).trans (Category.id_comp (ε d))

/-- `ALGD-C1-ADJOINT-10` (定理 10, pp.8–9).
The dual results. For `F ⊣ G`: (a) `⟨Gd, ε_d⟩` with `ε_d = (id_{Gd})~` is a universal arrow from
`F` to `d`, and the inverse bijection is `g ↦ ε_d ∘ Fg`; (b) the counit `ε` is natural;
(c) a functor with a universal arrow from it to every object has a right adjoint;
(d) right adjoints are unique up to natural isomorphism; (e) right adjoints preserve limits. -/
theorem counit_dual (adj : F ⊣ G) :
    ((∀ (d : D) (c : C) (f : F.obj c ⟶ d), ∃! g : c ⟶ G.obj d, F.map g ≫ adj.counit.app d = f) ∧
      (∀ d, adj.counit.app d = (adj.homEquiv (G.obj d) d).symm (𝟙 (G.obj d))) ∧
      (∀ c d (g : c ⟶ G.obj d), (adj.homEquiv c d).symm g = F.map g ≫ adj.counit.app d)) ∧
    (∀ {d d' : D} (q : d ⟶ d'), F.map (G.map q) ≫ adj.counit.app d' = adj.counit.app d ≫ q) ∧
    (∀ F' : C ⥤ D, (∀ d : D, ∃ (c : C) (ε : F'.obj c ⟶ d),
        ∀ (c' : C) (f : F'.obj c' ⟶ d), ∃! g : c' ⟶ c, F'.map g ≫ ε = f) → F'.IsLeftAdjoint) ∧
    (∀ {G' : D ⥤ C}, (F ⊣ G') → Nonempty (G ≅ G')) ∧
    (∀ {J : Type w} [Category.{w'} J] {T : J ⥤ D} {s : Cone T}, IsLimit s →
      Nonempty (IsLimit (G.mapCone s))) := by
  refine ⟨⟨fun d c f ↦ ?_, fun d ↦ (adj.homEquiv_symm_id d).symm, adj.homEquiv_counit⟩,
    fun q ↦ adj.counit_naturality q, fun F' hF' ↦ ?_, fun adj' ↦ ⟨adj.rightAdjointUniq adj'⟩,
    fun hs ↦ ?_⟩
  · refine ⟨adj.homEquiv c d f, ?_, fun g hg ↦ ?_⟩ <;> beta_reduce at *
    · exact (adj.homEquiv_counit c d _).symm.trans ((adj.homEquiv c d).symm_apply_apply f)
    · rw [← hg]
      exact ((adj.homEquiv c d).apply_symm_apply g).symm.trans
        (congrArg _ (adj.homEquiv_counit c d g))
  · choose c ε hε using hF'
    exact (adjunctionOfUniversalArrowsFrom F' c ε hε).isLeftAdjoint
  · have := adj.rightAdjoint_preservesLimits.{w', w}
    exact ⟨isLimitOfPreserves G hs⟩

/-- `ALGD-C1-ADJOINT-11` (例 11, p.9).
If every `T : J → C` has a colimit, then `colim ⊣ Δ`, the unit at `T` is the colimit cocone `μ`
and the bijection is `f ↦ Δf ∘ μ`; `colim` preserves colimits, so iterated colimits commute; and
if every `T` has a limit, then `Δ ⊣ lim`. -/
theorem colim_adjunction (J : Type w) [Category.{w'} J] [HasColimitsOfShape J C] :
    (∀ T : J ⥤ C, (colimConstAdj (J := J) (C := C)).unit.app T = (colimit.cocone T).ι) ∧
    (∀ (T : J ⥤ C) (c : C) (f : colimit T ⟶ c),
      (colimConstAdj (J := J) (C := C)).homEquiv T c f =
        (colimit.cocone T).ι ≫ (Functor.const J).map f) ∧
    PreservesColimitsOfSize.{w', w} (colim : (J ⥤ C) ⥤ C) ∧
    (∀ {I : Type w} [Category.{w'} I] [HasColimitsOfShape I C] (T : I ⥤ J ⥤ C),
      Nonempty (colimit (T.flip ⋙ colim) ≅ colimit (T ⋙ colim))) ∧
    (∀ [HasLimitsOfShape J C], Nonempty (Functor.const J ⊣ (lim : (J ⥤ C) ⥤ C))) := by
  have hunit : ∀ T : J ⥤ C, (colimConstAdj (J := J) (C := C)).unit.app T =
      (colimit.cocone T).ι := fun T ↦ by
    ext j
    simp [colimConstAdj]
  refine ⟨hunit, fun T c f ↦ by rw [Adjunction.homEquiv_unit, hunit],
    colimConstAdj.leftAdjoint_preservesColimits,
    fun T ↦ ⟨colimitFlipCompColimIsoColimitCompColim T⟩,
    ⟨constLimAdj⟩⟩

/-- `ALGD-C1-ADJOINT-12` (例 12, pp.9–10).
The free abelian group functor is left adjoint to the forgetful functor `U : Ab → Set`, so `U`
preserves limits. `U` has no right adjoint, because it does not preserve coproducts; here the
failing coproduct is the empty one, since `U(0)` is not empty. -/
theorem free_abelian_group :
    Nonempty (AddCommGrpCat.free.{u} ⊣ forget AddCommGrpCat.{u}) ∧
    PreservesLimitsOfSize.{w', w} (forget AddCommGrpCat.{u}) ∧
    ¬ (forget AddCommGrpCat.{u}).IsLeftAdjoint := by
  refine ⟨⟨AddCommGrpCat.adj⟩, AddCommGrpCat.adj.rightAdjoint_preservesLimits, ?_⟩
  rintro ⟨R, ⟨adj⟩⟩
  have := adj.leftAdjoint_preservesColimits.{0, 0}
  have hZ : IsInitial (AddCommGrpCat.of.{u} PUnit) :=
    (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of PUnit)).isInitial
  exact ((hZ.isInitialObj (forget AddCommGrpCat)).to PEmpty (0 : AddCommGrpCat.of PUnit)).elim

/-- `ALGD-C1-ADJOINT-13` (例 13, p.10).
For the forgetful functor `U : Top → Set`, the discrete and indiscrete space functors satisfy
`F ⊣ U ⊣ G`; hence `U` preserves colimits (such as `X ⊔ Y`) and limits (such as `X × Y`). -/
theorem top_discrete_indiscrete :
    Nonempty (TopCat.discrete.{u} ⊣ forget TopCat.{u}) ∧
    Nonempty (forget TopCat.{u} ⊣ TopCat.trivial.{u}) ∧
    PreservesColimitsOfSize.{w', w} (forget TopCat.{u}) ∧
    PreservesLimitsOfSize.{w', w} (forget TopCat.{u}) :=
  ⟨⟨TopCat.adj₁⟩, ⟨TopCat.adj₂⟩, TopCat.adj₂.leftAdjoint_preservesColimits,
    TopCat.adj₁.rightAdjoint_preservesLimits⟩

/-- `ALGD-C1-ADJOINT-D05` (定義, §1, p.10).
`f : a → b` is a split epimorphism iff `f ∘ g = id_b` for some `g : b → a`, and a split
monomorphism iff `g ∘ f = id_a` for some `g : b → a`. -/
theorem split_iff {a b : C} (f : a ⟶ b) :
    (IsSplitEpi f ↔ ∃ g : b ⟶ a, g ≫ f = 𝟙 b) ∧ (IsSplitMono f ↔ ∃ g : b ⟶ a, f ≫ g = 𝟙 a) :=
  ⟨⟨fun _ ↦ ⟨section_ f, IsSplitEpi.id f⟩, fun ⟨g, hg⟩ ↦ IsSplitEpi.mk' ⟨g, hg⟩⟩,
    ⟨fun _ ↦ ⟨retraction f, IsSplitMono.id f⟩, fun ⟨g, hg⟩ ↦ IsSplitMono.mk' ⟨g, hg⟩⟩⟩

/-- `ALGD-C1-ADJOINT-14` (命題 14, pp.10–11).
Split epimorphisms are epimorphisms and split monomorphisms are monomorphisms. -/
theorem split_epi_mono {a b : C} (f : a ⟶ b) : (IsSplitEpi f → Epi f) ∧ (IsSplitMono f → Mono f) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

/-- `ALGD-C1-ADJOINT-15` (命題 15, p.11).
A monomorphism that is a split epimorphism is an isomorphism. -/
theorem isIso_of_mono_of_split_epi {a b : C} (f : a ⟶ b) [Mono f] [IsSplitEpi f] : IsIso f :=
  isIso_of_mono_of_isSplitEpi f

/-- `ALGD-C1-ADJOINT-R02` (prose after 命題 15, p.11).
An epimorphism that is a split monomorphism is an isomorphism. -/
theorem isIso_of_epi_of_split_mono {a b : C} (f : a ⟶ b) [Epi f] [IsSplitMono f] : IsIso f :=
  isIso_of_epi_of_isSplitMono f

/-- `ALGD-C1-ADJOINT-16` (命題 16, p.11).
(1) Functors preserve split epimorphisms; (2) a fully faithful functor reflects them. -/
theorem map_split_epi (F : C ⥤ D) {a b : C} (f : a ⟶ b) :
    (IsSplitEpi f → IsSplitEpi (F.map f)) ∧
    (F.Full → F.Faithful → IsSplitEpi (F.map f) → IsSplitEpi f) :=
  ⟨fun _ ↦ inferInstance, fun _ _ h ↦ (F.isSplitEpi_iff f).1 h⟩

/-- `ALGD-C1-ADJOINT-17` (補題 17, pp.11–12).
For `f : a → b` and the Yoneda embedding `y`: (1) `f` is split epi iff `y(f)` is split epi iff
`y(f)` is epi; (2) `f` is mono iff `y(f)` is mono; (3) `f` is split mono iff `y(f)` is split
mono. -/
theorem yoneda_split {a b : C} (f : a ⟶ b) :
    (IsSplitEpi f ↔ IsSplitEpi (yoneda.map f)) ∧
    (IsSplitEpi (yoneda.map f) ↔ Epi (yoneda.map f)) ∧
    (Mono f ↔ Mono (yoneda.map f)) ∧
    (IsSplitMono f ↔ IsSplitMono (yoneda.map f)) := by
  refine ⟨(yoneda.isSplitEpi_iff f).symm, ⟨fun _ ↦ inferInstance, fun h ↦ ?_⟩,
    (yoneda.mono_map_iff_mono f).symm, (yoneda.isSplitMono_iff f).symm⟩
  rw [NatTrans.epi_iff_epi_app] at h
  obtain ⟨g, hg⟩ := (epi_iff_surjective _).1 (h (op b)) (𝟙 b)
  have : IsSplitEpi f := IsSplitEpi.mk' ⟨g, by simpa using hg⟩
  infer_instance

/-- `ALGD-C1-ADJOINT-18` (定理 18, pp.12–13).
For `F ⊣ G` with unit `η` and counit `ε`: (1) `F` is faithful iff every `η_c` is mono; (2) `F` is
full iff every `η_c` is split epi; (3) `F` is fully faithful iff every `η_c` is iso; (4)–(6) the
same for `G` with `ε_d` epi, split mono and iso. -/
theorem faithful_full_criteria (adj : F ⊣ G) :
    (F.Faithful ↔ ∀ c, Mono (adj.unit.app c)) ∧
    (F.Full ↔ ∀ c, IsSplitEpi (adj.unit.app c)) ∧
    (F.Full ∧ F.Faithful ↔ ∀ c, IsIso (adj.unit.app c)) ∧
    (G.Faithful ↔ ∀ d, Epi (adj.counit.app d)) ∧
    (G.Full ↔ ∀ d, IsSplitMono (adj.counit.app d)) ∧
    (G.Full ∧ G.Faithful ↔ ∀ d, IsIso (adj.counit.app d)) := by
  refine ⟨⟨fun _ ↦ adj.unit_mono_of_L_faithful, fun _ ↦ adj.faithful_L_of_mono_unit_app⟩,
    ⟨fun _ ↦ adj.unit_isSplitEpi_of_L_full, fun _ ↦ adj.full_L_of_isSplitEpi_unit_app⟩,
    ⟨fun ⟨_, _⟩ _ ↦ by have := adj.unit_isIso_of_L_fully_faithful; infer_instance, fun _ ↦ ?_⟩,
    ⟨fun _ ↦ adj.counit_epi_of_R_faithful, fun _ ↦ adj.faithful_R_of_epi_counit_app⟩,
    ⟨fun _ ↦ adj.counit_isSplitMono_of_R_full, fun _ ↦ adj.full_R_of_isSplitMono_counit_app⟩,
    ⟨fun ⟨_, _⟩ _ ↦ by have := adj.counit_isIso_of_R_fully_faithful; infer_instance,
      fun _ ↦ ?_⟩⟩
  · have : IsIso adj.unit := NatIso.isIso_of_isIso_app _
    exact ⟨adj.fullyFaithfulLOfIsIsoUnit.full, adj.fullyFaithfulLOfIsIsoUnit.faithful⟩
  · have : IsIso adj.counit := NatIso.isIso_of_isIso_app _
    exact ⟨adj.fullyFaithfulROfIsIsoCounit.full, adj.fullyFaithfulROfIsIsoCounit.faithful⟩

/-- `ALGD-C1-ADJOINT-19` (定理 19, pp.13–14).
For `F ⊣ G ⊣ H`, every unit component of `F ⊣ G` is iso iff every counit component of `G ⊣ H`
is iso; hence `F` is fully faithful iff `H` is. -/
theorem triple_fullyFaithful {H : C ⥤ D} (adj₁ : F ⊣ G) (adj₂ : G ⊣ H) :
    ((∀ c, IsIso (adj₁.unit.app c)) ↔ ∀ c, IsIso (adj₂.counit.app c)) ∧
    (F.Full ∧ F.Faithful ↔ H.Full ∧ H.Faithful) := by
  have key : (∀ c, IsIso (adj₁.unit.app c)) ↔ ∀ c, IsIso (adj₂.counit.app c) := by
    rw [← NatTrans.isIso_iff_isIso_app, ← NatTrans.isIso_iff_isIso_app]
    exact (Adjunction.Triple.mk adj₁ adj₂).isIso_unit_iff_isIso_counit
  exact ⟨key, (faithful_full_criteria adj₁).2.2.1.trans
    (key.trans (faithful_full_criteria adj₂).2.2.2.2.2.symm)⟩

/-! ## §2 Triangle identities and equivalences -/

namespace HomSetAdjunction

/-- The unit component `η_c := φ_{c,Fc}(id_{Fc})` of a hom-set adjunction. -/
def unitApp (h : HomSetAdjunction F G) (c : C) : c ⟶ G.obj (F.obj c) :=
  h.φ c (F.obj c) (𝟙 _)

/-- The counit component `ε_d := φ_{Gd,d}⁻¹(id_{Gd})` of a hom-set adjunction. -/
def counitApp (h : HomSetAdjunction F G) (d : D) : F.obj (G.obj d) ⟶ d :=
  (h.φ (G.obj d) d).symm (𝟙 _)

/-- `ALGD-C1-ADJOINT-20` (定理 20, §2, pp.14–15).
For a hom-set adjunction, `Gε_d ∘ η_{Gd} = id_{Gd}`, derived from the naturality of `φ`. -/
theorem right_triangle (h : HomSetAdjunction F G) (d : D) :
    h.unitApp (G.obj d) ≫ G.map (h.counitApp d) = 𝟙 (G.obj d) := by
  rw [unitApp, ← h.natural_right, Category.id_comp, counitApp, Equiv.apply_symm_apply]

/-- `ALGD-C1-ADJOINT-R03` (prose after 定理 20, p.15).
Dually, `ε_{Fc} ∘ Fη_c = id_{Fc}`. -/
theorem left_triangle (h : HomSetAdjunction F G) (c : C) :
    F.map (h.unitApp c) ≫ h.counitApp (F.obj c) = 𝟙 (F.obj c) := by
  apply (h.φ c (F.obj c)).injective
  rw [h.natural_left, counitApp, Equiv.apply_symm_apply, Category.comp_id, unitApp]

theorem toAdjunction_unit_app (h : HomSetAdjunction F G) (c : C) :
    h.toAdjunction.unit.app c = h.unitApp c := by
  rw [← Adjunction.homEquiv_id, toAdjunction_homEquiv]
  rfl

theorem toAdjunction_counit_app (h : HomSetAdjunction F G) (d : D) :
    h.toAdjunction.counit.app d = h.counitApp d := by
  rw [← Adjunction.homEquiv_symm_id, toAdjunction_homEquiv]
  rfl

end HomSetAdjunction

/-- `ALGD-C1-ADJOINT-21` (定理 21, pp.15–16).
Natural transformations `η : id_C ⇒ GF` and `ε : FG ⇒ id_D` satisfying the triangle identities
give a hom-set adjunction with `φ_cd(f) = Gf ∘ η_c` and inverse `ψ_cd(g) = ε_d ∘ Fg`. -/
theorem adjunction_of_triangle (η : 𝟭 C ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D)
    (right : ∀ d, η.app (G.obj d) ≫ G.map (ε.app d) = 𝟙 (G.obj d))
    (left : ∀ c, F.map (η.app c) ≫ ε.app (F.obj c) = 𝟙 (F.obj c)) :
    ∃ h : HomSetAdjunction F G, ∀ c d,
      (∀ f : F.obj c ⟶ d, h.φ c d f = η.app c ≫ G.map f) ∧
      (∀ g : c ⟶ G.obj d, (h.φ c d).symm g = F.map g ≫ ε.app d) := by
  let adj : F ⊣ G :=
    { unit := η, counit := ε, left_triangle_components := left,
      right_triangle_components := right }
  exact ⟨.ofAdjunction adj, fun c d ↦ ⟨adj.homEquiv_unit c d, adj.homEquiv_counit c d⟩⟩

/-- `ALGD-C1-ADJOINT-22` (命題 22, pp.18–20).
If `FG ≅ id_D` by some natural isomorphism, then the counit of `F ⊣ G` is an isomorphism. -/
theorem counit_isIso_of_iso (adj : F ⊣ G) (σ : G ⋙ F ≅ 𝟭 D) : IsIso adj.counit :=
  adj.isIso_counit_of_iso σ

/-- `ALGD-C1-ADJOINT-23` (命題 23, pp.21–22).
An equivalence `η : id_C ≅ GF`, `σ : FG ≅ id_D` gives an adjunction `F ⊣ G` with unit `η` and
counit `ε_d = σ_d ∘ F(η_{Gd})⁻¹ ∘ σ_{FGd}⁻¹`. -/
theorem adjunction_of_equivalence (η : 𝟭 C ≅ F ⋙ G) (σ : G ⋙ F ≅ 𝟭 D) :
    ∃ adj : F ⊣ G, adj.unit = η.hom ∧ ∀ d, adj.counit.app d =
      (σ.app (F.obj (G.obj d))).inv ≫ F.map (η.app (G.obj d)).inv ≫ (σ.app d).hom := by
  refine ⟨(CategoryTheory.Equivalence.mk G F σ.symm η.symm).symm.toAdjunction, rfl, fun d ↦ ?_⟩
  change (Equivalence.adjointifyη σ.symm η.symm).inv.app d = _
  have h : F.map (G.map (σ.inv.app d)) = σ.inv.app (F.obj (G.obj d)) := by
    have := σ.inv.naturality (σ.inv.app d)
    simp only [Functor.id_map, Functor.comp_map] at this
    exact ((cancel_epi (σ.inv.app d)).1 this).symm
  simp [Equivalence.adjointifyη, Trans.trans, h]

/-- `ALGD-C1-ADJOINT-24` (系 24, p.22).
An equivalence of categories preserves limits and colimits. -/
theorem equivalence_preserves (F : C ⥤ D) [F.IsEquivalence] :
    PreservesColimitsOfSize.{w', w} F ∧ PreservesLimitsOfSize.{w', w} F :=
  ⟨inferInstance, inferInstance⟩

/-- `ALGD-C1-ADJOINT-25` (系 25, p.22).
Cocompleteness is invariant under equivalence of categories. -/
theorem hasColimits_of_equivalence (e : C ≌ D) [HasColimitsOfSize.{w', w} C] :
    HasColimitsOfSize.{w', w} D :=
  Adjunction.has_colimits_of_equivalence e.inverse

theorem unit_counit_iso_aux (adj : F ⊣ G) :
    ((∀ c, IsIso (adj.unit.app c)) → F.Full ∧ F.Faithful ∧ G.EssSurj) ∧
    ((∀ d, IsIso (adj.counit.app d)) → G.Full ∧ G.Faithful ∧ F.EssSurj) :=
  ⟨fun h ↦ ⟨((faithful_full_criteria adj).2.2.1.2 h).1,
      ((faithful_full_criteria adj).2.2.1.2 h).2, ⟨fun c ↦ adj.mem_essImage_of_unit_isIso c⟩⟩,
    fun h ↦ ⟨((faithful_full_criteria adj).2.2.2.2.2.2 h).1,
      ((faithful_full_criteria adj).2.2.2.2.2.2 h).2,
      ⟨fun d ↦ adj.mem_essImage_of_counit_isIso d⟩⟩⟩

/-- `ALGD-C1-ADJOINT-R04` (※ box, p.23).
If the unit of `F ⊣ G` is an isomorphism, `F` is fully faithful and `G` is essentially
surjective; dually for the counit. Hence the functor of an equivalence is fully faithful and
essentially surjective. -/
theorem unit_counit_iso_consequences (adj : F ⊣ G) :
    ((∀ c, IsIso (adj.unit.app c)) → F.Full ∧ F.Faithful ∧ G.EssSurj) ∧
    ((∀ d, IsIso (adj.counit.app d)) → G.Full ∧ G.Faithful ∧ F.EssSurj) ∧
    (∀ e : C ≌ D, e.functor.Full ∧ e.functor.Faithful ∧ e.functor.EssSurj) := by
  refine ⟨(unit_counit_iso_aux adj).1, (unit_counit_iso_aux adj).2, fun e ↦ ?_⟩
  have hη : ∀ c, IsIso (e.toAdjunction.unit.app c) := fun c ↦ by
    rw [Equivalence.toAdjunction_unit]
    infer_instance
  have hε : ∀ d, IsIso (e.toAdjunction.counit.app d) := fun d ↦ by
    rw [Equivalence.toAdjunction_counit]
    infer_instance
  exact ⟨((unit_counit_iso_aux e.toAdjunction).1 hη).1,
    ((unit_counit_iso_aux e.toAdjunction).1 hη).2.1,
    ((unit_counit_iso_aux e.toAdjunction).2 hε).2.2⟩

/-- `ALGD-C1-ADJOINT-R05` (※ box, p.23).
If `F ⊣ G` and both `F` and `G` are fully faithful, then `F` is an equivalence. -/
theorem isEquivalence_of_fullyFaithful (adj : F ⊣ G) [F.Full] [F.Faithful] [G.Full]
    [G.Faithful] : F.IsEquivalence := by
  have hε := (faithful_full_criteria adj).2.2.2.2.2.1 ⟨inferInstance, inferInstance⟩
  have := ((unit_counit_iso_aux adj).2 hε).2.2
  exact { }

/-- `ALGD-C1-ADJOINT-R06` (※ box, p.23).
For a field `k`, the free vector space functor `F : Set → Vect_k` is essentially surjective (every
vector space has a basis), the forgetful functor `U` is faithful but not full, and so the counit
of `F ⊣ U` is not an isomorphism. -/
theorem free_vectorSpace (k : Type u) [Field k] :
    (ModuleCat.free k).EssSurj ∧ (forget (ModuleCat.{u} k)).Faithful ∧
    ¬ (forget (ModuleCat.{u} k)).Full ∧ ¬ ∀ V, IsIso ((ModuleCat.adj k).counit.app V) := by
  have hfull : ¬ (forget (ModuleCat.{u} k)).Full := by
    intro _
    let M := ModuleCat.of k k
    let g : (forget (ModuleCat k)).obj M ⟶ (forget (ModuleCat k)).obj M :=
      TypeCat.ofHom fun _ ↦ (1 : k)
    have h := ConcreteCategory.congr_hom ((forget (ModuleCat k)).map_preimage g) (0 : k)
    simp [g] at h
  refine ⟨⟨fun V ↦ ⟨_, ⟨(LinearEquiv.toModuleIso (Module.Basis.ofVectorSpace k V).repr).symm⟩⟩⟩,
    inferInstance, hfull, fun h ↦ hfull ?_⟩
  exact ((faithful_full_criteria (ModuleCat.adj k)).2.2.2.2.2.2 h).1

/-- `ALGD-C1-ADJOINT-26` (命題 26, p.23).
If `F ⊣ G` and `L ⊣ R`, then `LF ⊣ GR`, with
`Hom(LFa, c) ≅ Hom(Fa, Rc) ≅ Hom(a, GRc)`. -/
theorem comp_adjunction {E : Type u₃} [Category.{v₃} E] {L : D ⥤ E} {R : E ⥤ D}
    (adj₁ : F ⊣ G) (adj₂ : L ⊣ R) :
    ∃ adj : F ⋙ L ⊣ R ⋙ G, ∀ (a : C) (e : E) (f : L.obj (F.obj a) ⟶ e),
      adj.homEquiv a e f = adj₁.homEquiv a (R.obj e) (adj₂.homEquiv (F.obj a) e f) :=
  ⟨adj₁.comp adj₂, fun a e f ↦ by rw [Adjunction.comp_homEquiv]; rfl⟩

/-- `ALGD-C1-ADJOINT-27` (命題 27, pp.23–25).
If `F ⊣ G`, then postcomposition gives `F_* ⊣ G_* : C^U → D^U`, with `β_KL(θ) = Gθ ∘ η_K`. -/
theorem postcomp_adjunction (adj : F ⊣ G) (U : Type u₃) [Category.{v₃} U] :
    ∃ adj' : (Functor.whiskeringRight U C D).obj F ⊣ (Functor.whiskeringRight U D C).obj G,
      ∀ (K : U ⥤ C) (L : U ⥤ D) (θ : K ⋙ F ⟶ L) (u : U),
        (adj'.homEquiv K L θ).app u = adj.unit.app (K.obj u) ≫ G.map (θ.app u) :=
  ⟨adj.whiskerRight U, fun K L θ u ↦ by
    rw [Adjunction.homEquiv_unit]
    simp [Adjunction.whiskerRight]⟩

/-- `ALGD-C1-ADJOINT-28` (命題 28, p.25).
If `F ⊣ G`, then precomposition gives `G⁻¹ ⊣ F⁻¹ : U^C → U^D`. -/
theorem precomp_adjunction (adj : F ⊣ G) (U : Type u₃) [Category.{v₃} U] :
    Nonempty ((Functor.whiskeringLeft D C U).obj G ⊣ (Functor.whiskeringLeft C D U).obj F) :=
  ⟨adj.whiskerLeft U⟩

/-- `ALGD-C1-ADJOINT-29` (系 29, p.25).
If `F ⊣ G`, then `(F^op)⁻¹ ⊣ (G^op)⁻¹ : D̂ → Ĉ`, where `(F^op)⁻¹ P = P ∘ F^op`. -/
theorem presheaf_adjunction (adj : F ⊣ G) :
    Nonempty ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj F.op ⊣
      (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ (Type w)).obj G.op) :=
  ⟨adj.op.whiskerLeft (Type w)⟩

/-! ## §3 Idempotent adjunctions -/

/-- The full subcategory `C0 = {c ∈ C : η_c is an isomorphism}`. -/
def unitFixed (adj : F ⊣ G) : ObjectProperty C := fun c ↦ IsIso (adj.unit.app c)

/-- The full subcategory `D0 = {d ∈ D : ε_d is an isomorphism}`. -/
def counitFixed (adj : F ⊣ G) : ObjectProperty D := fun d ↦ IsIso (adj.counit.app d)

/-- `ALGD-C1-ADJOINT-D07` (prose, §3, p.25).
`C0 = unitFixed adj` lies in `C1 = G.essImage` (the objects isomorphic to some `Gd`), and
`D0 = counitFixed adj` lies in `D1 = F.essImage`. -/
theorem unitFixed_le_essImage (adj : F ⊣ G) :
    unitFixed adj ≤ G.essImage ∧ counitFixed adj ≤ F.essImage :=
  ⟨fun c (_ : IsIso _) ↦ adj.mem_essImage_of_unit_isIso c,
    fun d (_ : IsIso _) ↦ adj.mem_essImage_of_counit_isIso d⟩

theorem isIso_right_of_comp_eq_id {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X} [IsIso f]
    (h : f ≫ g = 𝟙 X) : IsIso g :=
  IsIso.of_isIso_fac_left h

theorem isIso_left_of_comp_eq_id {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X} [IsIso g]
    (h : f ≫ g = 𝟙 X) : IsIso f :=
  IsIso.of_isIso_fac_right h

theorem counit_isIso_of_unit_isIso (adj : F ⊣ G) (c : C) (_ : IsIso (adj.unit.app c)) :
    IsIso (adj.counit.app (F.obj c)) :=
  isIso_right_of_comp_eq_id (adj.left_triangle_components c)

theorem unit_isIso_of_counit_isIso (adj : F ⊣ G) (d : D) (_ : IsIso (adj.counit.app d)) :
    IsIso (adj.unit.app (G.obj d)) :=
  isIso_left_of_comp_eq_id (adj.right_triangle_components d)

instance (adj : F ⊣ G) (c : (unitFixed adj).FullSubcategory) : IsIso (adj.unit.app c.obj) :=
  c.property

instance (adj : F ⊣ G) (d : (counitFixed adj).FullSubcategory) : IsIso (adj.counit.app d.obj) :=
  d.property

/-- The isomorphism `η_c : c ≅ GFc` for `c ∈ C0`. -/
noncomputable def unitFixedIso (adj : F ⊣ G) (c : (unitFixed adj).FullSubcategory) :
    c.obj ≅ G.obj (F.obj c.obj) :=
  asIso (adj.unit.app c.obj)

/-- The isomorphism `ε_d : FGd ≅ d` for `d ∈ D0`. -/
noncomputable def counitFixedIso (adj : F ⊣ G) (d : (counitFixed adj).FullSubcategory) :
    F.obj (G.obj d.obj) ≅ d.obj :=
  asIso (adj.counit.app d.obj)

/-- `F` restricted to `C0 → D0`. -/
def unitFixedFunctor (adj : F ⊣ G) :
    (unitFixed adj).FullSubcategory ⥤ (counitFixed adj).FullSubcategory :=
  (counitFixed adj).lift ((unitFixed adj).ι ⋙ F) fun c ↦
    counit_isIso_of_unit_isIso adj c.obj c.property

/-- `G` restricted to `D0 → C0`. -/
def counitFixedFunctor (adj : F ⊣ G) :
    (counitFixed adj).FullSubcategory ⥤ (unitFixed adj).FullSubcategory :=
  (unitFixed adj).lift ((counitFixed adj).ι ⋙ G) fun d ↦
    unit_isIso_of_counit_isIso adj d.obj d.property

/-- The equivalence `C0 ≃ D0` of 定理 30, with `η` and `ε` as unit and counit. -/
noncomputable def fixedPointEquivalence (adj : F ⊣ G) :
    (unitFixed adj).FullSubcategory ≌ (counitFixed adj).FullSubcategory :=
  CategoryTheory.Equivalence.mk (unitFixedFunctor adj) (counitFixedFunctor adj)
    (NatIso.ofComponents (fun c ↦ (unitFixed adj).fullyFaithfulι.preimageIso
        (unitFixedIso adj c))
      fun f ↦ by
        apply (unitFixed adj).ι.map_injective
        exact (adj.unit_naturality f.hom).symm)
    (NatIso.ofComponents (fun d ↦ (counitFixed adj).fullyFaithfulι.preimageIso
        (counitFixedIso adj d))
      fun f ↦ by
        apply (counitFixed adj).ι.map_injective
        exact adj.counit_naturality f.hom)

/-- `ALGD-C1-ADJOINT-30` (定理 30, pp.25–26).
`F ⊣ G` induces an equivalence `C0 ≃ D0` whose functors are the restrictions of `F` and `G`. -/
theorem fixedPoint_equivalence (adj : F ⊣ G) :
    ∃ e : (unitFixed adj).FullSubcategory ≌ (counitFixed adj).FullSubcategory,
      Nonempty (e.functor ⋙ (counitFixed adj).ι ≅ (unitFixed adj).ι ⋙ F) ∧
      Nonempty (e.inverse ⋙ (unitFixed adj).ι ≅ (counitFixed adj).ι ⋙ G) :=
  ⟨fixedPointEquivalence adj, ⟨ObjectProperty.liftCompιIso _ _ _⟩,
    ⟨ObjectProperty.liftCompιIso _ _ _⟩⟩

/-- An adjunction is idempotent if `Fη : F ⇒ FGF` is an isomorphism (condition (1) of 定理 31). -/
def IsIdempotent (adj : F ⊣ G) : Prop := ∀ c, IsIso (F.map (adj.unit.app c))

/-- `ALGD-C1-ADJOINT-31` (定理 31, pp.26–28).
The twelve conditions for `F ⊣ G` to be idempotent are equivalent. Each condition on a whiskered
transformation is stated componentwise: (1) `Fη` iso; (2) `ηG` iso; (3) `FηG` iso;
(4) `GFη = ηGF`; (5) `GFηG = ηGFG`; (6) `C0 = C1`; (7) `Gε` iso; (8) `εF` iso; (9) `GεF` iso;
(10) `FGε = εFG`; (11) `FGεF = εFGF`; (12) `D0 = D1`. -/
theorem idempotent_tfae (adj : F ⊣ G) :
    List.TFAE [
      ∀ c, IsIso (F.map (adj.unit.app c)),
      ∀ d, IsIso (adj.unit.app (G.obj d)),
      ∀ d, IsIso (F.map (adj.unit.app (G.obj d))),
      ∀ c, G.map (F.map (adj.unit.app c)) = adj.unit.app (G.obj (F.obj c)),
      ∀ d, G.map (F.map (adj.unit.app (G.obj d))) = adj.unit.app (G.obj (F.obj (G.obj d))),
      unitFixed adj = G.essImage,
      ∀ d, IsIso (G.map (adj.counit.app d)),
      ∀ c, IsIso (adj.counit.app (F.obj c)),
      ∀ c, IsIso (G.map (adj.counit.app (F.obj c))),
      ∀ d, F.map (G.map (adj.counit.app d)) = adj.counit.app (F.obj (G.obj d)),
      ∀ c, F.map (G.map (adj.counit.app (F.obj c))) = adj.counit.app (F.obj (G.obj (F.obj c))),
      counitFixed adj = F.essImage] := by
  have T1 := adj.left_triangle_components
  have T2 := adj.right_triangle_components
  tfae_have 1 → 8 := fun h c ↦ isIso_right_of_comp_eq_id (T1 c)
  tfae_have 8 → 1 := fun h c ↦ isIso_left_of_comp_eq_id (T1 c)
  tfae_have 8 → 9 := fun h c ↦ inferInstance
  tfae_have 9 → 4 := fun h c ↦ by
    rw [← cancel_mono (G.map (adj.counit.app (F.obj c)))]
    erw [← G.map_comp, T1, G.map_id, T2]
    rfl
  tfae_have 4 → 1 := fun h c ↦ by
    have := adj.counit_naturality (F.map (adj.unit.app c))
    erw [h c, T1] at this
    exact ⟨⟨adj.counit.app (F.obj c), T1 c, this.symm⟩⟩
  tfae_have 2 → 7 := fun h d ↦ isIso_right_of_comp_eq_id (T2 d)
  tfae_have 7 → 2 := fun h d ↦ isIso_left_of_comp_eq_id (T2 d)
  tfae_have 2 → 3 := fun h d ↦ inferInstance
  tfae_have 3 → 10 := fun h d ↦ by
    rw [← cancel_epi (F.map (adj.unit.app (G.obj d)))]
    erw [← F.map_comp, T2, F.map_id, T1]
  tfae_have 10 → 2 := fun h d ↦ by
    have := adj.unit_naturality (G.map (adj.counit.app d))
    erw [h d, T2] at this
    exact ⟨⟨G.map (adj.counit.app d), T2 d, this.symm⟩⟩
  tfae_have 1 → 3 := fun h d ↦ h (G.obj d)
  tfae_have 7 → 9 := fun h c ↦ h (F.obj c)
  tfae_have 4 → 5 := fun h d ↦ h (G.obj d)
  tfae_have 5 → 2 := fun h d ↦ by
    have := adj.unit_naturality (G.map (adj.counit.app d))
    erw [← h d, ← G.map_comp, ← F.map_comp, T2, F.map_id, G.map_id] at this
    exact ⟨⟨G.map (adj.counit.app d), T2 d, this.symm⟩⟩
  tfae_have 10 → 11 := fun h c ↦ h (F.obj c)
  tfae_have 11 → 1 := fun h c ↦ by
    have := adj.counit_naturality (F.map (adj.unit.app c))
    erw [← h c, ← F.map_comp, ← G.map_comp, T1, G.map_id, F.map_id] at this
    exact ⟨⟨adj.counit.app (F.obj c), T1 c, this.symm⟩⟩
  tfae_have 6 → 2 := fun h d ↦ by
    have : unitFixed adj (G.obj d) := h ▸ G.obj_mem_essImage d
    exact this
  tfae_have 2 → 6 := fun h ↦ by
    refine le_antisymm (unitFixed_le_essImage adj).1 fun c ⟨d, ⟨i⟩⟩ ↦ ?_
    have : IsIso (i.hom ≫ adj.unit.app c) := by
      rw [← adj.unit_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left i.hom _
  tfae_have 12 → 8 := fun h c ↦ by
    have : counitFixed adj (F.obj c) := h ▸ F.obj_mem_essImage c
    exact this
  tfae_have 8 → 12 := fun h ↦ by
    refine le_antisymm (unitFixed_le_essImage adj).2 fun d ⟨c, ⟨i⟩⟩ ↦ ?_
    have : IsIso (F.map (G.map i.hom) ≫ adj.counit.app d) := by
      erw [adj.counit_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left (F.map (G.map i.hom)) _
  tfae_finish

/-- The unit at `c` is an isomorphism iff `F` is bijective on `Hom_C(c', c)` for every `c'`. The
right side depends only on `F`, not on the adjunction. -/
theorem unit_isIso_iff_map_bijective (adj : F ⊣ G) (c : C) :
    IsIso (adj.unit.app c) ↔ ∀ c' : C, Function.Bijective (fun p : c' ⟶ c ↦ F.map p) := by
  rw [isIso_iff_yoneda_map_bijective]
  refine forall_congr' fun c' ↦ ?_
  have : (fun p : c' ⟶ c ↦ p ≫ adj.unit.app c) =
      (adj.homEquiv c' (F.obj c)) ∘ (fun p : c' ⟶ c ↦ F.map p) := by
    funext p
    simp [Adjunction.homEquiv_unit]
  exact (Iff.of_eq (congrArg Function.Bijective this)).trans
    ((adj.homEquiv c' (F.obj c)).bijective.of_comp_iff' _)

theorem map_bijective_iff_of_iso {F' : C ⥤ D} (e : F ≅ F') (a b : C) :
    Function.Bijective (fun p : a ⟶ b ↦ F.map p) ↔
      Function.Bijective (fun p : a ⟶ b ↦ F'.map p) := by
  have : (fun p : a ⟶ b ↦ F'.map p) = ((e.app a).homCongr (e.app b)) ∘ fun p ↦ F.map p := by
    funext p
    simp [Iso.homCongr_apply]
  rw [this, ((e.app a).homCongr (e.app b)).bijective.of_comp_iff']

theorem comp_map_bijective_iff {E : Type u₃} [Category.{v₃} E] (L : C ⥤ E) (K : E ⥤ D)
    [K.Full] [K.Faithful] (a b : C) :
    Function.Bijective (fun p : a ⟶ b ↦ (L ⋙ K).map p) ↔
      Function.Bijective (fun p : a ⟶ b ↦ L.map p) :=
  ((Functor.FullyFaithful.ofFullyFaithful K).map_bijective (L.obj a) (L.obj b)).of_comp_iff' _

theorem unit_isIso_of_iso (adj : F ⊣ G) {c c' : C} (i : c ≅ c') (h : IsIso (adj.unit.app c)) :
    IsIso (adj.unit.app c') := by
  have : IsIso (i.hom ≫ adj.unit.app c') := by
    rw [← adj.unit_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left i.hom _

/-- The converse half of 定理 32, for a category `X` in any universe. -/
theorem idempotent_of_factorization (adj : F ⊣ G) {X : Type u₃} [Category.{v₃} X]
    {K₀ : X ⥤ C} {K₁ : X ⥤ D} {L : C ⥤ X} {R : D ⥤ X} [K₀.Full] [K₀.Faithful] [K₁.Full]
    [K₁.Faithful] (adj₁ : L ⊣ K₀) (eF : F ≅ L ⋙ K₁) (eG : G ≅ R ⋙ K₀) :
    IsIdempotent adj := by
  refine (idempotent_tfae adj).out 1 2 |>.2 fun d ↦ ?_
  rw [unit_isIso_iff_map_bijective adj,
    forall_congr' fun c' ↦ (map_bijective_iff_of_iso eF c' (G.obj d)).trans
      (comp_map_bijective_iff L K₁ c' (G.obj d)),
    ← unit_isIso_iff_map_bijective adj₁]
  refine unit_isIso_of_iso adj₁ (eG.app d).symm ?_
  have := (faithful_full_criteria adj₁).2.2.2.2.2.1 ⟨inferInstance, inferInstance⟩
  exact isIso_left_of_comp_eq_id (adj₁.right_triangle_components (R.obj d))

/-- `ALGD-C1-ADJOINT-32` (定理 32, pp.28–29).
`F ⊣ G` is idempotent iff there are a category `X`, fully faithful `K₀ : X → C` and
`K₁ : X → D`, and adjunctions `L ⊣ K₀`, `K₁ ⊣ R` with `F ≅ K₁L` and `G ≅ K₀R`. For `⇒`, `X` is
`D0`, `K₁` is the inclusion, `K₀` is `G` restricted to `D0`, `L` is `F` and `R d = FGd`. -/
theorem idempotent_iff_factorization (adj : F ⊣ G) :
    IsIdempotent adj ↔ ∃ (X : Type u₂) (_ : Category.{v₂} X) (K₀ : X ⥤ C) (K₁ : X ⥤ D)
      (L : C ⥤ X) (R : D ⥤ X), (K₀.Full ∧ K₀.Faithful) ∧ (K₁.Full ∧ K₁.Faithful) ∧
      Nonempty (L ⊣ K₀) ∧ Nonempty (K₁ ⊣ R) ∧ Nonempty (F ≅ L ⋙ K₁) ∧ Nonempty (G ≅ R ⋙ K₀) := by
  constructor
  · intro h
    have h8 : ∀ c, IsIso (adj.counit.app (F.obj c)) := (idempotent_tfae adj).out 1 8 |>.1 h
    have h10 : ∀ d, F.map (G.map (adj.counit.app d)) = adj.counit.app (F.obj (G.obj d)) :=
      (idempotent_tfae adj).out 1 10 |>.1 h
    let P := counitFixed adj
    let L : C ⥤ P.FullSubcategory := P.lift F h8
    let K₀ : P.FullSubcategory ⥤ C := P.ι ⋙ G
    let adj₁ : L ⊣ K₀ := Adjunction.mkOfHomEquiv
      { homEquiv := fun c x ↦
          { toFun := fun g ↦ adj.homEquiv c x.obj g.hom
            invFun := fun g ↦ ObjectProperty.homMk ((adj.homEquiv c x.obj).symm g)
            left_inv := fun g ↦ by ext; simp
            right_inv := fun g ↦ by simp }
        homEquiv_naturality_left_symm := fun f g ↦ by
          ext
          simp [L, Adjunction.homEquiv_naturality_left_symm]
          rfl
        homEquiv_naturality_right := fun f g ↦ by
          simp [K₀, Adjunction.homEquiv_naturality_right] }
    have hK₀ : K₀.Full ∧ K₀.Faithful := by
      refine (faithful_full_criteria adj₁).2.2.2.2.2.2 fun x ↦ ?_
      have : IsIso (P.ι.map (adj₁.counit.app x)) := by
        have e : P.ι.map (adj₁.counit.app x) = adj.counit.app x.obj := by
          rw [← Adjunction.homEquiv_symm_id, ← Adjunction.homEquiv_symm_id]
          simp [adj₁]
          rfl
        rw [e]
        exact x.property
      exact isIso_of_fully_faithful P.ι _
    let c : D → P.FullSubcategory := fun d ↦ ⟨F.obj (G.obj d), h8 (G.obj d)⟩
    have univ : ∀ d (x : P.FullSubcategory) (f : P.ι.obj x ⟶ d),
        ∃! g : x ⟶ c d, P.ι.map g ≫ adj.counit.app d = f := by
      intro d x f
      have : IsIso (adj.counit.app x.obj) := x.property
      refine ⟨ObjectProperty.homMk (inv (adj.counit.app x.obj) ≫ F.map (G.map f)), ?_,
        fun g hg ↦ ?_⟩
      · simp
      · ext
        simp only [ObjectProperty.ι_map] at hg
        rw [ObjectProperty.homMk_hom, IsIso.eq_inv_comp, ← hg, G.map_comp, F.map_comp, h10]
        exact (adj.counit_naturality g.hom).symm
    let R := rightAdjointOfUniversalArrows P.ι c (fun d ↦ adj.counit.app d) univ
    let adj₂ : P.ι ⊣ R := adjunctionOfUniversalArrowsFrom P.ι c (fun d ↦ adj.counit.app d) univ
    have hR : ∀ {d d' : D} (q : d ⟶ d'), (R.map q).hom ≫ adj.counit.app d' =
        adj.counit.app d ≫ q := fun {d d'} q ↦ by
      have := adj₂.counit_naturality q
      rw [adjunctionOfUniversalArrowsFrom_counit_app,
        adjunctionOfUniversalArrowsFrom_counit_app] at this
      exact this
    have h7 : ∀ d, IsIso (G.map (adj.counit.app d)) := (idempotent_tfae adj).out 1 7 |>.1 h
    let eG : G ≅ R ⋙ K₀ := NatIso.ofComponents
      (fun d ↦ (asIso (G.map (adj.counit.app d))).symm) fun {d d'} q ↦ by
        have h := congrArg G.map (hR q)
        erw [G.map_comp, G.map_comp] at h
        simp only [Iso.symm_hom, asIso_inv, Functor.comp_map]
        rw [← cancel_epi (G.map (adj.counit.app d))]
        erw [IsIso.hom_inv_id_assoc, ← reassoc_of% h, IsIso.hom_inv_id, Category.comp_id]
        rfl
    exact ⟨P.FullSubcategory, inferInstance, K₀, P.ι, L, R, hK₀, ⟨inferInstance, inferInstance⟩,
      ⟨adj₁⟩, ⟨adj₂⟩, ⟨(P.liftCompιIso F h8).symm⟩, ⟨eG⟩⟩
  · rintro ⟨X, _, K₀, K₁, L, R, ⟨_, _⟩, ⟨_, _⟩, ⟨adj₁⟩, -, ⟨eF⟩, ⟨eG⟩⟩
    exact idempotent_of_factorization adj adj₁ eF eG

/-- `ALGD-C1-ADJOINT-33` (系 33, p.29).
If `F ⊣ G` is idempotent, the inclusion `C0 → C` has a left adjoint, sending `c` to `GFc`. -/
theorem unitFixed_reflective (adj : F ⊣ G) (h : IsIdempotent adj) :
    (unitFixed adj).ι.IsRightAdjoint := by
  have h2 : ∀ d, IsIso (adj.unit.app (G.obj d)) := (idempotent_tfae adj).out 1 2 |>.1 h
  have h4 : ∀ c, G.map (F.map (adj.unit.app c)) = adj.unit.app (G.obj (F.obj c)) :=
    (idempotent_tfae adj).out 1 4 |>.1 h
  let d : C → (unitFixed adj).FullSubcategory := fun c ↦ ⟨G.obj (F.obj c), h2 (F.obj c)⟩
  have univ : ∀ c (e : (unitFixed adj).FullSubcategory) (g : c ⟶ (unitFixed adj).ι.obj e),
      ∃! k : d c ⟶ e, adj.unit.app c ≫ (unitFixed adj).ι.map k = g := by
    intro c e g
    have : IsIso (adj.unit.app e.obj) := e.property
    refine ⟨ObjectProperty.homMk (G.map (F.map g) ≫ inv (adj.unit.app e.obj)), ?_,
      fun k hk ↦ ?_⟩
    · simp [Adjunction.unit_naturality_assoc]
    · ext
      simp only [ObjectProperty.ι_map] at hk
      rw [ObjectProperty.homMk_hom, IsIso.eq_comp_inv]
      erw [← adj.unit_naturality k.hom, ← h4 c, ← G.map_comp, ← F.map_comp, hk]
  exact (adjunctionOfUniversalArrows (unitFixed adj).ι d (fun c ↦ adj.unit.app c)
    univ).isRightAdjoint

/-- `ALGD-C1-ADJOINT-34` (系 34, p.29).
If `F ⊣ G` is idempotent, then in the notation of 定理 32, `X ≃ C0`: `K₁ ⊣ R` with `K₁` fully
faithful makes `R` essentially surjective, so `K₀` corestricts to a fully faithful, essentially
surjective functor `X → C0`. Only `K₀`, `K₁`, `K₁ ⊣ R` and `G ≅ K₀R` are needed. -/
theorem factorization_equivalence (adj : F ⊣ G) (h : IsIdempotent adj) {X : Type u₃}
    [Category.{v₃} X] {K₀ : X ⥤ C} {K₁ : X ⥤ D} {R : D ⥤ X} [K₀.Full] [K₀.Faithful]
    [K₁.Full] [K₁.Faithful] (adj₂ : K₁ ⊣ R) (eG : G ≅ R ⋙ K₀) :
    Nonempty (X ≌ (unitFixed adj).FullSubcategory) := by
  have h2 : ∀ d, IsIso (adj.unit.app (G.obj d)) := (idempotent_tfae adj).out 1 2 |>.1 h
  have : R.EssSurj := ((unit_counit_iso_aux adj₂).1
    ((faithful_full_criteria adj₂).2.2.1.1 ⟨inferInstance, inferInstance⟩)).2.2
  have hK : ∀ x, unitFixed adj (K₀.obj x) := fun x ↦
    unit_isIso_of_iso adj ((eG.app (R.objPreimage x)).trans
      (K₀.mapIso (R.objObjPreimageIso x))) (h2 _)
  let K := (unitFixed adj).lift K₀ hK
  have : K.EssSurj := ⟨fun c ↦ ⟨R.obj (F.obj c.obj), ⟨(unitFixed adj).fullyFaithfulι.preimageIso
    ((eG.app (F.obj c.obj)).symm ≪≫ (unitFixedIso adj c).symm)⟩⟩⟩
  have : K.IsEquivalence := { }
  exact ⟨K.asEquivalence⟩

/-! ## §4 Cartesian closed categories

Finite products are a chosen `CartesianMonoidalCategory` structure, and the source's `− × a` is
`tensorRight a` (`b ↦ b ⊗ a`). mathlib's `MonoidalClosed` asks for right adjoints of
`tensorLeft a` instead; `isCartesianClosed_iff_monoidalClosed` bridges the two through the
braiding. -/

section CCC

open MonoidalCategory CartesianMonoidalCategory

variable [CartesianMonoidalCategory C]

/-- `ALGD-C1-ADJOINT-D08` (定義, §4, p.30).
`⟨e, ev⟩` is an exponential object `b^a`: a universal arrow from `− × a` to `b`, i.e. every
`f : x × a → b` is `ev ∘ (g × id_a)` for a unique `g : x → e`. -/
def IsExponential (a b e : C) (ev : e ⊗ a ⟶ b) : Prop :=
  ∀ (x : C) (f : x ⊗ a ⟶ b), ∃! g : x ⟶ e, g ▷ a ≫ ev = f

/-- `ALGD-C1-ADJOINT-35` (例 35, p.30).
In `Set`, `b^a = Hom_Set(a, b)` with `ev(f, x) = f(x)`. -/
theorem types_exponential (a b : Type u) :
    IsExponential a b (a → b) (TypeCat.ofHom fun p : (a → b) × a ↦ p.1 p.2) := by
  intro x f
  refine ⟨TypeCat.ofHom fun y z ↦ f (y, z), ?_, fun g hg ↦ ?_⟩
  · ext ⟨y, z⟩
    rfl
  · beta_reduce at hg
    ext y z
    exact ConcreteCategory.congr_hom hg ((y, z) : x × a)

/-- `ALGD-C1-ADJOINT-36` (命題 36, p.30).
If every `b^a` exists, then `b ↦ b^a` is a functor `(−)^a` with `− × a ⊣ (−)^a`, whose counit is
`ev` and whose inverse bijection `Hom(b, c^a) → Hom(b × a, c)` is `g ↦ ev ∘ (g × id_a)`. -/
theorem exponential_adjunction (a : C) (e : C → C) (ev : ∀ b, e b ⊗ a ⟶ b)
    (h : ∀ b, IsExponential a b (e b) (ev b)) :
    (∀ b, (rightAdjointOfUniversalArrows (tensorRight a) e ev h).obj b = e b) ∧
    (∀ b, (adjunctionOfUniversalArrowsFrom (tensorRight a) e ev h).counit.app b = ev b) ∧
    (∀ (b c : C) (g : b ⟶ e c),
      ((adjunctionOfUniversalArrowsFrom (tensorRight a) e ev h).homEquiv b c).symm g =
        g ▷ a ≫ ev c) :=
  ⟨fun _ ↦ rfl, adjunctionOfUniversalArrowsFrom_counit_app _ _ _ h, fun b c g ↦ by
    erw [Adjunction.homEquiv_counit, adjunctionOfUniversalArrowsFrom_counit_app]
    rfl⟩

variable (C) in
/-- `ALGD-C1-ADJOINT-D09` (定義, §4, p.30).
A cartesian closed category: `C` has finite products (here a chosen `CartesianMonoidalCategory`)
and every `− × a` has a right adjoint. -/
def IsCartesianClosed : Prop := ∀ a : C, (tensorRight a).IsLeftAdjoint

theorem tensorLeft_isLeftAdjoint (hC : IsCartesianClosed C) (x : C) :
    (tensorLeft x).IsLeftAdjoint := by
  let := BraidedCategory.ofCartesianMonoidalCategory (C := C)
  have := hC x
  exact Functor.isLeftAdjoint_of_iso (BraidedCategory.tensorLeftIsoTensorRight x).symm

/-- The source's cartesian closed categories are mathlib's: `MonoidalClosed` uses `tensorLeft`,
which is isomorphic to `tensorRight` through the braiding. -/
theorem isCartesianClosed_iff_monoidalClosed :
    IsCartesianClosed C ↔ Nonempty (MonoidalClosed C) := by
  let := BraidedCategory.ofCartesianMonoidalCategory (C := C)
  constructor
  · intro hC
    have := tensorLeft_isLeftAdjoint hC
    exact ⟨{ closed := fun x ↦ ⟨_, Adjunction.ofIsLeftAdjoint (tensorLeft x)⟩ }⟩
  · rintro ⟨_⟩ a
    have : (tensorLeft a).IsLeftAdjoint := (ihom.adjunction a).isLeftAdjoint
    exact Functor.isLeftAdjoint_of_iso (BraidedCategory.tensorLeftIsoTensorRight a)

theorem isExponential_counit {a : C} {Ga : C ⥤ C} (adj : tensorRight a ⊣ Ga) (b : C) :
    IsExponential a b (Ga.obj b) (adj.counit.app b) :=
  (counit_dual.{0, 0} adj).1.1 b

/-- `ALGD-C1-ADJOINT-R07` (※ box, p.30).
If `G_a` is right adjoint to `− × a`, then `⟨G_a b, ε_b⟩` are exponential objects (定理 10), and
`G_a ≅ (−)^a`, the functor built from them in 命題 36. -/
theorem exponential_of_rightAdjoint {a : C} {Ga : C ⥤ C} (adj : tensorRight a ⊣ Ga) :
    (∀ b, IsExponential a b (Ga.obj b) (adj.counit.app b)) ∧
    Nonempty (Ga ≅ rightAdjointOfUniversalArrows (tensorRight a) Ga.obj
      (fun b ↦ adj.counit.app b) (isExponential_counit adj)) :=
  ⟨isExponential_counit adj,
    ⟨adj.rightAdjointUniq (adjunctionOfUniversalArrowsFrom _ _ _ (isExponential_counit adj))⟩⟩

/-- `ALGD-C1-ADJOINT-37` (命題 37, p.31).
For `− × a ⊣ (−)^a`: `− × a` preserves colimits and `(−)^a` preserves limits. In particular
`(b ⊔ c) × a` is a coproduct of `b × a` and `c × a`, `(b × c)^a ≅ b^a × c^a`, `0 × a` is initial
and `1^a` is terminal. -/
theorem exponential_preserves {a : C} {E : C ⥤ C} (adj : tensorRight a ⊣ E) :
    PreservesColimitsOfSize.{w', w} (tensorRight a) ∧ PreservesLimitsOfSize.{w', w} E ∧
    (∀ (b c : C) [HasBinaryCoproduct b c],
      Nonempty (IsColimit (BinaryCofan.mk (coprod.inl ▷ a : b ⊗ a ⟶ (b ⨿ c) ⊗ a)
        (coprod.inr ▷ a)))) ∧
    (∀ b c : C, Nonempty (E.obj (b ⊗ c) ≅ E.obj b ⊗ E.obj c)) ∧
    (∀ z : C, IsInitial z → Nonempty (IsInitial (z ⊗ a))) ∧
    Nonempty (IsTerminal (E.obj (𝟙_ C))) := by
  have := adj.leftAdjoint_preservesColimits.{0, 0}
  have := adj.rightAdjoint_preservesLimits.{0, 0}
  refine ⟨adj.leftAdjoint_preservesColimits, adj.rightAdjoint_preservesLimits,
    fun b c _ ↦ ⟨(isColimitMapCoconeBinaryCofanEquiv (tensorRight a) _ _)
      (isColimitOfPreserves (tensorRight a) (coprodIsCoprod b c))⟩, fun b c ↦ ?_,
    fun z hz ↦ ⟨hz.isInitialObj (tensorRight a)⟩, ⟨isTerminalTensorUnit.isTerminalObj E⟩⟩
  have h := (isLimitMapConeBinaryFanEquiv E (fst b c) (snd b c))
    (isLimitOfPreserves E (tensorProductIsBinaryProduct b c))
  exact ⟨h.conePointUniqueUpToIso (tensorProductIsBinaryProduct (E.obj b) (E.obj c))⟩

/-- `ALGD-C1-ADJOINT-38` (命題 38, p.31).
`(a^b)^c ≅ a^{b×c}`: `(x × c) × b ≅ x × (b × c)` naturally in `x`, so the composite adjunction
`(− × c) × b ⊣ ((−)^b)^c` and `− × (b × c) ⊣ (−)^{b×c}` have isomorphic right adjoints. -/
theorem exponential_exponential {b c : C} {Eb Ec Ebc : C ⥤ C} (adjb : tensorRight b ⊣ Eb)
    (adjc : tensorRight c ⊣ Ec) (adjbc : tensorRight (b ⊗ c) ⊣ Ebc) (a : C) :
    Nonempty (Ec.obj (Eb.obj a) ≅ Ebc.obj a) := by
  let := BraidedCategory.ofCartesianMonoidalCategory (C := C)
  let i : tensorRight c ⋙ tensorRight b ≅ tensorRight (b ⊗ c) :=
    NatIso.ofComponents (fun x ↦ α_ x c b ≪≫ whiskerLeftIso x (β_ c b)) fun f ↦ by
      change (f ▷ c) ▷ b ≫ (α_ _ c b).hom ≫ _ ◁ (β_ c b).hom =
        ((α_ _ c b).hom ≫ _ ◁ (β_ c b).hom) ≫ f ▷ (b ⊗ c)
      rw [associator_naturality_left_assoc, Category.assoc, ← whisker_exchange]
  exact ⟨((adjbc.rightAdjointUniq ((adjc.comp adjb).ofNatIsoLeft i)).app a).symm⟩

/-- `ALGD-C1-ADJOINT-39` (命題 39, p.31).
In a cartesian closed category, `a^b × a^c ≅ a^{b⊔c}`: both represent
`Hom_C(− × (b ⊔ c), a) ≅ Hom_C(− × b, a) × Hom_C(− × c, a)`. -/
theorem exponential_coprod (hC : IsCartesianClosed C) {b c : C} [HasBinaryCoproduct b c]
    {Eb Ec Ebc : C ⥤ C} (adjb : tensorRight b ⊣ Eb) (adjc : tensorRight c ⊣ Ec)
    (adjbc : tensorRight (b ⨿ c) ⊣ Ebc) (a : C) :
    Nonempty (Eb.obj a ⊗ Ec.obj a ≅ Ebc.obj a) := by
  have := tensorLeft_isLeftAdjoint hC
  have hx : ∀ x : C, IsColimit (BinaryCofan.mk (x ◁ coprod.inl : x ⊗ b ⟶ x ⊗ (b ⨿ c))
      (x ◁ coprod.inr)) := fun x ↦ by
    have := (Adjunction.ofIsLeftAdjoint (tensorLeft x)).leftAdjoint_preservesColimits.{0, 0}
    exact (isColimitMapCoconeBinaryCofanEquiv (tensorLeft x) _ _)
      (isColimitOfPreserves (tensorLeft x) (coprodIsCoprod b c))
  let d : ∀ x : C, (x ⟶ Eb.obj a ⊗ Ec.obj a) → (x ⊗ (b ⨿ c) ⟶ a) := fun x g ↦
    (BinaryCofan.IsColimit.desc' (hx x) ((adjb.homEquiv x a).symm (g ≫ fst _ _))
      ((adjc.homEquiv x a).symm (g ≫ snd _ _))).1
  have d_inl : ∀ x g, x ◁ coprod.inl ≫ d x g = (adjb.homEquiv x a).symm (g ≫ fst _ _) :=
    fun x g ↦ (BinaryCofan.IsColimit.desc' (hx x) _ _).2.1
  have d_inr : ∀ x g, x ◁ coprod.inr ≫ d x g = (adjc.homEquiv x a).symm (g ≫ snd _ _) :=
    fun x g ↦ (BinaryCofan.IsColimit.desc' (hx x) _ _).2.2
  let r : ((tensorRight (b ⨿ c)).op ⋙ yoneda.obj a).RepresentableBy (Eb.obj a ⊗ Ec.obj a) :=
    { homEquiv := fun {x} ↦
        { toFun := d x
          invFun := fun h ↦ lift (adjb.homEquiv x a (x ◁ coprod.inl ≫ h))
            (adjc.homEquiv x a (x ◁ coprod.inr ≫ h))
          left_inv := fun g ↦ by
            refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
            · rw [lift_fst, d_inl, Equiv.apply_symm_apply]
            · rw [lift_snd, d_inr, Equiv.apply_symm_apply]
          right_inv := fun h ↦ by
            refine BinaryCofan.IsColimit.hom_ext (hx x) ?_ ?_
            · change x ◁ coprod.inl ≫ d x _ = x ◁ coprod.inl ≫ h
              rw [d_inl, lift_fst, Equiv.symm_apply_apply]
            · change x ◁ coprod.inr ≫ d x _ = x ◁ coprod.inr ≫ h
              rw [d_inr, lift_snd, Equiv.symm_apply_apply] }
      homEquiv_comp := fun {x' x} f g ↦ by
        change d x' (f ≫ g) = f ▷ (b ⨿ c) ≫ d x g
        refine BinaryCofan.IsColimit.hom_ext (hx x') ?_ ?_
        · change x' ◁ coprod.inl ≫ d x' (f ≫ g) = x' ◁ coprod.inl ≫ f ▷ (b ⨿ c) ≫ d x g
          rw [d_inl, whisker_exchange_assoc, d_inl, Category.assoc]
          exact adjb.homEquiv_naturality_left_symm f (g ≫ fst _ _)
        · change x' ◁ coprod.inr ≫ d x' (f ≫ g) = x' ◁ coprod.inr ≫ f ▷ (b ⨿ c) ≫ d x g
          rw [d_inr, whisker_exchange_assoc, d_inr, Category.assoc]
          exact adjc.homEquiv_naturality_left_symm f (g ≫ snd _ _) }
  exact ⟨r.uniqueUpToIso (adjbc.representableBy a)⟩

/-- `ALGD-C1-ADJOINT-40` (命題 40, p.31).
In a cartesian closed category, `a^0` is terminal (`a^0 ≅ 1`) for an initial object `0`, and
`a^1 ≅ a` for the terminal object `1 = 𝟙_ C`. -/
theorem exponential_initial_unit (hC : IsCartesianClosed C) {z : C} (hz : IsInitial z)
    {E₀ E₁ : C ⥤ C} (adj₀ : tensorRight z ⊣ E₀) (adj₁ : tensorRight (𝟙_ C) ⊣ E₁) (a : C) :
    Nonempty (IsTerminal (E₀.obj a)) ∧ Nonempty (E₁.obj a ≅ a) := by
  refine ⟨⟨?_⟩, ?_⟩
  · have := tensorLeft_isLeftAdjoint hC
    have hinit : ∀ x : C, IsInitial (x ⊗ z) := fun x ↦ by
      have := (Adjunction.ofIsLeftAdjoint (tensorLeft x)).leftAdjoint_preservesColimits.{0, 0}
      exact hz.isInitialObj (tensorLeft x)
    exact IsTerminal.ofUniqueHom (fun x ↦ adj₀.homEquiv x a ((hinit x).to a)) fun x m ↦ by
      rw [← Equiv.symm_apply_eq]
      exact (hinit x).hom_ext _ _
  · let i : tensorRight (𝟙_ C) ≅ 𝟭 C := NatIso.ofComponents (fun x ↦ ρ_ x) fun f ↦ by simp
    exact ⟨(adj₁.ofNatIsoLeft i).rightAdjointUniq Adjunction.id |>.app a⟩

end CCC

section Parametrized

variable {X : Type u₃} [Category.{v₃} X]

/-- The functor `G : X^op × D → C` of 定理 41, curried with the parameter first:
`G(x, −) = G_x`, and `G_k : G_{x'} ⇒ G_x` is the mate (`conjugateEquiv`) of `F(−, k)`. -/
noncomputable def parametrizedRightAdjoint (F : X ⥤ C ⥤ D) (G : X → D ⥤ C)
    (adj : ∀ x, F.obj x ⊣ G x) : Xᵒᵖ ⥤ D ⥤ C where
  obj x := G x.unop
  map {x x'} k := conjugateEquiv (adj x.unop) (adj x'.unop) (F.map k.unop)
  map_id x := by
    rw [unop_id, F.map_id, conjugateEquiv_id]
  map_comp {x y z} k l := by
    rw [unop_comp, F.map_comp, ← conjugateEquiv_comp]

/-- `ALGD-C1-ADJOINT-41` (定理 41, pp.32–36).
Let `F : C × X → D` (curried as `X ⥤ C ⥤ D`) with right adjoints `G_x` of `F(−, x)`. Then
`G := parametrizedRightAdjoint F G adj` satisfies (1) `G(x, −) = G_x` and (2) the bijections
`φ_cxd` of `F(−, x) ⊣ G_x` are natural in `x`; and any family `β_k : G_{x'} ⇒ G_x` with (2) is
the action of `G` on morphisms, so `G` is unique. -/
theorem parametrized_adjunction (F : X ⥤ C ⥤ D) (G : X → D ⥤ C) (adj : ∀ x, F.obj x ⊣ G x) :
    (∀ x, (parametrizedRightAdjoint F G adj).obj (op x) = G x) ∧
    (∀ {x x' : X} (k : x ⟶ x') (c : C) (d : D) (f : (F.obj x').obj c ⟶ d),
      (adj x).homEquiv c d ((F.map k).app c ≫ f) =
        (adj x').homEquiv c d f ≫ ((parametrizedRightAdjoint F G adj).map k.op).app d) ∧
    (∀ β : ∀ {x x' : X}, (x ⟶ x') → (G x' ⟶ G x),
      (∀ {x x' : X} (k : x ⟶ x') (c : C) (d : D) (f : (F.obj x').obj c ⟶ d),
        (adj x).homEquiv c d ((F.map k).app c ≫ f) = (adj x').homEquiv c d f ≫ (β k).app d) →
      ∀ {x x' : X} (k : x ⟶ x'), β k = (parametrizedRightAdjoint F G adj).map k.op) := by
  have nat : ∀ {x x' : X} (k : x ⟶ x') (c : C) (d : D) (f : (F.obj x').obj c ⟶ d),
      (adj x).homEquiv c d ((F.map k).app c ≫ f) =
        (adj x').homEquiv c d f ≫ ((parametrizedRightAdjoint F G adj).map k.op).app d := by
    intro x x' k c d f
    change _ = _ ≫ (conjugateEquiv (adj x') (adj x) (F.map k)).app d
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
      ((conjugateEquiv (adj x') (adj x)) (F.map k)).naturality, ← Category.assoc,
      unit_conjugateEquiv, Category.assoc, ← Functor.map_comp]
  refine ⟨fun _ ↦ rfl, nat, fun β hβ x x' k ↦ ?_⟩
  ext d
  have h1 := hβ k ((G x').obj d) d ((adj x').counit.app d)
  have h2 := nat k ((G x').obj d) d ((adj x').counit.app d)
  have e : (adj x').homEquiv _ d ((adj x').counit.app d) = 𝟙 _ := by
    rw [← Adjunction.homEquiv_symm_id, Equiv.apply_symm_apply]
  rw [e, Category.id_comp] at h1
  rw [e] at h2
  exact h1.symm.trans (h2.trans (Category.id_comp _))

/-- `ALGD-C1-ADJOINT-42` (系 42, p.36).
For `p : c → c'`, `q : d' → d`, `f : F(c, x) → d`, `g : F(c', x') → d'` and `k : x → x'`:
`f = q ∘ g ∘ F(p, k)` iff `f̃ = G(k, q) ∘ g̃ ∘ p`, where `G(k, q) = G_k(d) ∘ G_{x'}(q)`. -/
theorem parametrized_square_iff (F : X ⥤ C ⥤ D) (G : X → D ⥤ C) (adj : ∀ x, F.obj x ⊣ G x)
    {c c' : C} {d d' : D} {x x' : X} (p : c ⟶ c') (q : d' ⟶ d) (k : x ⟶ x')
    (f : (F.obj x).obj c ⟶ d) (g : (F.obj x').obj c' ⟶ d') :
    f = (F.map k).app c ≫ (F.obj x').map p ≫ g ≫ q ↔
      (adj x).homEquiv c d f = p ≫ (adj x').homEquiv c' d' g ≫
        (G x').map q ≫ ((parametrizedRightAdjoint F G adj).map k.op).app d := by
  have key : (adj x).homEquiv c d ((F.map k).app c ≫ (F.obj x').map p ≫ g ≫ q) =
      p ≫ (adj x').homEquiv c' d' g ≫ (G x').map q ≫
        ((parametrizedRightAdjoint F G adj).map k.op).app d := by
    rw [(parametrized_adjunction F G adj).2.1, (adj x').homEquiv_naturality_left,
      (adj x').homEquiv_naturality_right]
    exact (Category.assoc _ _ _).trans (congrArg (p ≫ ·) (Category.assoc _ _ _))
  rw [← key, Equiv.apply_eq_iff_eq]

end Parametrized

section CCC2

open MonoidalCategory

variable [CartesianMonoidalCategory C]

/-- `ALGD-C1-ADJOINT-43` (例 43, p.36).
In a cartesian closed category with chosen right adjoints `− × a ⊣ (−)^a`, `⟨a, b⟩ ↦ b^a` is a
functor `C^op × C → C` (定理 41 for `F(b, a) = b × a`), and `Hom(b × a, c) ≅ Hom(b, c^a)` is
natural in `a` as well as in `b` and `c`. -/
theorem exponential_bifunctor (E : C → C ⥤ C) (adj : ∀ a, tensorRight a ⊣ E a) :
    (∀ a, (parametrizedRightAdjoint (tensoringRight C) E adj).obj (op a) = E a) ∧
    ∀ {a a' : C} (k : a ⟶ a') (b c : C) (f : b ⊗ a' ⟶ c),
      (adj a).homEquiv b c (b ◁ k ≫ f) =
        (adj a').homEquiv b c f ≫
          ((parametrizedRightAdjoint (tensoringRight C) E adj).map k.op).app c :=
  ⟨fun _ ↦ rfl, fun k b c f ↦ (parametrized_adjunction _ _ adj).2.1 k b c f⟩

end CCC2

open MonoidalCategory in
/-- `ALGD-C1-ADJOINT-44` (例 44, p.36).
`Ab` (with products `A × B`) is not cartesian closed: `− × ℤ` would preserve the initial object,
but `0 × ℤ ≅ ℤ`. Instead `Ab`, as `ℤ-Mod`, is monoidal closed for the tensor product, with
`Hom(A ⊗ B, C) ≅ Hom(B, Hom(A, C))`. -/
theorem ab_not_cartesianClosed :
    ¬ @IsCartesianClosed AddCommGrpCat.{u} _ AddCommGrpCat.cartesianMonoidalCategory ∧
    ∀ A : ModuleCat.{0} ℤ, Nonempty (tensorLeft A ⊣ ihom A) := by
  refine ⟨fun hC ↦ ?_, fun A ↦ ⟨ihom.adjunction A⟩⟩
  let := AddCommGrpCat.cartesianMonoidalCategory.{u}
  let A := AddCommGrpCat.of (ULift.{u} ℤ)
  have := hC A
  have := (Adjunction.ofIsLeftAdjoint (tensorRight A)).leftAdjoint_preservesColimits.{0, 0}
  have hZ : IsInitial (AddCommGrpCat.of.{u} PUnit) :=
    (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of PUnit)).isInitial
  have h := hZ.isInitialObj (tensorRight A)
  have h1 := ConcreteCategory.congr_hom (h.hom_ext (𝟙 _) 0) ((PUnit.unit, ⟨1⟩) : PUnit × ULift ℤ)
  have h2 : ((PUnit.unit, ⟨1⟩) : PUnit × ULift.{u} ℤ) = 0 := h1
  exact one_ne_zero (congrArg (fun p : PUnit × ULift ℤ ↦ p.2.down) h2)

/-! ## §5 Examples -/

/-- `ALGD-C1-ADJOINT-45` (例 45, §5, p.37).
The free group functor is left adjoint to the forgetful functor `U : Grp → Set`. -/
theorem free_group : Nonempty (GrpCat.free.{u} ⊣ forget GrpCat.{u}) :=
  ⟨GrpCat.adj⟩

/-- `ALGD-C1-ADJOINT-46` (例 46, p.37).
`Ab` is a full subcategory of `Grp`, and abelianization `G ↦ G/[G, G]` is left adjoint to the
inclusion. mathlib's `Ab` here is the multiplicative `CommGrpCat`. -/
theorem abelianization :
    (forget₂ CommGrpCat.{u} GrpCat.{u}).Full ∧ (forget₂ CommGrpCat.{u} GrpCat.{u}).Faithful ∧
    Nonempty (GrpCat.abelianize.{u} ⊣ forget₂ CommGrpCat.{u} GrpCat.{u}) :=
  ⟨inferInstance, inferInstance, ⟨GrpCat.abelianizeAdj⟩⟩

/-- `ALGD-C1-ADJOINT-47` (例 47, p.37).
For a commutative ring `R` and the forgetful functor `U : R-Mod → Ab`, `F(A) = R ⊗_ℤ A` and
`G(A) = Hom_ℤ(R, A)` satisfy `F ⊣ U ⊣ G`. Here `Ab` is `ℤ-Mod`, `U` is restriction of scalars
along `ℤ → R`, and `F`, `G` are extension and coextension of scalars. -/
theorem module_forget (R : Type u) [CommRing R] :
    Nonempty (ModuleCat.extendScalars.{0, u, u} (algebraMap ℤ R) ⊣
      ModuleCat.restrictScalars.{u} (algebraMap ℤ R)) ∧
    Nonempty (ModuleCat.restrictScalars.{u} (algebraMap ℤ R) ⊣
      ModuleCat.coextendScalars.{0, u, u} (algebraMap ℤ R)) :=
  ⟨⟨ModuleCat.extendRestrictScalarsAdj _⟩, ⟨ModuleCat.restrictCoextendScalarsAdj _⟩⟩

/-- `ALGD-C1-ADJOINT-48` (例 48, p.37).
For the forgetful functor `U : Top → Set`, the discrete and indiscrete space functors satisfy
`F ⊣ U ⊣ G`. -/
theorem top_adjoint_triple :
    Nonempty (TopCat.discrete.{u} ⊣ forget TopCat.{u}) ∧
    Nonempty (forget TopCat.{u} ⊣ TopCat.trivial.{u}) :=
  ⟨⟨TopCat.adj₁⟩, ⟨TopCat.adj₂⟩⟩

/-- The forgetful functor `U : Ring → Monoid` to the multiplicative monoid. -/
def ringToMon : RingCat.{u} ⥤ MonCat.{u} :=
  forget₂ RingCat SemiRingCat ⋙ forget₂ SemiRingCat MonCat

/-- The inclusion `M → ℤ[M]` is a universal arrow from `M` to `U : Ring → Monoid`. -/
theorem monoidAlgebra_universal (M : MonCat.{u}) (A : RingCat.{u}) (g : M ⟶ ringToMon.obj A) :
    ∃! h : RingCat.of (MonoidAlgebra ℤ M) ⟶ A,
      MonCat.ofHom (MonoidAlgebra.of ℤ M) ≫ ringToMon.map h = g := by
  refine ⟨RingCat.ofHom (MonoidAlgebra.lift ℤ A M g.hom).toRingHom, ?_, fun h hh ↦ ?_⟩
  · ext m
    exact MonoidAlgebra.lift_of (A := A) g.hom m
  · apply RingCat.hom_ext
    have : h.hom.toIntAlgHom = MonoidAlgebra.lift ℤ A M g.hom := by
      apply MonoidAlgebra.algHom_ext
      · intro m
        have e1 : h.hom (MonoidAlgebra.single m 1) = g m := ConcreteCategory.congr_hom hh m
        have e2 := MonoidAlgebra.lift_of (R := ℤ) (A := A) g.hom m
        rw [MonoidAlgebra.of_apply] at e2
        exact e1.trans e2.symm
      · ext
    exact congrArg AlgHom.toRingHom this

/-- `ALGD-C1-ADJOINT-49` (例 49, p.37).
The monoid ring functor `M ↦ ℤ[M]` is left adjoint to `U : Ring → Monoid` (rings need not be
commutative). -/
theorem monoid_ring :
    ∃ (L : MonCat.{u} ⥤ RingCat.{u}) (_ : L ⊣ ringToMon),
      ∀ M, L.obj M = RingCat.of (MonoidAlgebra ℤ M) :=
  ⟨leftAdjointOfUniversalArrows ringToMon (fun M ↦ RingCat.of (MonoidAlgebra ℤ M))
    (fun M ↦ MonCat.ofHom (MonoidAlgebra.of ℤ M)) monoidAlgebra_universal,
    adjunctionOfUniversalArrows _ _ _ _, fun _ ↦ rfl⟩

namespace Ex50

/-- A pointed commutative ring `⟨A, a⟩`. -/
structure PointedRing : Type (u + 1) where
  /-- The ring. -/
  ring : CommRingCat.{u}
  /-- The base point. -/
  point : ring

/-- A ring homomorphism preserving the base points. -/
@[ext]
structure Hom (A B : PointedRing.{u}) where
  /-- The underlying ring homomorphism. -/
  hom : A.ring ⟶ B.ring
  map_point : hom A.point = B.point

instance : Category PointedRing.{u} where
  Hom := Hom
  id A := ⟨𝟙 _, rfl⟩
  comp p q := ⟨p.hom ≫ q.hom, by simp [p.map_point, q.map_point]⟩

@[ext]
theorem hom_ext {A B : PointedRing.{u}} {p q : A ⟶ B} (h : p.hom = q.hom) : p = q :=
  Hom.ext h

/-- The forgetful functor `U : Ring_∗ → Ring`. -/
def forget : PointedRing.{u} ⥤ CommRingCat.{u} where
  obj A := A.ring
  map p := p.hom

/-- `F(R) = ⟨R[x], x⟩`. -/
noncomputable def polynomial (R : CommRingCat.{u}) : PointedRing.{u} :=
  ⟨CommRingCat.of (Polynomial R), Polynomial.X⟩

theorem polynomial_universal (R : CommRingCat.{u}) (B : PointedRing.{u})
    (g : R ⟶ forget.obj B) :
    ∃! h : polynomial R ⟶ B, CommRingCat.ofHom Polynomial.C ≫ forget.map h = g := by
  refine ⟨⟨CommRingCat.ofHom (Polynomial.eval₂RingHom g.hom B.point),
    Polynomial.eval₂_X _ _⟩, ?_, fun h hh ↦ ?_⟩
  · ext r
    exact Polynomial.eval₂_C _ _
  · ext : 2
    apply Polynomial.ringHom_ext
    · intro r
      have := ConcreteCategory.congr_hom hh r
      exact this.trans (Polynomial.eval₂_C _ _).symm
    · exact h.map_point.trans (Polynomial.eval₂_X _ _).symm

/-- `ALGD-C1-ADJOINT-50` (例 50, p.37), for commutative rings.
For the category `Ring_∗` of pointed commutative rings and the forgetful `U : Ring_∗ → Ring`,
`F(R) = ⟨R[x], x⟩` is left adjoint to `U`. -/
theorem polynomial_adjunction :
    ∃ (L : CommRingCat.{u} ⥤ PointedRing.{u}) (_ : L ⊣ forget), ∀ R, L.obj R = polynomial R :=
  ⟨leftAdjointOfUniversalArrows forget polynomial (fun _ ↦ CommRingCat.ofHom Polynomial.C)
    polynomial_universal, adjunctionOfUniversalArrows _ _ _ _, fun _ ↦ rfl⟩

end Ex50

namespace Ex51

/-- An integral domain. -/
structure Dom : Type (u + 1) where
  /-- The ring. -/
  ring : CommRingCat.{u}
  [isDomain : IsDomain ring]

attribute [instance] Dom.isDomain

/-- A morphism of `Dom`: an injective ring homomorphism. -/
@[ext]
structure DomHom (A B : Dom.{u}) where
  /-- The underlying ring homomorphism. -/
  hom : A.ring ⟶ B.ring
  injective : Function.Injective hom

instance : Category Dom.{u} where
  Hom := DomHom
  id A := ⟨𝟙 _, fun _ _ h ↦ h⟩
  comp p q := ⟨p.hom ≫ q.hom, fun _ _ h ↦ p.injective (q.injective h)⟩

@[ext]
theorem domHom_ext {A B : Dom.{u}} {p q : A ⟶ B} (h : p.hom = q.hom) : p = q :=
  DomHom.ext h

/-- A field. -/
structure Fld : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [field : Field carrier]

attribute [instance] Fld.field

instance : Category Fld.{u} where
  Hom K L := K.carrier →+* L.carrier
  id K := RingHom.id K.carrier
  comp f g := g.comp f

/-- The forgetful functor `U : Field → Dom`. -/
def forget : Fld.{u} ⥤ Dom.{u} where
  obj K := ⟨CommRingCat.of K.carrier⟩
  map f := ⟨CommRingCat.ofHom f, f.injective⟩

/-- The fraction field `Quot(R)`. -/
noncomputable def fractionField (R : Dom.{u}) : Fld.{u} := ⟨FractionRing R.ring⟩

/-- The inclusion `R → Quot(R)`. -/
noncomputable def toFractionField (R : Dom.{u}) : R ⟶ forget.obj (fractionField R) :=
  ⟨CommRingCat.ofHom (algebraMap R.ring (FractionRing R.ring)),
    IsFractionRing.injective R.ring (FractionRing R.ring)⟩

theorem fractionField_universal (R : Dom.{u}) (K : Fld.{u}) (g : R ⟶ forget.obj K) :
    ∃! h : fractionField R ⟶ K, toFractionField R ≫ forget.map h = g := by
  refine ⟨IsFractionRing.lift (K := FractionRing R.ring) (g := g.hom.hom) g.injective, ?_,
    fun h hh ↦ ?_⟩
  · ext x
    exact IsFractionRing.lift_algebraMap (K := FractionRing R.ring) (L := K.carrier) g.injective x
  · refine IsLocalization.ringHom_ext (S := FractionRing R.ring) (nonZeroDivisors R.ring)
      (j := h) ?_
    ext x
    have := ConcreteCategory.congr_hom (congrArg DomHom.hom hh) x
    exact this.trans (IsFractionRing.lift_algebraMap (K := FractionRing R.ring) (L := K.carrier)
      g.injective x).symm

/-- `ALGD-C1-ADJOINT-51` (例 51, p.37), with injective morphisms in `Dom`.
For the category `Dom` of integral domains and injective ring homomorphisms and the forgetful
`U : Field → Dom`, the fraction field functor `Quot` is left adjoint to `U`. -/
theorem fractionField_adjunction :
    ∃ (L : Dom.{u} ⥤ Fld.{u}) (_ : L ⊣ forget), ∀ R, L.obj R = fractionField R :=
  ⟨leftAdjointOfUniversalArrows forget fractionField toFractionField fractionField_universal,
    adjunctionOfUniversalArrows _ _ _ _, fun _ ↦ rfl⟩

end Ex51

/-- `ALGD-C1-ADJOINT-54` (例 54, p.38).
The Stone–Čech compactification is left adjoint to the forgetful functor `CptHaus → Top`. -/
theorem stoneCech_adjunction :
    Nonempty (topToCompHaus.{u} ⊣ compHausToTop.{u}) ∧
    ∀ X : TopCat.{u}, ↥(topToCompHaus.obj X).toTop = StoneCech X :=
  ⟨⟨reflectorAdjunction compHausToTop⟩, topToCompHaus_obj⟩

namespace Ex56

/-- An object `⟨X, v⟩` of `Idem`: a set with an idempotent endomap. -/
structure Idem : Type (u + 1) where
  /-- The underlying set. -/
  X : Type u
  /-- The idempotent map. -/
  v : X → X
  idem : ∀ x, v (v x) = v x

/-- A morphism `f : ⟨X, v⟩ → ⟨Y, w⟩` of `Idem`: a map with `w ∘ f = f ∘ v`. -/
@[ext]
structure Hom (A B : Idem.{u}) where
  /-- The underlying map. -/
  f : A.X → B.X
  comm : ∀ x, B.v (f x) = f (A.v x)

instance : Category Idem.{u} where
  Hom := Hom
  id A := ⟨id, fun _ ↦ rfl⟩
  comp p q := ⟨q.f ∘ p.f, fun x ↦ by simp only [Function.comp_apply, q.comm, p.comm]⟩

@[ext]
theorem hom_ext {A B : Idem.{u}} {p q : A ⟶ B} (h : p.f = q.f) : p = q :=
  Hom.ext h

@[simp]
theorem comp_f {A B C : Idem.{u}} (p : A ⟶ B) (q : B ⟶ C) : (p ≫ q).f = q.f ∘ p.f :=
  rfl

@[simp]
theorem id_f (A : Idem.{u}) : Hom.f (𝟙 A) = id :=
  rfl

/-- `F⟨X, v⟩ = {x ∈ X : v(x) = x}`. -/
def fixedPoints : Idem.{u} ⥤ Type u where
  obj A := {x : A.X // A.v x = x}
  map {A B} p := TypeCat.ofHom fun x ↦ ⟨p.f x.1, by rw [p.comm, x.2]⟩

/-- `GX = ⟨X, id_X⟩`. -/
def trivialIdem : Type u ⥤ Idem.{u} where
  obj X := ⟨X, id, fun _ ↦ rfl⟩
  map h := ⟨h, fun _ ↦ rfl⟩

/-- `F ⊣ G`. -/
def fixedPointsAdj : fixedPoints.{u} ⊣ trivialIdem.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A Y ↦
        { toFun := fun φ ↦ ⟨fun x ↦ φ ⟨A.v x, A.idem x⟩, fun x ↦
            congrArg φ (Subtype.ext (A.idem x).symm)⟩
          invFun := fun g ↦ TypeCat.ofHom fun x ↦ g.f x.1
          left_inv := fun φ ↦ by
            ext x
            exact congrArg φ (Subtype.ext x.2)
          right_inv := fun g ↦ by
            ext x
            exact (g.comm x).symm }
      homEquiv_naturality_left_symm := fun _ _ ↦ rfl
      homEquiv_naturality_right := fun _ _ ↦ rfl }

/-- `G ⊣ F`. -/
def trivialIdemAdj : trivialIdem.{u} ⊣ fixedPoints.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦
        { toFun := fun g ↦ TypeCat.ofHom fun x ↦ ⟨g.f x, g.comm x⟩
          invFun := fun ψ ↦ ⟨fun x ↦ (ψ x).1, fun x ↦ (ψ x).2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      homEquiv_naturality_left_symm := fun _ _ ↦ rfl
      homEquiv_naturality_right := fun _ _ ↦ rfl }

/-- `ALGD-C1-ADJOINT-56` (例 56, p.38).
For the category `Idem` of sets with an idempotent endomap, `F⟨X, v⟩ = {x : v(x) = x}` and
`GX = ⟨X, id_X⟩` satisfy both `F ⊣ G` and `G ⊣ F`. -/
theorem idem_adjunctions :
    Nonempty (fixedPoints.{u} ⊣ trivialIdem.{u}) ∧ Nonempty (trivialIdem.{u} ⊣ fixedPoints.{u}) :=
  ⟨⟨fixedPointsAdj⟩, ⟨trivialIdemAdj⟩⟩

end Ex56

/-! ## Axiom audit

Each declaration carrying a source ID must depend only on Lean's standard axioms. The expected
output is pinned with `#guard_msgs`, so `lake build` fails if it changes. -/

/-- info: 'ProjectEpisteme.AlgD.Adjoint.HomSetAdjunction' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.HomSetAdjunction

/-- info: 'ProjectEpisteme.AlgD.Adjoint.square_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.square_iff

/-- info: 'ProjectEpisteme.AlgD.Adjoint.factor_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.factor_iff

/-- info: 'ProjectEpisteme.AlgD.Adjoint.unit_app_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.unit_app_eq

/-- info: 'ProjectEpisteme.AlgD.Adjoint.unit_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.unit_universal

/-- info: 'ProjectEpisteme.AlgD.Adjoint.universalArrow_exists_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.universalArrow_exists_iff

/-- info: 'ProjectEpisteme.AlgD.Adjoint.homEquiv_eq_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.homEquiv_eq_unit

/-- info: 'ProjectEpisteme.AlgD.Adjoint.universalArrows_leftAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.universalArrows_leftAdjoint

/-- info: 'ProjectEpisteme.AlgD.Adjoint.isRightAdjoint_iff_corepresentable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.isRightAdjoint_iff_corepresentable

/-- info: 'ProjectEpisteme.AlgD.Adjoint.unit_naturality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.unit_naturality

/-- info: 'ProjectEpisteme.AlgD.Adjoint.leftAdjoint_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.leftAdjoint_unique

/-- info: 'ProjectEpisteme.AlgD.Adjoint.leftAdjoint_preserves_colimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.leftAdjoint_preserves_colimit

/-- info: 'ProjectEpisteme.AlgD.Adjoint.op_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.op_adjunction

/-- info: 'ProjectEpisteme.AlgD.Adjoint.counit_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.counit_dual

/-- info: 'ProjectEpisteme.AlgD.Adjoint.colim_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.colim_adjunction

/-- info: 'ProjectEpisteme.AlgD.Adjoint.free_abelian_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.free_abelian_group

/-- info: 'ProjectEpisteme.AlgD.Adjoint.top_discrete_indiscrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.top_discrete_indiscrete

/-- info: 'ProjectEpisteme.AlgD.Adjoint.split_iff' depends on axioms: [Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.split_iff

/-- info: 'ProjectEpisteme.AlgD.Adjoint.split_epi_mono' depends on axioms: [Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.split_epi_mono

/-- info: 'ProjectEpisteme.AlgD.Adjoint.isIso_of_mono_of_split_epi' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.isIso_of_mono_of_split_epi

/-- info: 'ProjectEpisteme.AlgD.Adjoint.isIso_of_epi_of_split_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.isIso_of_epi_of_split_mono

/-- info: 'ProjectEpisteme.AlgD.Adjoint.map_split_epi' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.map_split_epi

/-- info: 'ProjectEpisteme.AlgD.Adjoint.yoneda_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.yoneda_split

/-- info: 'ProjectEpisteme.AlgD.Adjoint.faithful_full_criteria' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.faithful_full_criteria

/-- info: 'ProjectEpisteme.AlgD.Adjoint.triple_fullyFaithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.triple_fullyFaithful

/-- info: 'ProjectEpisteme.AlgD.Adjoint.HomSetAdjunction.right_triangle' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.HomSetAdjunction.right_triangle

/-- info: 'ProjectEpisteme.AlgD.Adjoint.HomSetAdjunction.left_triangle' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.HomSetAdjunction.left_triangle

/-- info: 'ProjectEpisteme.AlgD.Adjoint.adjunction_of_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.adjunction_of_triangle

/-- info: 'ProjectEpisteme.AlgD.Adjoint.counit_isIso_of_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.counit_isIso_of_iso

/-- info: 'ProjectEpisteme.AlgD.Adjoint.adjunction_of_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.adjunction_of_equivalence

/-- info: 'ProjectEpisteme.AlgD.Adjoint.equivalence_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.equivalence_preserves

/-- info: 'ProjectEpisteme.AlgD.Adjoint.hasColimits_of_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.hasColimits_of_equivalence

/-- info: 'ProjectEpisteme.AlgD.Adjoint.unit_counit_iso_consequences' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.unit_counit_iso_consequences

/-- info: 'ProjectEpisteme.AlgD.Adjoint.isEquivalence_of_fullyFaithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.isEquivalence_of_fullyFaithful

/-- info: 'ProjectEpisteme.AlgD.Adjoint.free_vectorSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.free_vectorSpace

/-- info: 'ProjectEpisteme.AlgD.Adjoint.comp_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.comp_adjunction

/-- info: 'ProjectEpisteme.AlgD.Adjoint.postcomp_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.postcomp_adjunction

/-- info: 'ProjectEpisteme.AlgD.Adjoint.precomp_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.precomp_adjunction

/-- info: 'ProjectEpisteme.AlgD.Adjoint.presheaf_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.presheaf_adjunction

/-- info: 'ProjectEpisteme.AlgD.Adjoint.unitFixed_le_essImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.unitFixed_le_essImage

/-- info: 'ProjectEpisteme.AlgD.Adjoint.fixedPoint_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.fixedPoint_equivalence

/-- info: 'ProjectEpisteme.AlgD.Adjoint.idempotent_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.idempotent_tfae

/-- info: 'ProjectEpisteme.AlgD.Adjoint.unitFixed_reflective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.unitFixed_reflective

/-- info: 'ProjectEpisteme.AlgD.Adjoint.free_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.free_group

/-- info: 'ProjectEpisteme.AlgD.Adjoint.abelianization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.abelianization

/-- info: 'ProjectEpisteme.AlgD.Adjoint.module_forget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.module_forget

/-- info: 'ProjectEpisteme.AlgD.Adjoint.top_adjoint_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.top_adjoint_triple

/-- info: 'ProjectEpisteme.AlgD.Adjoint.stoneCech_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.stoneCech_adjunction

/-- info: 'ProjectEpisteme.AlgD.Adjoint.Ex56.idem_adjunctions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.Ex56.idem_adjunctions

/-- info: 'ProjectEpisteme.AlgD.Adjoint.idempotent_iff_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.idempotent_iff_factorization

/-- info: 'ProjectEpisteme.AlgD.Adjoint.factorization_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.factorization_equivalence

/-- info: 'ProjectEpisteme.AlgD.Adjoint.IsExponential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.IsExponential

/-- info: 'ProjectEpisteme.AlgD.Adjoint.types_exponential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.types_exponential

/-- info: 'ProjectEpisteme.AlgD.Adjoint.exponential_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.exponential_adjunction

/-- info: 'ProjectEpisteme.AlgD.Adjoint.IsCartesianClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.IsCartesianClosed

/-- info: 'ProjectEpisteme.AlgD.Adjoint.exponential_of_rightAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.exponential_of_rightAdjoint

/-- info: 'ProjectEpisteme.AlgD.Adjoint.exponential_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.exponential_preserves

/-- info: 'ProjectEpisteme.AlgD.Adjoint.exponential_exponential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.exponential_exponential

/-- info: 'ProjectEpisteme.AlgD.Adjoint.exponential_coprod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.exponential_coprod

/-- info: 'ProjectEpisteme.AlgD.Adjoint.exponential_initial_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.exponential_initial_unit

/-- info: 'ProjectEpisteme.AlgD.Adjoint.parametrized_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.parametrized_adjunction

/-- info: 'ProjectEpisteme.AlgD.Adjoint.parametrized_square_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.parametrized_square_iff

/-- info: 'ProjectEpisteme.AlgD.Adjoint.exponential_bifunctor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.exponential_bifunctor

/-- info: 'ProjectEpisteme.AlgD.Adjoint.ab_not_cartesianClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.ab_not_cartesianClosed

/-- info: 'ProjectEpisteme.AlgD.Adjoint.monoid_ring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.monoid_ring

/-- info: 'ProjectEpisteme.AlgD.Adjoint.Ex50.polynomial_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.Ex50.polynomial_adjunction

/-- info: 'ProjectEpisteme.AlgD.Adjoint.Ex51.fractionField_adjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Adjoint.Ex51.fractionField_adjunction

end ProjectEpisteme.AlgD.Adjoint

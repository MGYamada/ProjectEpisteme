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
* Not formalized yet (see the ledger): §4 (cartesian closed categories), 定理 32, 系 34, 定理 41,
  系 42 and 例 49–53, 55.
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
    have he : ∀ (X' X : C) (Y : D) (f : X' ⟶ X) (g : F'.obj X ⟶ Y),
        universalArrowFromEquiv F' c ε hε X' Y (F'.map f ≫ g) =
          f ≫ universalArrowFromEquiv F' c ε hε X Y g := fun X' X Y f g ↦ by
      rw [universalArrowFromEquiv, Equiv.symm_apply_eq]
      simp only [Equiv.ofBijective_apply, F'.map_comp, Category.assoc]
      congr 1
      exact ((Equiv.ofBijective (fun g : X ⟶ c Y ↦ F'.map g ≫ ε Y)
        ((Function.bijective_iff_existsUnique _).2 (hε Y X))).apply_symm_apply g).symm
    exact (Adjunction.adjunctionOfEquivRight _ he).isLeftAdjoint
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
    ((unit_counit_iso_aux e.toAdjunction).1 hη).2.1, ((unit_counit_iso_aux e.toAdjunction).2 hε).2.2⟩

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

end ProjectEpisteme.AlgD.Adjoint

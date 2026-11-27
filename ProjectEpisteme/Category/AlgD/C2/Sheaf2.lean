/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Topology.Sheaves.EtaleSpace
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Tactic.TFAE

/-!
# alg-d, Chapter 2: 例：位相空間上の層 その2 (Example: sheaves on a topological space, part 2)

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 2, `sheaf_kan_extension.pdf`
(<https://alg-d.com/math/kan_extension/sheaf_kan_extension.pdf>), printed date 2026-07-22,
SHA-256 `abb57620ed58bd0842f0f0bed9c031f3abe16114df46770bd0680b783e74075b`,
retrieved 2026-11-26. Ledger: `docs/ledger/algd/C2-SHEAF2.md`.

§1 restates results of 「Kan拡張」; those rows share the declarations in
`ProjectEpisteme/Category/AlgD/C2/Kan.lean`. This module covers §2–§4.

## Conventions

* `X : TopCat.{u}`, `O_X` is `Opens X` with its order category, and a presheaf on `X` is
  `TopCat.Presheaf (Type u) X = (Opens X)ᵒᵖ ⥤ Type u`.
* The stalk `P_x` is mathlib's `TopCat.Presheaf.stalk`, the colimit over the open neighbourhoods
  of `x`; `stalkFunctorIso` identifies the functor with the source's `ev_{x} ∘ i_x^*`.
* `F : O_X → Top/X` is `toOver X`, sending `U` to its inclusion `U → X` in `Over X`.
* The Yoneda embedding in the universal adjunction is mathlib's `uliftYoneda.{u}`, and
  `F † y = Presheaf.restrictedULiftYoneda.{u} (toOver X)`, so
  `F † y(f)(U) = ULift (Hom_{Top/X}(F U, f))`. The `ULift` changes no universe here, since the
  hom-sets of `Opens X` and `Over X` are already in `Type u`.
* `Sh(X)` is `TopCat.Sheaf (Type u) X`, the full subcategory of sheaves, with the inclusion
  `TopCat.Sheaf.forget`. 命題 19 and 命題 20 are stated for every left adjoint of the inclusion,
  which covers the source's `L = F † y ∘ y † F` (`sheafification`) and mathlib's sheafification.
* `y † F` is taken to be the étale space functor `etale X`, `P ↦ (EtaleSpace P → X)`, where
  mathlib's `EtaleSpace P` is the source's `E = ∐_x P_x` with its topology. `etaleIsPointwise`
  shows that it is a pointwise left Kan extension with legs `ν_{⟨U,u⟩} = germHom P U u`, and
  `etaleAdj` is the universal adjunction `y † F ⊣ F † y` built from it by mathlib's
  `uliftYonedaAdjunction`. R06, R08 and R09 are stated for any pointwise left Kan extension.
* The source's arguments that compute `y † F` from the colimit (R06–R09) are replaced by the proof
  that the étale space is that colimit. 命題 14 compares stalks instead of gluing, and 命題 23
  (whose proof the source omits) is proved through `Sh(U) ≃ Etale(U)` on an open `U`.
-/

@[expose] public section

namespace ProjectEpisteme.AlgD.Sheaf2

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology TopCat.Presheaf

universe u

variable {X : TopCat.{u}}

/-! ## §2 Stalks of presheaves -/

/-- `ALGD-C2-SHEAF2-D01` (prose, §2, p.2).
The open sets of `X` ordered by inclusion form a category with a morphism `U → V` iff `U ⊆ V`,
and `Ô_X = Set^{O_X^op}` is the category of presheaves on `X`. -/
theorem presheaf_def :
    TopCat.Presheaf (Type u) X = ((Opens X)ᵒᵖ ⥤ Type u) ∧
      ∀ U V : Opens X, Nonempty (U ⟶ V) ↔ U ≤ V :=
  ⟨rfl, fun _ _ ↦ ⟨fun ⟨i⟩ ↦ i.le, fun h ↦ ⟨homOfLE h⟩⟩⟩

/-- The inclusion `i_x : {x} → X` of a point. -/
def pointInclusion (x : X) : TopCat.of ({x} : Set X) ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The open neighbourhoods of `x`, as objects of `F ↓ {x}` for `F = (i_x⁻¹)^op`. An open set `V`
lies in `F ↓ {x}` iff `{x} ⊆ i_x⁻¹(V)`, that is, iff `x ∈ V`. -/
def nhdsToArrow (x : X) :
    (OpenNhds x)ᵒᵖ ⥤ CostructuredArrow (Opens.map (pointInclusion x)).op (op ⊤) where
  obj V := CostructuredArrow.mk (Y := op V.unop.1)
    (homOfLE (fun y _ ↦ by
      obtain ⟨y, rfl⟩ := y
      exact V.unop.2)).op
  map {V W} f := CostructuredArrow.homMk ((OpenNhds.inclusion x).map f.unop).op rfl

instance (x : X) : (nhdsToArrow x).Full where
  map_surjective {_ _} g := ⟨(homOfLE (leOfHom g.left.unop)).op, rfl⟩

instance (x : X) : (nhdsToArrow x).Faithful where
  map_injective {_ _} _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

instance (x : X) : (nhdsToArrow x).EssSurj where
  mem_essImage c := by
    have hx : x ∈ c.left.unop :=
      leOfHom c.hom.unop (show (⟨x, rfl⟩ : ({x} : Set X)) ∈ (⊤ : Opens _) from trivial)
    exact ⟨op ⟨c.left.unop, hx⟩, ⟨CostructuredArrow.isoMk (Iso.refl _) rfl⟩⟩

instance (x : X) : (nhdsToArrow x).IsEquivalence where

/-- The stalk functor as the colimit over `F ↓ {x}`, through the equivalence `nhdsToArrow`. -/
noncomputable def stalkFunctorIsoColim (x : X) :
    stalkFunctor (Type u) x ≅
      (Functor.whiskeringLeft _ _ (Type u)).obj
        (CostructuredArrow.proj (Opens.map (pointInclusion x)).op (op ⊤)) ⋙ colim :=
  Functor.isoWhiskerLeft ((Functor.whiskeringLeft _ _ (Type u)).obj
    (CostructuredArrow.proj (Opens.map (pointInclusion x)).op (op ⊤)))
    (Functor.Final.colimIso (nhdsToArrow x))

/-- The stalk functor is `ev_{x} ∘ i_x^*`. -/
noncomputable def stalkFunctorIso (x : X) :
    stalkFunctor (Type u) x ≅
      Presheaf.pullback (Type u) (pointInclusion x) ⋙ (evaluation _ _).obj (op ⊤) :=
  stalkFunctorIsoColim x ≪≫
    (lanEvaluationIsoColim (Type u) (Opens.map (pointInclusion x)).op (op ⊤)).symm

/-- `ALGD-C2-SHEAF2-D02` (prose, §2, p.3).
For `x ∈ X` with inclusion `i_x : {x} → X`, the stalk functor `st_x : Ô_X → Set` is the composite
`ev_{x} ∘ i_x^*`, and `P_x := st_x(P)` is the stalk of `P` at `x`. mathlib defines the stalk as
the colimit over the open neighbourhoods of `x`; the two functors are naturally isomorphic. -/
theorem stalkFunctor_iso_pullback (x : X) :
    Nonempty (stalkFunctor (Type u) x ≅
      Presheaf.pullback (Type u) (pointInclusion x) ⋙ (evaluation _ _).obj (op ⊤)) :=
  ⟨stalkFunctorIso x⟩

/-- `ALGD-C2-SHEAF2-R02` (prose, §2, p.3).
`P_x ≅ colim_{U ∋ x} P(U) ≅ (∐_{U ∋ x} P(U))/∼`, where `u ∈ P(U)` and `v ∈ P(V)` satisfy `u ∼ v`
iff `u|_W = v|_W` for some open `W` with `x ∈ W ⊆ U ∩ V`: every element of the stalk is a germ,
and two germs agree iff the sections agree on a smaller neighbourhood. -/
theorem stalk_quotient (P : X.Presheaf (Type u)) (x : X) :
    (∀ t : P.stalk x, ∃ (U : Opens X) (hU : x ∈ U) (u : P.obj (op U)), P.germ U x hU u = t) ∧
    ∀ {U V : Opens X} (hU : x ∈ U) (hV : x ∈ V) (u : P.obj (op U)) (v : P.obj (op V)),
      P.germ U x hU u = P.germ V x hV v ↔
        ∃ (W : Opens X) (_ : x ∈ W) (i : W ⟶ U) (j : W ⟶ V), P.map i.op u = P.map j.op v :=
  ⟨fun t ↦ P.exists_germ_eq t, fun hU hV u v ↦
    ⟨P.germ_eq _ hU hV u v, fun ⟨W, hW, i, j, h⟩ ↦ P.germ_ext W hW i j h⟩⟩

/-- Germs of continuous maps into `T` agree iff the maps agree near the point. -/
theorem germ_continuous_eq_iff (T : TopCat.{u}) {U V : Opens X} {x : X} (hU : x ∈ U)
    (hV : x ∈ V) (u : (Opens.toTopCat X).obj U ⟶ T) (v : (Opens.toTopCat X).obj V ⟶ T) :
    germ (presheafToTop X T) U x hU u = germ (presheafToTop X T) V x hV v ↔
      ∃ (W : Opens X) (hW : W ≤ U ⊓ V), x ∈ W ∧
        ∀ (a : X) (ha : a ∈ W), u ⟨a, (hW ha).1⟩ = v ⟨a, (hW ha).2⟩ := by
  rw [(stalk_quotient (presheafToTop X T) x).2 hU hV u v]
  constructor
  · rintro ⟨W, hxW, i, j, h⟩
    exact ⟨W, le_inf i.le j.le, hxW, fun a ha ↦
      congrArg (fun φ : (Opens.toTopCat X).obj W ⟶ T ↦ φ ⟨a, ha⟩) h⟩
  · rintro ⟨W, hW, hxW, h⟩
    refine ⟨W, hxW, homOfLE (hW.trans inf_le_left), homOfLE (hW.trans inf_le_right), ?_⟩
    change (Opens.toTopCat X).map (homOfLE (hW.trans inf_le_left)) ≫ u =
      (Opens.toTopCat X).map (homOfLE (hW.trans inf_le_right)) ≫ v
    ext ⟨a, ha⟩
    exact h a ha

/-- `ALGD-C2-SHEAF2-09` (例 9, §2, p.3).
For the presheaf of real-valued continuous functions, `u ∈ P(U)` and `v ∈ P(V)` have the same
germ at `x` iff `u(a) = v(a)` for all `a` in some open `W ⊆ U ∩ V` containing `x`. The values
are taken in `ULift ℝ`, so that the presheaf is valued in `Type u`. -/
theorem real_germ_eq_iff {U V : Opens X} {x : X} (hU : x ∈ U) (hV : x ∈ V)
    (u : (Opens.toTopCat X).obj U ⟶ TopCat.of (ULift.{u} ℝ))
    (v : (Opens.toTopCat X).obj V ⟶ TopCat.of (ULift.{u} ℝ)) :
    germ (presheafToTop X (TopCat.of (ULift.{u} ℝ))) U x hU u =
        germ (presheafToTop X (TopCat.of (ULift.{u} ℝ))) V x hV v ↔
      ∃ (W : Opens X) (hW : W ≤ U ⊓ V), x ∈ W ∧
        ∀ (a : X) (ha : a ∈ W), (u ⟨a, (hW ha).1⟩).down = (v ⟨a, (hW ha).2⟩).down := by
  simp only [germ_continuous_eq_iff, ULift.ext_iff]

/-- `ALGD-C2-SHEAF2-10` (例 10, §2, p.3).
For an open `O` and `P := y(O)`, the stalk `P_x` is empty if `x ∉ O` and a singleton if `x ∈ O`.
The proof uses germs; the source uses that `{U ∋ x ∣ U ⊆ O}` is final in `{U ∋ x}`. -/
theorem stalk_yoneda (O : Opens X) (x : X) :
    (x ∉ O → IsEmpty (stalk (yoneda.obj O) x)) ∧
    (x ∈ O → Nonempty (stalk (yoneda.obj O) x ≃ PUnit.{u + 1})) := by
  refine ⟨fun h ↦ ⟨fun t ↦ ?_⟩, fun h ↦ ⟨?_⟩⟩
  · obtain ⟨U, hU, f, -⟩ := exists_germ_eq (yoneda.obj O) t
    exact h (f.le hU)
  · refine
      { toFun := fun _ ↦ PUnit.unit
        invFun := fun _ ↦ germ (yoneda.obj O) O x h (𝟙 O)
        left_inv := fun t ↦ ?_
        right_inv := fun _ ↦ rfl }
    obtain ⟨U, hU, f, rfl⟩ := exists_germ_eq (yoneda.obj O) t
    exact germ_ext (yoneda.obj O) (U ⊓ O) ⟨hU, h⟩ (Opens.infLERight _ _) (Opens.infLELeft _ _)
      (Subsingleton.elim (α := U ⊓ O ⟶ O) _ _)

/-- `ALGD-C2-SHEAF2-R03` (prose, §2, p.4).
For `θ : P ⇒ Q` the map `θ_x := st_x(θ) : P_x → Q_x` sends the germ `u_x` of `u ∈ P(U)` to
`(θ_U(u))_x`. -/
theorem stalk_map_germ {P Q : X.Presheaf (Type u)} (θ : P ⟶ Q) {U : Opens X} (u : P.obj (op U))
    {x : X} (hx : x ∈ U) :
    (stalkFunctor (Type u) x).map θ (P.germ U x hx u) = Q.germ U x hx (θ.app (op U) u) :=
  stalkFunctor_map_germ_apply U x hx θ u

/-- `ALGD-C2-SHEAF2-R04` (prose, §2, p.4).
If `u ∈ P(U)` corresponds to `θ : y(U) ⇒ P` under the Yoneda lemma and `x ∈ U`, then `θ_x` sends
the germ `(id_U)_x`, the only element of `y(U)_x` (例 10), to `u_x`. So `u` and `θ` may both be
written `u`. -/
theorem stalk_yonedaEquiv (P : X.Presheaf (Type u)) {U : Opens X} (u : P.obj (op U)) {x : X}
    (hx : x ∈ U) :
    (stalkFunctor (Type u) x).map (yonedaEquiv.symm u) (germ (yoneda.obj U) U x hx (𝟙 U)) =
      P.germ U x hx u := by
  rw [stalkFunctor_map_germ_apply]
  simp [yonedaEquiv_symm_app_apply]

/-! ## §3 Sheaves and étale bundles -/

/-- `ALGD-C2-SHEAF2-D04` (prose, §3, p.4).
The functor `F : O_X → Top/X` sends an open set `U` to its inclusion `U → X`. -/
@[simps]
def toOver (X : TopCat.{u}) : Opens X ⥤ Over X where
  obj U := Over.mk U.inclusion'
  map {_ _} i := Over.homMk ((Opens.toTopCat X).map i) rfl

/-- `ALGD-C2-SHEAF2-R05` (prose, §3, p.4).
`Top/X` is cocomplete, so the pointwise left Kan extension `y † F` exists, and the universal
adjunction (定理 3) gives `y † F ⊣ F † y : Ô_X → Top/X`, where `F † y(f) = Hom_{Top/X}(F −, f)`. -/
theorem universal_adjunction_exists :
    HasColimits (Over X) ∧ (uliftYoneda.{u}).HasPointwiseLeftKanExtension (toOver X) ∧
      Nonempty ((uliftYoneda.{u}).leftKanExtension (toOver X) ⊣
        Presheaf.restrictedULiftYoneda.{u} (toOver X)) :=
  ⟨inferInstance, inferInstance, ⟨Presheaf.uliftYonedaAdjunction.{0}
    ((uliftYoneda.{u}).leftKanExtension (toOver X))
    ((uliftYoneda.{u}).leftKanExtensionUnit (toOver X))⟩⟩

/-- The sections of `f` over `U`, as in (11). -/
def sectionsEquiv (f : Over X) (U : Opens X) :
    ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f).obj (op U) ≃
      {s : (Opens.toTopCat X).obj U ⟶ f.left // s ≫ f.hom = U.inclusion'} where
  toFun s := ⟨s.down.left, Over.w s.down⟩
  invFun s := ULift.up (Over.homMk s.1 s.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `ALGD-C2-SHEAF2-11` (formula (11), §3, p.4).
For `f : Y → X` in `Top/X` and `U ∈ O_X`, `F † y(f)(U) ≅ Hom_{Top/X}(F(U), f)
= {s ∈ Hom_Top(U, Y) ∣ f ∘ s = F(U)}`, the continuous sections of `f` over `U`. -/
theorem sections_spec (f : Over X) (U : Opens X) :
    Nonempty (((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f).obj (op U) ≃
      {s : (Opens.toTopCat X).obj U ⟶ f.left // s ≫ f.hom = U.inclusion'}) :=
  ⟨sectionsEquiv f U⟩

/-! ## §4 Sheafification -/

/-- The local predicate of continuous sections of `f`. -/
def sectionPredicate (f : Over X) : LocalPredicate fun _ : X ↦ f.left :=
  (continuousLocal X f.left).and (isSection f.hom)

/-- `F † y(f)` is the presheaf of functions satisfying `sectionPredicate f`. -/
def sectionsIso (f : Over X) :
    subpresheafToTypes (sectionPredicate f).toPrelocalPredicate ≅
      (Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun := fun g ↦ ULift.up (Over.homMk (TopCat.ofHom ⟨g.1, g.2.1⟩) (by
        ext y
        exact congrFun g.2.2 y))
      invFun := fun s ↦ ⟨fun y ↦ s.down.left y, s.down.left.hom.continuous, by
        funext y
        exact congrArg (fun φ ↦ φ y) (Over.w s.down)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl })

/-- `ALGD-C2-SHEAF2-18` (命題 18, §4, p.14).
For `f ∈ Top/X`, the presheaf `F † y(f)` of sections of `f` is a sheaf: by (11), continuity and
the section condition are both local. -/
theorem sections_isSheaf (f : Over X) :
    TopCat.Presheaf.IsSheaf ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f) :=
  isSheaf_of_iso (sectionsIso f) (subpresheafToTypes.isSheaf (sectionPredicate f))

/-- `ALGD-C2-SHEAF2-19` (命題 19, §4, p.15).
Let `L ⊣ U` with `U : Sh(X) → Ô_X` the inclusion and unit `η`. For a presheaf `P`, a sheaf `Q`
and `θ : P ⇒ U(Q)` there is a unique `τ : LP ⇒ Q` with `U(τ) ∘ η_P = θ`. -/
theorem sheafify_universal {L : X.Presheaf (Type u) ⥤ X.Sheaf (Type u)}
    (adj : L ⊣ Sheaf.forget (Type u) X) (P : X.Presheaf (Type u)) (Q : X.Sheaf (Type u))
    (θ : P ⟶ (Sheaf.forget (Type u) X).obj Q) :
    ∃! τ : L.obj P ⟶ Q, adj.unit.app P ≫ (Sheaf.forget (Type u) X).map τ = θ := by
  refine ⟨(adj.homEquiv P Q).symm θ, ?_, fun τ hτ ↦ ?_⟩
  · exact (adj.homEquiv_unit P Q _).symm.trans ((adj.homEquiv P Q).apply_symm_apply θ)
  · rw [← (adj.homEquiv P Q).symm_apply_apply τ]
    exact congrArg _ ((adj.homEquiv_unit P Q τ).trans hτ)

/-- `ALGD-C2-SHEAF2-20` (命題 20, §4, p.15).
Sheafification preserves stalks: for a left adjoint `L` of the inclusion `Sh(X) → Ô_X`, the map
`P_x → (LP)_x` induced by the unit `η_P` is a bijection. The proof uses that `st_x` is left
adjoint to the skyscraper sheaf functor followed by the inclusion; the source uses 命題 12 and
the idempotence of `y † F ⊣ F † y`. -/
theorem sheafify_stalk {L : X.Presheaf (Type u) ⥤ X.Sheaf (Type u)}
    (adj : L ⊣ Sheaf.forget (Type u) X) (P : X.Presheaf (Type u)) (x : X) :
    IsIso ((stalkFunctor (Type u) x).map (adj.unit.app P)) := by
  classical
  exact Adjunction.isIso_map_unit_of_isLeftAdjoint_comp adj (skyscraperSheafForgetAdjunction x)

/-- `ALGD-C2-SHEAF2-22` (condition (22), §4, p.16).
A map `k : U → A` into a discrete space satisfies (22), "every `x ∈ U` has an open neighbourhood
`V ⊆ U` on which `k` is constant", iff `k` is continuous. -/
theorem locallyConstant_iff {U : Opens X} {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (k : U → A) :
    (∀ x : U, ∃ V : Opens X, x.1 ∈ V ∧ V ≤ U ∧ ∀ y : U, y.1 ∈ V → k y = k x) ↔
      Continuous k := by
  rw [← IsLocallyConstant.iff_continuous, IsLocallyConstant.iff_exists_open]
  constructor
  · intro h x
    obtain ⟨V, hxV, -, hV⟩ := h x
    exact ⟨Subtype.val ⁻¹' V, V.isOpen.preimage continuous_subtype_val, hxV, fun y hy ↦ hV y hy⟩
  · intro h x
    obtain ⟨W, hW, hxW, hk⟩ := h x
    refine ⟨⟨Subtype.val '' W, U.isOpen.isOpenMap_subtype_val W hW⟩, ⟨x, hxW, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · rintro y ⟨y', hy', hyy'⟩
      rw [← Subtype.ext hyy']
      exact hk y' hy'

/-- `ALGD-C2-SHEAF2-D08` (prose, §4, p.17).
For `P ∈ Ô_X` and `U ∈ O_X`, `P|_U := F(U)^*(P)` is the inverse image along the inclusion
`U → X`, and `P|_U(V) ≅ colim_{W ⊃ V} P(W) ≅ P(V)` for `V` open in `U`. -/
theorem restrict_obj (P : X.Presheaf (Type u)) (U : Opens X)
    (V : Opens ((Opens.toTopCat X).obj U)) :
    Nonempty (((Presheaf.pullback (Type u) U.inclusion').obj P).obj (op V) ≅
      P.obj (op ⟨U.inclusion' '' V, U.isOpenEmbedding.isOpenMap _ V.2⟩)) :=
  ⟨pullbackObjObjOfImageOpen _ P V _⟩

/-- `ALGD-C2-SHEAF2-D09` (定義, §4, p.17).
A sheaf `P` is locally constant if every `x ∈ X` has an open neighbourhood `U` such that `P|_U`
is isomorphic to a constant sheaf, the sheafification of a constant presheaf `ΔA` on `U`. -/
def IsLocallyConstantSheaf (P : X.Sheaf (Type u)) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ A : Type u,
    Nonempty ((Presheaf.pullback (Type u) U.inclusion').obj P.presheaf ≅
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) (Type u)).obj A).obj)

/-- `ALGD-C2-SHEAF2-24` (例 24, §4, p.17–18).
The skyscraper sheaf. `st_x` has a right adjoint `G_x † y`, and `P := G_x † y(A)` satisfies
`P(U) ≅ Hom_Set(y(U)_x, A)`, which is `A` if `x ∈ U` and a singleton otherwise (例 10). `P` is a
sheaf, and if `X` is T1 then `P_z ≅ A` for `z = x` and `P_z ≅ 1` for `z ≠ x`. In mathlib, `P` is
`skyscraperPresheaf x A`, the right adjoint of the stalk functor. -/
theorem skyscraper_spec (x : X) [∀ U : Opens X, Decidable (x ∈ U)] (A : Type u) :
    Nonempty (stalkFunctor (Type u) x ⊣ skyscraperPresheafFunctor x) ∧
    (∀ U : Opens X, Nonempty ((skyscraperPresheaf x A).obj (op U) ≃
      (stalk (yoneda.obj U) x → A))) ∧
    (skyscraperPresheaf x A).IsSheaf ∧
    (T1Space X → ∀ z : X, (z = x → Nonempty ((skyscraperPresheaf x A).stalk z ≃ A)) ∧
      (z ≠ x → Nonempty ((skyscraperPresheaf x A).stalk z ≃ PUnit.{u + 1}))) := by
  refine ⟨⟨skyscraperPresheafStalkAdjunction x⟩, fun U ↦ ?_, skyscraperPresheaf_isSheaf x A,
    fun _ z ↦ ⟨?_, fun hz ↦ ?_⟩⟩
  · by_cases h : x ∈ U
    · obtain ⟨e⟩ := (stalk_yoneda U x).2 h
      rw [skyscraperPresheaf_obj, ite_eq_left h]
      exact ⟨((Equiv.arrowCongr e (Equiv.refl A)).trans (Equiv.punitArrowEquiv A)).symm⟩
    · have := (stalk_yoneda U x).1 h
      rw [skyscraperPresheaf_obj, ite_eq_right h]
      exact ⟨(Types.terminalIso.toEquiv).trans (Equiv.ofUnique _ _)⟩
  · rintro rfl
    exact ⟨(skyscraperPresheafStalkOfSpecializes z A specializes_rfl).toEquiv⟩
  · have : ¬ x ⤳ z := fun h ↦ hz (specializes_iff_eq.mp h).symm
    exact ⟨(skyscraperPresheafStalkOfNotSpecializes x A this ≪≫ Types.terminalIso).toEquiv⟩

/-! ## §3–§4 The étale space, `Sh(X) ≃ Etale(X)`, constant sheaves and covering maps -/

noncomputable section

section Etale

variable (P : X.Presheaf (Type u))

/-- The set of germs of `s ∈ P(U)`. -/
def germSet (U : Opens X) (s : P.obj (op U)) : Set (EtaleSpace P) :=
  {g | ∃ h : g.base ∈ U, g.germ = P.germ U g.base h s}

theorem isOpen_germSet (U : Opens X) (s : P.obj (op U)) : IsOpen (germSet P U s) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, s, rfl⟩

variable {P} in
theorem eventually_germ_eq {U V : Opens X} {x : X} (hU : x ∈ U) (hV : x ∈ V)
    {s : P.obj (op U)} {t : P.obj (op V)} (h : P.germ U x hU s = P.germ V x hV t) :
    ∃ W : Opens X, x ∈ W ∧ ∃ (hWU : W ≤ U) (hWV : W ≤ V), ∀ (y : X) (hy : y ∈ W),
      P.germ U y (hWU hy) s = P.germ V y (hWV hy) t := by
  obtain ⟨W, hxW, i, j, e⟩ := P.germ_eq x hU hV s t h
  refine ⟨W, hxW, i.le, j.le, fun y hy ↦ ?_⟩
  rw [← P.germ_res_apply i y hy s, ← P.germ_res_apply j y hy t, e]

/-- `ν_{U,s} : U → E`, `x ↦ s_x`. -/
def germMap (U : Opens X) (s : P.obj (op U)) (x : U) : EtaleSpace P :=
  ⟨x.1, P.germ U x.1 x.2 s⟩

theorem continuous_germMap (U : Opens X) (s : P.obj (op U)) : Continuous (germMap P U s) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨V, t, rfl⟩
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨hxV, hx⟩
  obtain ⟨W, hxW, hWU, hWV, hW⟩ := eventually_germ_eq x.2 hxV hx
  exact ⟨Subtype.val ⁻¹' (W : Set X), fun y hy ↦ ⟨hWV hy, hW y.1 hy⟩,
    W.isOpen.preimage continuous_subtype_val, hxW⟩

/-- `E → X` as an object of `Top/X`. -/
def etaleObj : Over X :=
  Over.mk (Y := TopCat.of (EtaleSpace P))
    (TopCat.ofHom ⟨EtaleSpace.base, EtaleSpace.continuous_base P⟩)

/-- `ν_{U,s}` as a morphism `F(U) → E` over `X`. -/
def germHom (U : Opens X) (s : P.obj (op U)) : (toOver X).obj U ⟶ etaleObj P :=
  Over.homMk (TopCat.ofHom ⟨germMap P U s, continuous_germMap P U s⟩) rfl

variable {P}

theorem germHom_apply (U : Opens X) (s : P.obj (op U)) (x : U) :
    (germHom P U s).left x = germMap P U s x := rfl

/-- The map `E_P → E_Q` induced by `θ : P ⟶ Q` on stalks. -/
def etaleMapFun {Q : X.Presheaf (Type u)} (θ : P ⟶ Q) (g : EtaleSpace P) : EtaleSpace Q :=
  ⟨g.base, (stalkFunctor (Type u) g.base).map θ g.germ⟩

theorem continuous_etaleMapFun {Q : X.Presheaf (Type u)} (θ : P ⟶ Q) :
    Continuous (etaleMapFun θ) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨V, t, rfl⟩
  rw [isOpen_iff_forall_mem_open]
  rintro g ⟨hgV, hg⟩
  obtain ⟨U, hU, s, hs⟩ := P.exists_germ_eq g.germ
  change (stalkFunctor (Type u) g.base).map θ g.germ = _ at hg
  rw [← hs, stalkFunctor_map_germ_apply] at hg
  obtain ⟨W, hxW, hWU, hWV, hW⟩ := eventually_germ_eq hU hgV hg
  refine ⟨germSet P U s ∩ EtaleSpace.base ⁻¹' (W : Set X), ?_,
    (isOpen_germSet P U s).inter (W.isOpen.preimage (EtaleSpace.continuous_base P)),
    ⟨hU, hs.symm⟩, hxW⟩
  rintro g' ⟨⟨hg'U, hg'⟩, hg'W⟩
  refine ⟨hWV hg'W, ?_⟩
  change (stalkFunctor (Type u) g'.base).map θ g'.germ = _
  rw [hg', stalkFunctor_map_germ_apply]
  exact hW _ hg'W

variable (X) in
/-- The étale space functor `y † F : Ô_X → Top/X`. -/
def etale : X.Presheaf (Type u) ⥤ Over X where
  obj := etaleObj
  map θ := Over.homMk (TopCat.ofHom ⟨etaleMapFun θ, continuous_etaleMapFun θ⟩) rfl
  map_id P := by
    ext ⟨b, t⟩
    change (⟨b, (stalkFunctor (Type u) b).map (𝟙 P) t⟩ : EtaleSpace P) = ⟨b, t⟩
    rw [(stalkFunctor (Type u) b).map_id]
  map_comp θ φ := by
    ext g
    change etaleMapFun (θ ≫ φ) g = etaleMapFun φ (etaleMapFun θ g)
    simp [etaleMapFun]

theorem etale_map_germHom {Q : X.Presheaf (Type u)} (θ : P ⟶ Q) (U : Opens X)
    (s : P.obj (op U)) : germHom P U s ≫ (etale X).map θ = germHom Q U (θ.app (op U) s) := by
  ext x
  change (⟨x.1, (stalkFunctor (Type u) x.1).map θ (P.germ U x.1 x.2 s)⟩ : EtaleSpace Q) = _
  rw [stalkFunctor_map_germ_apply]
  rfl

variable (X) in
/-- The unit `ξ : F ⇒ (y † F) ∘ y`, `x ↦ (id_U)_x`. -/
def etaleUnit : toOver X ⟶ uliftYoneda.{u} ⋙ etale X where
  app U := germHom (uliftYoneda.{u}.obj U) U (uliftYonedaEquiv (𝟙 _))
  naturality U V i := by
    ext ⟨x, hx⟩
    change EtaleSpace.mk (F := uliftYoneda.{u}.obj V) x
        (germ (uliftYoneda.{u}.obj V) V x (i.le hx) (uliftYonedaEquiv (𝟙 _))) =
      EtaleSpace.mk (F := uliftYoneda.{u}.obj V) x ((stalkFunctor (Type u) x).map
        (uliftYoneda.{u}.map i) (germ (uliftYoneda.{u}.obj U) U x hx (uliftYonedaEquiv (𝟙 _))))
    rw [stalkFunctor_map_germ_apply, ← germ_res_apply _ i x hx]
    congr 2

end Etale

section Colimit

variable (P : X.Presheaf (Type u))

/-- The cocone legs `ν_{U,u}` of `E = y † F(P)` over `y ↓ P`. -/
abbrev etaleExt : Functor.LeftExtension (uliftYoneda.{u} (C := Opens X)) (toOver X) :=
  Functor.LeftExtension.mk (etale X) (etaleUnit X)

theorem coconeAt_ι_app (j : CostructuredArrow uliftYoneda.{u} P) :
    ((etaleExt).coconeAt P).ι.app j = germHom P j.left (uliftYonedaEquiv j.hom) := by
  ext ⟨x, hx⟩
  change EtaleSpace.mk (F := P) x ((stalkFunctor (Type u) x).map j.hom
    (germ (uliftYoneda.{u}.obj j.left) j.left x hx (uliftYonedaEquiv (𝟙 _)))) = _
  rw [stalkFunctor_map_germ_apply]
  rfl

/-- A chosen section representing a germ. -/
structure Rep (g : EtaleSpace P) where
  /-- The open set. -/
  U : Opens X
  mem : g.base ∈ U
  /-- The section. -/
  s : P.obj (op U)
  eq : P.germ U g.base mem s = g.germ

theorem nonempty_rep (g : EtaleSpace P) : Nonempty (Rep P g) :=
  let ⟨U, h, s, e⟩ := P.exists_germ_eq g.germ
  ⟨⟨U, h, s, e⟩⟩

/-- The chosen representative. -/
def rep (g : EtaleSpace P) : Rep P g := Classical.choice (nonempty_rep P g)

theorem germMap_rep (g : EtaleSpace P) : germMap P (rep P g).U (rep P g).s ⟨g.base, (rep P g).mem⟩ = g := by
  obtain ⟨b, t⟩ := g
  exact congrArg (EtaleSpace.mk b) (rep P ⟨b, t⟩).eq

variable {P}

/-- The leg of a cocone at `⟨U, s⟩`. -/
def leg (c : Cocone (CostructuredArrow.proj uliftYoneda.{u} P ⋙ toOver X)) (U : Opens X)
    (s : P.obj (op U)) : (toOver X).obj U ⟶ c.pt :=
  c.ι.app (CostructuredArrow.mk (uliftYonedaEquiv.symm s))

theorem leg_eq (c : Cocone (CostructuredArrow.proj uliftYoneda.{u} P ⋙ toOver X))
    {U V : Opens X} {x : X} (hU : x ∈ U) (hV : x ∈ V) (s : P.obj (op U)) (t : P.obj (op V))
    (h : P.germ U x hU s = P.germ V x hV t) :
    (leg c U s).left ⟨x, hU⟩ = (leg c V t).left ⟨x, hV⟩ := by
  obtain ⟨W, hxW, i, j, e⟩ := P.germ_eq x hU hV s t h
  have key : ∀ {U : Opens X} (hU : x ∈ U) (i : W ⟶ U) (s : P.obj (op U)),
      (leg c U s).left ⟨x, hU⟩ = (leg c W (P.map i.op s)).left ⟨x, hxW⟩ := by
    intro U hU i s
    have := c.w (CostructuredArrow.homMk (S := uliftYoneda.{u})
      (f := CostructuredArrow.mk (uliftYonedaEquiv.symm (P.map i.op s)))
      (f' := CostructuredArrow.mk (uliftYonedaEquiv.symm s)) i
      (uliftYonedaEquiv_symm_map i.op s).symm)
    refine Eq.trans ?_ (congrArg (fun m ↦ m.left ⟨x, hxW⟩) this)
    rfl
  rw [key hU i s, key hV j t, e]

section Desc

variable {P : X.Presheaf (Type u)}
variable (c : Cocone (CostructuredArrow.proj uliftYoneda.{u} P ⋙ toOver X))

/-- The induced map `E → c.pt`: `u_x ↦ c_{U,u}(x)`. -/
def descFun (g : EtaleSpace P) : c.pt.left :=
  (leg c (rep P g).U (rep P g).s).left ⟨g.base, (rep P g).mem⟩

theorem descFun_germMap (U : Opens X) (s : P.obj (op U)) (x : U) :
    descFun c (germMap P U s x) = (leg c U s).left x :=
  leg_eq c _ x.2 _ _ ((rep P (germMap P U s x)).eq)

theorem descFun_eq_on {U : Opens X} {s : P.obj (op U)} {g : EtaleSpace P}
    (hg : g ∈ germSet P U s) : descFun c g = (leg c U s).left ⟨g.base, hg.1⟩ :=
  leg_eq c _ hg.1 _ _ ((rep P g).eq.trans hg.2)

theorem continuous_descFun : Continuous (descFun c) := by
  refine continuous_iff_continuousAt.2 fun g ↦ ?_
  let r := rep P g
  have hB : germSet P r.U r.s ∈ 𝓝 g := (isOpen_germSet P r.U r.s).mem_nhds ⟨r.mem, r.eq.symm⟩
  refine ContinuousOn.continuousAt ?_ hB
  rw [continuousOn_iff_continuous_domRestrict]
  have : (germSet P r.U r.s).domRestrict (descFun c) =
      fun g' ↦ (leg c r.U r.s).left ⟨g'.1.base, g'.2.1⟩ := funext fun g' ↦ descFun_eq_on c g'.2
  rw [this]
  exact (leg c r.U r.s).left.hom.continuous.comp
    (((EtaleSpace.continuous_base P).comp continuous_subtype_val).subtype_mk _)

/-- The induced morphism `E → c.pt` over `X`. -/
def desc : (etale X).obj P ⟶ c.pt :=
  Over.homMk (TopCat.ofHom ⟨descFun c, continuous_descFun c⟩) (by
    ext g
    change c.pt.hom (descFun c g) = g.base
    exact congrArg (fun φ ↦ φ ⟨g.base, (rep P g).mem⟩) (Over.w (leg c (rep P g).U (rep P g).s)))

theorem leg_hom (j : CostructuredArrow uliftYoneda.{u} P) :
    leg c j.left (uliftYonedaEquiv j.hom) = c.ι.app j := by
  obtain ⟨U, ⟨⟨⟩⟩, f⟩ := j
  simp only [leg]
  rw [uliftYonedaEquiv.symm_apply_apply]
  rfl

end Desc

variable (P : X.Presheaf (Type u))

/-- `E` with the legs `ν_{U,u}` is a colimit of `y ↓ P → O_X → Top/X`. -/
def etaleIsColimit : IsColimit ((etaleExt).coconeAt P) where
  desc c := desc c
  fac c j := by
    rw [coconeAt_ι_app, ← leg_hom c j]
    ext x
    exact descFun_germMap c _ _ x
  uniq c m hm := by
    ext g
    change m.left g = descFun c g
    rw [← germMap_rep P g, descFun_germMap]
    have := hm (CostructuredArrow.mk (uliftYonedaEquiv.symm (rep P g).s))
    rw [coconeAt_ι_app] at this
    simp only [CostructuredArrow.mk_left, CostructuredArrow.mk_hom_eq_self,
      Equiv.apply_symm_apply] at this
    exact congrArg (fun φ ↦ φ.left ⟨g.base, (rep P g).mem⟩) this

variable (X)

/-- `E` is a pointwise left Kan extension `y † F` of `F` along `y`. -/
def etaleIsPointwise : (etaleExt (X := X)).IsPointwiseLeftKanExtension :=
  fun P ↦ etaleIsColimit P

theorem etale_isLeftKanExtension : (etale X).IsLeftKanExtension (etaleUnit X) :=
  (etaleIsPointwise X).isLeftKanExtension

/-- The universal adjunction `y † F ⊣ F † y` with `y † F = E`. -/
def etaleAdj : etale X ⊣ Presheaf.restrictedULiftYoneda.{u} (toOver X) :=
  have := etale_isLeftKanExtension X
  Presheaf.uliftYonedaAdjunction.{0} (etale X) (etaleUnit X)

variable {X}

theorem etaleAdj_unit (U : Opens X) (s : P.obj (op U)) :
    (((etaleAdj X).unit.app P).app (op U) s).down = germHom P U s := by
  rw [etaleAdj, Presheaf.uliftYonedaAdjunction_unit_app_app]
  change germHom _ U _ ≫ (etale X).map _ = _
  rw [etale_map_germHom]
  congr 1
  simp [uliftYonedaEquiv]

end Colimit

section Unit

variable {P : X.Presheaf (Type u)}

theorem etaleUnit_app_map (U : Opens X) (s : P.obj (op U)) :
    (etaleUnit X).app U ≫ (etale X).map (uliftYonedaEquiv.symm s) = germHom P U s := by
  change germHom _ U _ ≫ (etale X).map _ = _
  rw [etale_map_germHom]
  congr 1
  simp [uliftYonedaEquiv]

/-- The counit of `y † F ⊣ F † y` sends the germ `(σ)_x` of a section `σ` of `f` to `σ(x)`. -/
theorem germHom_counit (f : Over X) (U : Opens X)
    (s : ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f).obj (op U)) :
    germHom _ U s ≫ (etaleAdj X).counit.app f = s.down := by
  have := etale_isLeftKanExtension X
  have h2 : (etaleAdj X).homEquiv _ f ((etaleAdj X).counit.app f) = 𝟙 _ := by
    rw [← (etaleAdj X).homEquiv_symm_id, Equiv.apply_symm_apply]
  have h3 := Presheaf.uliftYonedaAdjunction_homEquiv_app.{0} (L := etale X) (α := etaleUnit X)
    ((etaleAdj X).counit.app f) s
  have h4 : ((etaleAdj X).homEquiv _ f ((etaleAdj X).counit.app f)).app (op U) s = s := by
    rw [h2]
    rfl
  rw [← etaleUnit_app_map]
  exact congrArg ULift.down (h3.symm.trans h4)

theorem etaleMk_eq_of_mem {U : Opens X} {s : P.obj (op U)} {g : EtaleSpace P}
    (hg : g ∈ germSet P U s) : germMap P U s ⟨g.base, hg.1⟩ = g := by
  obtain ⟨b, t⟩ := g
  obtain ⟨h, e⟩ := hg
  exact congrArg (EtaleSpace.mk b) e.symm

theorem germMap_eq_of_mem {U : Opens X} {s : P.obj (op U)} {g : EtaleSpace P}
    (hg : g ∈ germSet P U s) {z : X} (hz : g.base = z) (hzU : z ∈ U) :
    germMap P U s ⟨z, hzU⟩ = g := by
  subst hz
  exact etaleMk_eq_of_mem hg

theorem germ_eq_of_germMap_eq {U V : Opens X} {s : P.obj (op U)} {t : P.obj (op V)} {x : X}
    (hU : x ∈ U) (hV : x ∈ V) (h : germMap P U s ⟨x, hU⟩ = germMap P V t ⟨x, hV⟩) :
    P.germ U x hU s = P.germ V x hV t := by
  simp only [germMap, EtaleSpace.mk.injEq, heq_eq_eq, true_and] at h
  exact h

end Unit

section Sheafify

variable (P : X.Presheaf (Type u))

/-- `η_P : P ⇒ F † y(y † F(P))`, the unit at `P` with its domain written as `P`. -/
def etaUnit : P ⟶ (Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj ((etale X).obj P) :=
  (etaleAdj X).unit.app P

theorem etaUnit_app (U : Opens X) (s : P.obj (op U)) :
    ((etaUnit P).app (op U) s).down = germHom P U s :=
  etaleAdj_unit P U s

theorem stalk_unit_injective (x : X) :
    Function.Injective ((stalkFunctor (Type u) x).map (etaUnit P)) := by
  intro t₁ t₂ h
  obtain ⟨U, hU, s, rfl⟩ := P.exists_germ_eq t₁
  obtain ⟨V, hV, t, rfl⟩ := P.exists_germ_eq t₂
  rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply] at h
  obtain ⟨W, hxW, i, j, e⟩ := germ_eq _ x hU hV _ _ h
  have e' := congrArg (fun φ ↦ (ULift.down φ).left ⟨x, hxW⟩) e
  change ((toOver X).map i ≫ ((etaUnit P).app (op U) s).down).left ⟨x, hxW⟩ =
    ((toOver X).map j ≫ ((etaUnit P).app (op V) t).down).left ⟨x, hxW⟩ at e'
  rw [etaUnit_app, etaUnit_app] at e'
  exact germ_eq_of_germMap_eq hU hV e'

theorem stalk_unit_surjective (x : X) :
    Function.Surjective ((stalkFunctor (Type u) x).map (etaUnit P)) := by
  intro t
  obtain ⟨V, hV, σ, rfl⟩ :=
    exists_germ_eq ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj ((etale X).obj P)) t
  have hbase : ∀ y : V, (σ.down.left y).base = y.1 := fun y ↦
    congrArg (fun φ ↦ φ y) (Over.w σ.down)
  let r := rep P (σ.down.left ⟨x, hV⟩)
  let N : Set V := σ.down.left ⁻¹' germSet P r.U r.s
  have hN : IsOpen N := (isOpen_germSet P r.U r.s).preimage σ.down.left.hom.continuous
  let W : Opens X := ⟨Subtype.val '' N, V.isOpen.isOpenMap_subtype_val N hN⟩
  have hxW : x ∈ W := ⟨⟨x, hV⟩, ⟨r.mem, r.eq.symm⟩, rfl⟩
  have hWV : W ≤ V := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hWU : W ≤ r.U := by
    rintro _ ⟨y, hy, rfl⟩
    exact hbase y ▸ hy.1
  refine ⟨P.germ r.U x (hWU hxW) r.s, ?_⟩
  rw [stalkFunctor_map_germ_apply]
  refine germ_ext _ W hxW (homOfLE hWU) (homOfLE hWV) ?_
  apply ULift.ext
  change (toOver X).map (homOfLE hWU) ≫ ((etaUnit P).app (op r.U) r.s).down =
    (toOver X).map (homOfLE hWV) ≫ σ.down
  rw [etaUnit_app]
  ext ⟨z, ⟨y, hy, rfl⟩⟩
  exact germMap_eq_of_mem hy (hbase y) _

/-- `ALGD-C2-SHEAF2-14` (命題 14, §3, p.10–11).
A presheaf `P` is a sheaf iff `η_P : P ⇒ F † y(y † F(P))` is an isomorphism. If `η_P` is an
isomorphism, `P` is isomorphic to a sheaf (命題 18). Conversely, `η_P` is a map of sheaves that is
bijective on every stalk, so it is an isomorphism; the source argues with gluing directly. -/
theorem isSheaf_iff_isIso_unit : P.IsSheaf ↔ IsIso (etaUnit P) := by
  constructor
  · intro hP
    let F : X.Sheaf (Type u) := ⟨P, hP⟩
    let G : X.Sheaf (Type u) := ⟨_, sections_isSheaf ((etale X).obj P)⟩
    let f : F ⟶ G := ObjectProperty.homMk (etaUnit P)
    have : ∀ x, IsIso ((stalkFunctor (Type u) x).map f.hom) := fun x ↦
      (isIso_iff_bijective _).2 ⟨stalk_unit_injective P x, stalk_unit_surjective P x⟩
    have := isIso_of_stalkFunctor_map_iso f
    exact (inferInstance : IsIso ((Sheaf.forget _ X).map f))
  · intro h
    exact isSheaf_of_iso (asIso (etaUnit P)).symm (sections_isSheaf _)

end Sheafify

section Bundles

/-- The germ sets form a basis of the topology of `E`. -/
theorem isTopologicalBasis_germSet (P : X.Presheaf (Type u)) :
    IsTopologicalBasis {S : Set (EtaleSpace P) | ∃ (U : Opens X) (s : P.obj (op U)),
      germSet P U s = S} where
  exists_subset_inter := by
    rintro _ ⟨U, s, rfl⟩ _ ⟨V, t, rfl⟩ g ⟨⟨hU, hs⟩, ⟨hV, ht⟩⟩
    obtain ⟨W, hxW, hWU, hWV, hW⟩ := eventually_germ_eq hU hV (hs.symm.trans ht)
    refine ⟨germSet P W (P.map (homOfLE hWU).op s), ⟨W, _, rfl⟩, ⟨hxW, ?_⟩, ?_⟩
    · rw [hs, germ_res_apply]
    · rintro g' ⟨hg'W, hg'⟩
      rw [germ_res_apply] at hg'
      exact ⟨⟨hWU hg'W, hg'⟩, ⟨hWV hg'W, hg'.trans (hW _ hg'W)⟩⟩
  sUnion_eq := Set.eq_univ_of_forall fun g ↦
    ⟨_, ⟨(rep P g).U, (rep P g).s, rfl⟩, (rep P g).mem, (rep P g).eq.symm⟩
  eq_generateFrom := rfl

/-- Condition (3) of 命題 16: every point has an open neighbourhood `O` with `f(O)` open and
`f|_O : O → f(O)` a homeomorphism. -/
def LocalHomeoCond (f : Over X) : Prop :=
  ∀ a : f.left, ∃ O : Set f.left, IsOpen O ∧ a ∈ O ∧ IsOpen (f.hom '' O) ∧
    ∃ e : O ≃ₜ (f.hom '' O), ∀ y : O, (e y : X) = f.hom y

theorem localHomeoCond_iff (f : Over X) : LocalHomeoCond f ↔ IsLocalHomeomorph f.hom := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  constructor
  · intro h a
    obtain ⟨O, hO, haO, hfO, e, he⟩ := h a
    refine ⟨O, hO.mem_nhds haO, ?_⟩
    have : O.domRestrict f.hom = Subtype.val ∘ e := funext fun y ↦ (he y).symm
    rw [this]
    exact hfO.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  · intro h a
    obtain ⟨U, hU, hemb⟩ := h a
    obtain ⟨O, hOU, hO, haO⟩ := mem_nhds_iff.1 hU
    have hemb' : IsOpenEmbedding (O.domRestrict f.hom) := by
      have : O.domRestrict f.hom = U.domRestrict f.hom ∘ Set.inclusion hOU := rfl
      rw [this]
      exact hemb.comp (IsOpenEmbedding.inclusion hOU (hO.preimage continuous_subtype_val))
    have hrange : Set.range (O.domRestrict f.hom) = f.hom '' O := Set.range_domRestrict _ _
    exact ⟨O, hO, haO, hrange ▸ hemb'.isOpen_range,
      hemb'.toIsEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange), fun _ ↦ rfl⟩

/-- `y † F(P) = E → X` satisfies condition (3): `germSet P U s → U` is a homeomorphism. -/
theorem etale_localHomeoCond (P : X.Presheaf (Type u)) : LocalHomeoCond ((etale X).obj P) := by
  intro g
  let r := rep P g
  have himg : ((etale X).obj P).hom '' germSet P r.U r.s = (r.U : Set X) := by
    ext x
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact hg'.1
    · intro hx
      exact ⟨germMap P r.U r.s ⟨x, hx⟩, ⟨hx, rfl⟩, rfl⟩
  let e₀ : germSet P r.U r.s ≃ₜ (r.U : Set X) :=
    { toFun := fun g' ↦ ⟨g'.1.base, g'.2.1⟩
      invFun := fun x ↦ ⟨germMap P r.U r.s x, x.2, rfl⟩
      left_inv := fun g' ↦ Subtype.ext (etaleMk_eq_of_mem g'.2)
      right_inv := fun _ ↦ rfl
      continuous_toFun :=
        ((EtaleSpace.continuous_base P).comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_germMap P r.U r.s).subtype_mk _ }
  exact ⟨germSet P r.U r.s, isOpen_germSet P r.U r.s, ⟨r.mem, r.eq.symm⟩,
    himg ▸ r.U.isOpen, e₀.trans (Homeomorph.setCongr himg.symm), fun _ ↦ rfl⟩

theorem injOn_of_homeomorph {f : Over X} {O : Set f.left} (e : O ≃ₜ (f.hom '' O))
    (he : ∀ y : O, (e y : X) = f.hom y) : Set.InjOn f.hom O := by
  intro b hb b' hb' h
  have : e ⟨b, hb⟩ = e ⟨b', hb'⟩ :=
    Subtype.ext ((he ⟨b, hb⟩).trans (h.trans (he ⟨b', hb'⟩).symm))
  exact congrArg Subtype.val (e.injective this)

theorem counit_apply (f : Over X) (U : Opens X)
    (s : ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f).obj (op U)) (x : U) :
    ((etaleAdj X).counit.app f).left (germMap _ U s x) = s.down.left x :=
  congrArg (fun φ ↦ φ.left x) (germHom_counit f U s)

/-- `ε_f` as a function `E_{F † y(f)} → Y`. -/
def epsFun (f : Over X) :
    EtaleSpace ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f) → f.left :=
  fun g ↦ ((etaleAdj X).counit.app f).left g

theorem epsFun_germMap (f : Over X) (U : Opens X)
    (s : ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f).obj (op U)) (x : U) :
    epsFun f (germMap _ U s x) = s.down.left x :=
  counit_apply f U s x

theorem section_base (f : Over X) {U : Opens X}
    (s : ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f).obj (op U)) (z : U) :
    f.hom (s.down.left z) = z.1 :=
  congrArg (fun φ ↦ φ z) (Over.w s.down)

theorem germMap_eq {P : X.Presheaf (Type u)} {U V : Opens X} {s : P.obj (op U)}
    {t : P.obj (op V)} {x y : X} (hU : x ∈ U) (hV : y ∈ V) (hxy : x = y)
    (h : P.germ U x hU s = P.germ V x (hxy ▸ hV) t) :
    germMap P U s ⟨x, hU⟩ = germMap P V t ⟨y, hV⟩ := by
  subst hxy
  exact congrArg (EtaleSpace.mk x) h

theorem germ_sections_eq (f : Over X) {U₁ U₂ W : Opens X}
    (s₁ : ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f).obj (op U₁))
    (s₂ : ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f).obj (op U₂))
    (h₁ : W ≤ U₁) (h₂ : W ≤ U₂) {x : X} (hxW : x ∈ W)
    (h : ∀ (z : X) (hz : z ∈ W), s₁.down.left ⟨z, h₁ hz⟩ = s₂.down.left ⟨z, h₂ hz⟩) :
    germ ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f) U₁ x (h₁ hxW) s₁ =
      germ ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f) U₂ x (h₂ hxW) s₂ := by
  refine germ_ext _ W hxW (homOfLE h₁) (homOfLE h₂) ?_
  apply ULift.ext
  change (toOver X).map (homOfLE h₁) ≫ s₁.down = (toOver X).map (homOfLE h₂) ≫ s₂.down
  ext ⟨z, hz⟩
  exact h z hz

/-- Under condition (3), `ε_f` is an isomorphism. -/
theorem isIso_counit_of_localHomeoCond (f : Over X) (hf : LocalHomeoCond f) :
    IsIso ((etaleAdj X).counit.app f) := by
  have hinj : Function.Injective (epsFun f) := by
    intro g₁ g₂ h
    rw [← germMap_rep _ g₁, ← germMap_rep _ g₂] at h ⊢
    rw [epsFun_germMap, epsFun_germMap] at h
    have hx : g₁.base = g₂.base := by
      have := congrArg f.hom h
      rwa [section_base, section_base] at this
    obtain ⟨O, hO, haO, -, e, he⟩ := hf ((rep _ g₁).s.down.left ⟨g₁.base, (rep _ g₁).mem⟩)
    have hinjO := injOn_of_homeomorph e he
    have haO' : (rep _ g₂).s.down.left ⟨g₂.base, (rep _ g₂).mem⟩ ∈ O := h ▸ haO
    let N₁ : Set X := Subtype.val '' ((rep _ g₁).s.down.left ⁻¹' O)
    let N₂ : Set X := Subtype.val '' ((rep _ g₂).s.down.left ⁻¹' O)
    have hN₁ : IsOpen N₁ := (rep _ g₁).U.isOpen.isOpenMap_subtype_val _
      (hO.preimage (rep _ g₁).s.down.left.hom.continuous)
    have hN₂ : IsOpen N₂ := (rep _ g₂).U.isOpen.isOpenMap_subtype_val _
      (hO.preimage (rep _ g₂).s.down.left.hom.continuous)
    let W : Opens X := ⟨N₁ ∩ N₂, hN₁.inter hN₂⟩
    have hxW : g₁.base ∈ W := ⟨⟨_, haO, rfl⟩, ⟨_, haO', hx.symm⟩⟩
    have hW₁ : W ≤ (rep _ g₁).U := by
      rintro _ ⟨⟨y, -, rfl⟩, -⟩
      exact y.2
    have hW₂ : W ≤ (rep _ g₂).U := by
      rintro _ ⟨-, ⟨y, -, rfl⟩⟩
      exact y.2
    refine germMap_eq _ _ hx (germ_sections_eq f _ _ hW₁ hW₂ hxW fun z hz ↦ ?_)
    obtain ⟨y₁, hy₁, hzy₁⟩ := hz.1
    obtain ⟨y₂, hy₂, hzy₂⟩ := hz.2
    have e₁ : y₁ = ⟨z, hW₁ hz⟩ := Subtype.ext hzy₁
    have e₂ : y₂ = ⟨z, hW₂ hz⟩ := Subtype.ext hzy₂
    rw [e₁] at hy₁
    rw [e₂] at hy₂
    exact hinjO hy₁ hy₂ ((section_base f _ ⟨z, hW₁ hz⟩).trans
      (section_base f _ ⟨z, hW₂ hz⟩).symm)
  have hsurj : Function.Surjective (epsFun f) := by
    intro a
    obtain ⟨O, hO, haO, hfO, e, he⟩ := hf a
    let V : Opens X := ⟨f.hom '' O, hfO⟩
    let σf : V → f.left := fun z ↦ (e.symm ⟨z.1, z.2⟩).1
    have hσf : Continuous σf := continuous_subtype_val.comp
      (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
    let σ : (toOver X).obj V ⟶ f := Over.homMk (TopCat.ofHom ⟨σf, hσf⟩) (by
        ext z
        change f.hom (e.symm ⟨z.1, z.2⟩).1 = z.1
        rw [← he (e.symm ⟨z.1, z.2⟩), e.apply_symm_apply])
    have hfa : f.hom a ∈ V := ⟨a, haO, rfl⟩
    let sσ : ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f).obj (op V) := ULift.up σ
    refine ⟨germMap _ V sσ ⟨f.hom a, hfa⟩, ?_⟩
    rw [epsFun_germMap]
    change (e.symm ⟨f.hom a, hfa⟩).1 = a
    have : e ⟨a, haO⟩ = ⟨f.hom a, hfa⟩ := Subtype.ext (he _)
    rw [← this, e.symm_apply_apply]
  have hopen : IsOpenMap (epsFun f) := by
    rw [(isTopologicalBasis_germSet _).isOpenMap_iff]
    rintro _ ⟨V, s, rfl⟩
    have himg : epsFun f '' germSet _ V s = Set.range s.down.left := by
      ext b
      constructor
      · rintro ⟨g, hg, rfl⟩
        rw [← etaleMk_eq_of_mem hg, epsFun_germMap]
        exact ⟨_, rfl⟩
      · rintro ⟨z, rfl⟩
        exact ⟨germMap _ V s z, ⟨z.2, rfl⟩, epsFun_germMap f V s z⟩
    rw [himg, isOpen_iff_forall_mem_open]
    rintro _ ⟨z₀, rfl⟩
    obtain ⟨O, hO, haO, -, e, he⟩ := hf (s.down.left z₀)
    have hinjO := injOn_of_homeomorph e he
    refine ⟨O ∩ f.hom ⁻¹' (Subtype.val '' (s.down.left ⁻¹' O)), ?_, ?_,
      ⟨haO, z₀, haO, (section_base f s z₀).symm⟩⟩
    · rintro c ⟨hcO, z, hzO, hz⟩
      exact ⟨z, hinjO hzO hcO ((section_base f s z).trans hz)⟩
    · exact hO.inter ((V.isOpen.isOpenMap_subtype_val _
        (hO.preimage s.down.left.hom.continuous)).preimage f.hom.hom.continuous)
  have : IsIso ((Over.forget X).map ((etaleAdj X).counit.app f)) :=
    TopCat.isIso_of_bijective_of_isOpenMap ((etaleAdj X).counit.app f).left ⟨hinj, hsurj⟩ hopen
  exact isIso_of_reflects_iso ((etaleAdj X).counit.app f) (Over.forget X)

end Bundles

section Equivalence

/-- `ALGD-C2-SHEAF2-D06` (prose, §3, p.11).
`f ∈ Top/X` is an étale bundle iff the counit `ε_f : y † F(F † y(f)) → f` is an isomorphism.
`Etale(X) ⊂ Top/X` is the full subcategory `EtaleBundles X`, and `Sh(X) ⊂ Ô_X` is mathlib's
`TopCat.Sheaf`, which is the full subcategory of sheaves. -/
def IsEtaleBundle (f : Over X) : Prop :=
  IsIso ((etaleAdj X).counit.app f)

variable (X) in
/-- `Etale(X) ⊂ Top/X`. -/
abbrev EtaleBundles : Type (u + 1) :=
  ObjectProperty.FullSubcategory (IsEtaleBundle (X := X))

/-- `ALGD-C2-SHEAF2-16` (命題 16, §3, p.12–14).
For a continuous `f : Y → X` the following are equivalent: (1) `f` is an étale bundle;
(2) `f ≅ y † F(P)` for some presheaf `P`; (3) every `a ∈ Y` has an open neighbourhood `O` such that
`f(O)` is open and `f|_O : O → f(O)` is a homeomorphism (`LocalHomeoCond`, which is mathlib's
`IsLocalHomeomorph` by `localHomeoCond_iff`). -/
theorem etale_tfae (f : Over X) :
    [IsEtaleBundle f, ∃ P : X.Presheaf (Type u), Nonempty ((etale X).obj P ≅ f),
      LocalHomeoCond f].TFAE := by
  tfae_have 1 → 2 := fun h ↦ by
    have : IsIso ((etaleAdj X).counit.app f) := h
    exact ⟨_, ⟨asIso ((etaleAdj X).counit.app f)⟩⟩
  tfae_have 2 → 3 := by
    rintro ⟨P, ⟨φ⟩⟩
    rw [localHomeoCond_iff]
    have hP := (localHomeoCond_iff _).1 (etale_localHomeoCond P)
    have : (f.hom : f.left → X) = ((etale X).obj P).hom ∘ φ.inv.left := by
      funext y
      exact (congrArg (fun m ↦ m y) (Over.w φ.inv)).symm
    rw [this]
    exact hP.comp (TopCat.homeoOfIso ((Over.forget X).mapIso φ.symm)).isLocalHomeomorph
  tfae_have 3 → 1 := isIso_counit_of_localHomeoCond f
  tfae_finish

theorem etale_isEtaleBundle (P : X.Presheaf (Type u)) : IsEtaleBundle ((etale X).obj P) :=
  isIso_counit_of_localHomeoCond _ (etale_localHomeoCond P)

variable (X) in
/-- `F † y` as a functor to sheaves (命題 18). -/
def sectionsSheaf : Over X ⥤ X.Sheaf (Type u) :=
  ObjectProperty.lift _ (Presheaf.restrictedULiftYoneda.{u} (toOver X)) sections_isSheaf

/-- `η_P` as an isomorphism for a sheaf `P` (命題 14). -/
def etaUnitIso (P : X.Sheaf (Type u)) :
    P.obj ≅ (Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj ((etale X).obj P.obj) :=
  have := (isSheaf_iff_isIso_unit P.obj).1 P.property
  asIso (etaUnit P.obj)

/-- `ε_f` as an isomorphism for an étale bundle `f`. -/
def counitIso (f : EtaleBundles X) :
    (etale X).obj ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f.obj) ≅ f.obj :=
  have : IsIso ((etaleAdj X).counit.app f.obj) := f.property
  asIso ((etaleAdj X).counit.app f.obj)

variable (X) in
/-- The equivalence `Sh(X) ≃ Etale(X)` of 定理 15. -/
def sheafEquivEtale : X.Sheaf (Type u) ≌ EtaleBundles X :=
  CategoryTheory.Equivalence.mk
    (ObjectProperty.lift _ (Sheaf.forget (Type u) X ⋙ etale X) fun P ↦ etale_isEtaleBundle P.obj)
    (ObjectProperty.ι _ ⋙ sectionsSheaf X)
    (NatIso.ofComponents
      (fun P ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso (etaUnitIso P))
      (fun {P Q} φ ↦ by
        apply CategoryTheory.Sheaf.hom_ext
        exact (etaleAdj X).unit.naturality φ.hom))
    (NatIso.ofComponents
      (fun f ↦ (ObjectProperty.fullyFaithfulι _).preimageIso (counitIso f))
      (fun {f g} φ ↦ by
        ext1
        exact (etaleAdj X).counit.naturality φ.hom))

end Equivalence

section Sheafification

variable (X) in
/-- `ALGD-C2-SHEAF2-D07` (prose, §4, p.15).
The sheafification functor `L := F † y ∘ y † F : Ô_X → Sh(X)`; `LP` is the sheafification
of `P`. -/
def sheafification : X.Presheaf (Type u) ⥤ X.Sheaf (Type u) :=
  etale X ⋙ sectionsSheaf X

variable (X) in
/-- `y † F` as a functor to étale bundles. -/
def etaleLift : X.Presheaf (Type u) ⥤ EtaleBundles X :=
  ObjectProperty.lift _ (etale X) etale_isEtaleBundle

variable (X) in
/-- `y † F ⊣ F † y` restricted to étale bundles. -/
def etaleLiftAdj :
    etaleLift X ⊣ ObjectProperty.ι _ ⋙ Presheaf.restrictedULiftYoneda.{u} (toOver X) :=
  (etaleAdj X).restrictFullyFaithful (iC := 𝟭 _) (iD := ObjectProperty.ι _)
    (Functor.FullyFaithful.id _) (ObjectProperty.fullyFaithfulι _) (Iso.refl _) (Iso.refl _)

variable (X) in
/-- `L ⊣ U` for the inclusion `U : Sh(X) → Ô_X`. -/
def sheafificationAdj : sheafification X ⊣ Sheaf.forget (Type u) X :=
  (((etaleLiftAdj X).comp (sheafEquivEtale X).symm.toAdjunction).ofNatIsoLeft
    (Iso.refl _)).ofNatIsoRight
    (NatIso.ofComponents (fun P ↦ (etaUnitIso P).symm) (fun {P Q} φ ↦ by
      have := (isSheaf_iff_isIso_unit P.obj).1 P.property
      have := (isSheaf_iff_isIso_unit Q.obj).1 Q.property
      change (Presheaf.restrictedULiftYoneda.{u} (toOver X)).map ((etale X).map φ.hom) ≫
          inv (etaUnit Q.obj) = inv (etaUnit P.obj) ≫ φ.hom
      rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
      exact ((etaleAdj X).unit.naturality φ.hom).symm))

/-- `ALGD-C2-SHEAF2-R10` (prose, §4, p.15, footnote 3).
`η_{F † y(f)}` is an isomorphism for every `f` (命題 14 and 命題 18), so `y † F ⊣ F † y` is
idempotent and `L = F † y ∘ y † F` is left adjoint to the inclusion `Sh(X) → Ô_X`.
`LP(U) ≅ {s ∈ Hom_Top(U, Λ_P) ∣ p ∘ s = F(U)}`, and `η_P` is an isomorphism when `P` is a sheaf.
Footnote 3: `(η_P)_U` need not be injective (constant `Bool`-valued presheaf at `U = ∅`). -/
theorem sheafification_spec :
    (∀ f : Over X, IsIso (etaUnit ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f))) ∧
    Nonempty (sheafification X ⊣ Sheaf.forget (Type u) X) ∧
    (∀ (P : X.Presheaf (Type u)) (U : Opens X),
      Nonempty (((sheafification X).obj P).obj.obj (op U) ≃
        {s : (Opens.toTopCat X).obj U ⟶ ((etale X).obj P).left //
          s ≫ ((etale X).obj P).hom = U.inclusion'})) ∧
    (∀ P : X.Presheaf (Type u), P.IsSheaf → IsIso (etaUnit P)) ∧
    ¬ ∀ (P : X.Presheaf (Type u)) (U : Opens X), Function.Injective ((etaUnit P).app (op U)) := by
  refine ⟨fun f ↦ (isSheaf_iff_isIso_unit _).1 (sections_isSheaf f), ⟨sheafificationAdj X⟩,
    fun P U ↦ ⟨sectionsEquiv _ U⟩, fun P hP ↦ (isSheaf_iff_isIso_unit P).1 hP, fun h ↦ ?_⟩
  let P : X.Presheaf (Type u) := (Functor.const _).obj (ULift.{u} Bool)
  have := @h P ⊥ (ULift.up true) (ULift.up false) (by
    apply ULift.ext
    apply Over.OverMorphism.ext
    ext ⟨z, hz⟩
    exact absurd hz (by simp))
  exact absurd (congrArg ULift.down this) (by decide)

end Sheafification

section Fibers

variable (X) in
/-- `ALGD-C2-SHEAF2-D05` (prose, §3, p.6).
`T_x : Top/X → Set` sends `f : Y → X` to the fibre `f⁻¹(x)`; `G_x := st_x ∘ y` is `stalkYoneda`. -/
def fiberFunctor (x : X) : Over X ⥤ Type u where
  obj f := {y : f.left // f.hom y = x}
  map {f g} φ := ↾fun y ↦ ⟨φ.left y.1, (congrArg (fun m ↦ m y.1) (Over.w φ)).trans y.2⟩

variable (X) in
/-- `G_x := st_x ∘ y`. -/
def stalkYoneda (x : X) : Opens X ⥤ Type u :=
  uliftYoneda.{u} ⋙ stalkFunctor (Type u) x

/-- The points `⟨t, b⟩` with `t ∈ X` and `b ∈ B` given only when `t = x`. -/
structure FiberRight (x : X) (B : Type u) where
  /-- The point of `X`. -/
  base : X
  /-- An element of `B` if `base = x`. -/
  val : base = x → B

instance (x : X) (B : Type u) : TopologicalSpace (FiberRight x B) :=
  TopologicalSpace.induced FiberRight.base inferInstance

theorem continuous_to_fiberRight (x : X) (B : Type u) {Y : Type*} [TopologicalSpace Y]
    (g : Y → FiberRight x B) (hg : Continuous fun y ↦ (g y).base) : Continuous g :=
  continuous_induced_rng.2 hg

/-- `FiberRight x B → X` as an object of `Top/X`. -/
def fiberRightObj (x : X) (B : Type u) : Over X :=
  Over.mk (Y := TopCat.of (FiberRight x B)) (TopCat.ofHom ⟨FiberRight.base, continuous_induced_dom⟩)

/-- The right adjoint of `T_x`. -/
def fiberRight (x : X) : Type u ⥤ Over X where
  obj B := fiberRightObj x B
  map {B B'} ψ := Over.homMk (TopCat.ofHom ⟨fun p : FiberRight x B ↦ ⟨p.base, fun h ↦ ψ (p.val h)⟩,
    continuous_to_fiberRight x B' _ continuous_induced_dom⟩) rfl

/-- `T_x ⊣ fiberRight x`, so `T_x` preserves colimits. -/
def fiberAdj (x : X) : fiberFunctor X x ⊣ fiberRight x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun f B ↦
        { toFun := fun φ ↦ Over.homMk (TopCat.ofHom
            ⟨fun y ↦ (⟨f.hom y, fun h ↦ φ ⟨y, h⟩⟩ : FiberRight x B),
              continuous_to_fiberRight x B _ f.hom.hom.continuous⟩) rfl
          invFun := fun ψ ↦ ↾fun y ↦ (ψ.left y.1 : FiberRight x B).val
            ((congrArg (fun m ↦ m y.1) (Over.w ψ)).trans y.2)
          left_inv := fun φ ↦ rfl
          right_inv := fun ψ ↦ by
            ext y
            have ht : (ψ.left y : FiberRight x B).base = f.hom y :=
              congrArg (fun m ↦ m y) (Over.w ψ)
            change (⟨f.hom y, fun h ↦ (ψ.left y : FiberRight x B).val (ht.trans h)⟩ :
              FiberRight x B) = ψ.left y
            generalize (ψ.left y : FiberRight x B) = q at ht ⊢
            obtain ⟨t, φ⟩ := q
            change t = f.hom y at ht
            subst ht
            rfl }
      homEquiv_naturality_left_symm := fun _ _ ↦ rfl
      homEquiv_naturality_right := fun _ _ ↦ rfl }

/-- The isomorphism `st_x ≅ T_x ∘ y † F` of 命題 12, `P_x ∋ t ↦ ⟨x, t⟩`. -/
def stalkIsoFiber (x : X) : stalkFunctor (Type u) x ≅ etale X ⋙ fiberFunctor X x :=
  NatIso.ofComponents (fun P ↦ Equiv.toIso
    { toFun := fun t ↦ ⟨⟨x, t⟩, rfl⟩
      invFun := fun g ↦ (g.2 : g.1.base = x) ▸ g.1.germ
      left_inv := fun _ ↦ rfl
      right_inv := by
        rintro ⟨⟨b, t⟩, h⟩
        change b = x at h
        subst h
        rfl })
    (fun θ ↦ rfl)

/-- `ALGD-C2-SHEAF2-12` (命題 12, §3, p.6).
`st_x ≅ T_x ∘ y † F`: the stalk `P_x` is the fibre of `Λ_P → X` over `x`. The source obtains the
isomorphism from the universal property of `y † G_x`; here it is `t ↦ ⟨x, t⟩`. -/
theorem stalk_iso_fiber (x : X) :
    Nonempty (stalkFunctor (Type u) x ≅ etale X ⋙ fiberFunctor X x) :=
  ⟨stalkIsoFiber x⟩

/-- `ALGD-C2-SHEAF2-15` (定理 15, §3, p.11).
`Sh(X) ≃ Etale(X)`, by the general theory of adjunctions: on sheaves `η` is an isomorphism
(命題 14), and on étale bundles `ε` is one by definition. A sheaf `P` corresponds to the étale
bundle `f = y † F(P)`, with `P ≅ F † y(f)` (so `P(U)` is the set of sections of `f`, by (11)) and
`f⁻¹(x) ≅ P_x` (命題 12). -/
theorem sheaf_equiv_etale :
    Nonempty (X.Sheaf (Type u) ≌ EtaleBundles X) ∧
    (∀ P : X.Sheaf (Type u), Nonempty (P.obj ≅
      (Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj ((etale X).obj P.obj))) ∧
    ∀ (P : X.Sheaf (Type u)) (x : X),
      Nonempty ((fiberFunctor X x).obj ((etale X).obj P.obj) ≃ stalk P.obj x) :=
  ⟨⟨sheafEquivEtale X⟩, fun P ↦ ⟨etaUnitIso P⟩,
    fun P x ↦ ⟨((stalkIsoFiber x).app P.obj).toEquiv.symm⟩⟩

end Fibers

section Statements

open Functor

/-- `ALGD-C2-SHEAF2-R07` (prose, §3, p.6).
`T_x` preserves colimits (it has a right adjoint), so `⟨T_x ∘ y † F, T_x ξ⟩` is a pointwise left Kan
extension of `T_x ∘ F` along `y` (定理 1). `⟨st_x, id⟩` is a pointwise left Kan extension of
`G_x = st_x ∘ y` along `y`, because `y` is dense (系 5) and `st_x` preserves colimits. -/
theorem fiber_kanExtensions (x : X) :
    PreservesColimitsOfSize.{u, u} (fiberFunctor X x) ∧
    Nonempty (LeftExtension.mk (etale X ⋙ fiberFunctor X x)
      (whiskerRight (etaleUnit X) (fiberFunctor X x) ≫
        (Functor.associator _ _ _).hom)).IsPointwiseLeftKanExtension ∧
    Nonempty (LeftExtension.mk (stalkFunctor (Type u) x)
      (𝟙 (stalkYoneda X x) : stalkYoneda X x ⟶ uliftYoneda.{u} ⋙ stalkFunctor (Type u) x)
      ).IsPointwiseLeftKanExtension := by
  have hpres : PreservesColimitsOfSize.{u, u} (fiberFunctor X x) :=
    (fiberAdj x).leftAdjoint_preservesColimits
  refine ⟨hpres, ⟨?_⟩, ⟨?_⟩⟩
  · exact LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
      (LeftExtension.postcompose₂ObjMkIso (fiberFunctor X x) (etaleUnit X))
      ((etaleIsPointwise X).postcompose (fiberFunctor X x))
  · have h₀ := ((isDense_iff_nonempty_isPointwiseLeftKanExtension
      (uliftYoneda.{u} (C := Opens X))).1 inferInstance).some
    have h₁ := LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
      (LeftExtension.postcompose₂ObjMkIso (stalkFunctor (Type u) x)
        (Functor.rightUnitor (uliftYoneda.{u} (C := Opens X))).inv)
      (h₀.postcompose (stalkFunctor (Type u) x))
    refine LeftExtension.isPointwiseLeftKanExtensionEquivOfIso ?_ h₁
    exact StructuredArrow.isoMk (Functor.leftUnitor _) (by ext; simp; rfl)

variable {L' : X.Presheaf (Type u) ⥤ Over X} {α' : toOver X ⟶ uliftYoneda.{u} ⋙ L'}

/-- `ALGD-C2-SHEAF2-R06` (prose, §3, p.5).
For any pointwise left Kan extension `⟨L', α'⟩ = y † F`, `L'(P) ≅ colim_{⟨U,u⟩ ∈ y ↓ P} F(U)`; the
projection `K : Top/X → Top` preserves colimits, so `Λ_P = K(L'(P)) ≅ colim U` in `Top`; and the
legs `μ_{⟨U,u⟩} = K(β_{⟨U,u⟩})` satisfy `p ∘ μ_{⟨U,u⟩} = F(U)`. -/
theorem lan_colimit_spec (h : (LeftExtension.mk L' α').IsPointwiseLeftKanExtension)
    (P : X.Presheaf (Type u)) :
    Nonempty (L'.obj P ≅ colimit (CostructuredArrow.proj uliftYoneda.{u} P ⋙ toOver X)) ∧
    Nonempty ((L'.obj P).left ≅
      colimit (CostructuredArrow.proj uliftYoneda.{u} P ⋙ toOver X ⋙ Over.forget X)) ∧
    ∀ j, (((LeftExtension.mk L' α').coconeAt P).ι.app j).left ≫ (L'.obj P).hom =
      ((toOver X).obj j.left).hom :=
  ⟨⟨(h P).coconePointUniqueUpToIso (colimit.isColimit _)⟩,
    ⟨(isColimitOfPreserves (Over.forget X) (h P)).coconePointUniqueUpToIso
      (colimit.isColimit _)⟩, fun _ ↦ Over.w _⟩

/-- The legs `μ_{U,s}` of `y † F(P)`. -/
abbrev muLeg (P : X.Presheaf (Type u)) (U : Opens X) (s : P.obj (op U)) :
    (toOver X).obj U ⟶ L'.obj P :=
  ((LeftExtension.mk L' α').coconeAt P).ι.app (CostructuredArrow.mk (uliftYonedaEquiv.symm s))

theorem germHom_eq_leg (P : X.Presheaf (Type u)) (U : Opens X) (s : P.obj (op U)) :
    germHom P U s =
      ((etaleExt).coconeAt P).ι.app (CostructuredArrow.mk (uliftYonedaEquiv.symm s)) := by
  rw [coconeAt_ι_app]
  simp only [CostructuredArrow.mk_left, CostructuredArrow.mk_hom_eq_self, Equiv.apply_symm_apply]

theorem etale_iso_leg (h : (LeftExtension.mk L' α').IsPointwiseLeftKanExtension)
    (P : X.Presheaf (Type u)) (U : Opens X) (s : P.obj (op U)) :
    germHom P U s ≫ ((etaleIsColimit P).coconePointUniqueUpToIso (h P)).hom =
      muLeg (α' := α') P U s := by
  rw [germHom_eq_leg]
  exact (etaleIsColimit P).comp_coconePointUniqueUpToIso_hom (h P) _

/-- `ALGD-C2-SHEAF2-R08` (prose, §3, p.6–7).
For any pointwise left Kan extension `y † F`, there is a bijection `h : E = ∐_x P_x → Λ_P`
(mathlib's `EtaleSpace P` is `E`) with `h(u_x) = μ_{⟨U,u⟩}(x)` and `p ∘ h = q`. -/
theorem lan_bijection (h : (LeftExtension.mk L' α').IsPointwiseLeftKanExtension)
    (P : X.Presheaf (Type u)) :
    ∃ e : EtaleSpace P ≃ (L'.obj P).left,
      (∀ (U : Opens X) (s : P.obj (op U)) (x : U),
        e (germMap P U s x) = (muLeg (α' := α') P U s).left x) ∧
      ∀ g, (L'.obj P).hom (e g) = g.base := by
  let φ := (etaleIsColimit P).coconePointUniqueUpToIso (h P)
  refine ⟨(TopCat.homeoOfIso ((Over.forget X).mapIso φ)).toEquiv, fun U s x ↦ ?_,
    fun g ↦ congrArg (fun m ↦ m g) (Over.w φ.hom)⟩
  exact congrArg (fun m ↦ m.left x) (etale_iso_leg h P U s)

theorem germMap_image (P : X.Presheaf (Type u)) {U V : Opens X} (hVU : V ≤ U)
    (s : P.obj (op U)) :
    germMap P U s '' {x | x.1 ∈ V} = germSet P V (P.map (homOfLE hVU).op s) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨hx, ?_⟩
    exact (germ_res_apply P (homOfLE hVU) x.1 hx s).symm
  · rintro ⟨hg, e⟩
    refine ⟨⟨g.base, hVU hg⟩, hg, ?_⟩
    exact germMap_eq_of_mem ⟨hVU hg, e.trans (germ_res_apply P (homOfLE hVU) g.base hg s)⟩
      rfl _

theorem etale_topology_eq (P : X.Presheaf (Type u)) :
    (inferInstance : TopologicalSpace (EtaleSpace P)) =
      TopologicalSpace.generateFrom {S | ∃ (U V : Opens X) (s : P.obj (op U)), V ≤ U ∧
        germMap P U s '' {x | x.1 ∈ V} = S} := by
  apply le_antisymm
  · refine le_generateFrom fun S ⟨U, V, s, hVU, hS⟩ ↦ ?_
    rw [← hS, germMap_image P hVU]
    exact isOpen_germSet _ _ _
  · refine TopologicalSpace.generateFrom_anti fun S ⟨U, s, hS⟩ ↦ ⟨U, U, s, le_rfl, ?_⟩
    rw [← hS, germMap_image P le_rfl]
    congr
    simp

theorem topology_eq_of_homeomorph {A B : Type*} [tA : TopologicalSpace A]
    [tB : TopologicalSpace B] (e : A ≃ₜ B) {S : Set (Set A)} (hS : tA = .generateFrom S) :
    tB = .generateFrom ((fun s ↦ e '' s) '' S) := by
  refine e.symm.isInducing.eq_induced.trans
    ((congrArg (TopologicalSpace.induced e.symm) hS).trans (induced_generateFrom_eq.trans ?_))
  congr 1
  ext T
  simp only [Set.mem_image]
  exact ⟨fun ⟨s, hs, h⟩ ↦ ⟨s, hs, by rw [← h, e.image_eq_preimage_symm]⟩,
    fun ⟨s, hs, h⟩ ↦ ⟨s, hs, by rw [← h, e.image_eq_preimage_symm]⟩⟩

/-- `ALGD-C2-SHEAF2-R09` (prose, §3, p.7–9).
The topology of `E` (mathlib's, generated by the germ sets) is generated by the sets
`ν_{⟨U,u⟩}(V)`, `V ⊆ U` open; `h : E → Λ_P` is a homeomorphism; and the topology of `Λ_P` is
generated by the sets `μ_{⟨U,u⟩}(V)`. -/
theorem lan_homeomorph (h : (LeftExtension.mk L' α').IsPointwiseLeftKanExtension)
    (P : X.Presheaf (Type u)) :
    (inferInstance : TopologicalSpace (EtaleSpace P)) =
      TopologicalSpace.generateFrom {S | ∃ (U V : Opens X) (s : P.obj (op U)), V ≤ U ∧
        germMap P U s '' {x | x.1 ∈ V} = S} ∧
    (∃ e : EtaleSpace P ≃ₜ (L'.obj P).left, ∀ (U : Opens X) (s : P.obj (op U)) (x : U),
        e (germMap P U s x) = (muLeg (α' := α') P U s).left x) ∧
    (inferInstance : TopologicalSpace (L'.obj P).left) =
      TopologicalSpace.generateFrom {S | ∃ (U V : Opens X) (s : P.obj (op U)), V ≤ U ∧
        (muLeg (α' := α') P U s).left '' {x | x.1 ∈ V} = S} := by
  let φ := (etaleIsColimit P).coconePointUniqueUpToIso (h P)
  let e := TopCat.homeoOfIso ((Over.forget X).mapIso φ)
  have he : ∀ (U : Opens X) (s : P.obj (op U)) (x : U),
      e (germMap P U s x) = (muLeg (α' := α') P U s).left x :=
    fun U s x ↦ congrArg (fun m ↦ m.left x) (etale_iso_leg h P U s)
  have himg : ∀ (U : Opens X) (s : P.obj (op U)) (A : Set U),
      e '' (germMap P U s '' A) = (muLeg (α' := α') P U s).left '' A := by
    intro U s A
    ext b
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (he U s x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, he U s x⟩
  refine ⟨etale_topology_eq P, ⟨e, he⟩, ?_⟩
  refine (topology_eq_of_homeomorph e (etale_topology_eq P)).trans ?_
  congr 1
  ext S
  constructor
  · rintro ⟨_, ⟨U, V, s, hVU, rfl⟩, rfl⟩
    exact ⟨U, V, s, hVU, (himg U s _).symm⟩
  · rintro ⟨U, V, s, hVU, rfl⟩
    exact ⟨_, ⟨U, V, s, hVU, rfl⟩, himg U s _⟩

/-- `ALGD-C2-SHEAF2-13` (命題 13, §3, p.9–10).
For the unit `η` of `y † F ⊣ F † y` and `u ∈ P(U)`, `(η_P)_U(u) = μ_{⟨U,u⟩}`, so
`(η_P)_U(u)(x) = u_x` for `x ∈ U`. Here `y † F = E` with legs `ν = μ`. -/
theorem unit_eq_leg (P : X.Presheaf (Type u)) (U : Opens X) (s : P.obj (op U)) :
    ((etaUnit P).app (op U) s).down =
        ((etaleExt).coconeAt P).ι.app (CostructuredArrow.mk (uliftYonedaEquiv.symm s)) ∧
      ∀ x : U, ((etaUnit P).app (op U) s).down.left x = ⟨x.1, P.germ U x.1 x.2 s⟩ := by
  rw [etaUnit_app, coconeAt_ι_app]
  simp only [CostructuredArrow.mk_left, CostructuredArrow.mk_hom_eq_self, Equiv.apply_symm_apply]
  exact ⟨rfl, fun _ ↦ rfl⟩

/-- `ALGD-C2-SHEAF2-17` (diagram (17), proof of 命題 16, p.13).
For a section `s : F(U) → f` (an element of `F † y(f)(U)`, corresponding to `u^s : y(U) ⇒ F † y(f)`),
`ε_f ∘ μ_{⟨U,u^s⟩} = s`, so `s(x) = ε_f(u^s_x)` for `x ∈ U`. -/
theorem counit_leg (f : Over X) (U : Opens X)
    (s : ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f).obj (op U)) :
    ((etaleExt).coconeAt _).ι.app (CostructuredArrow.mk (uliftYonedaEquiv.symm s)) ≫
        (etaleAdj X).counit.app f = s.down ∧
      ∀ x : U, ((etaleAdj X).counit.app f).left (germMap _ U s x) = s.down.left x := by
  rw [coconeAt_ι_app]
  simp only [CostructuredArrow.mk_left, CostructuredArrow.mk_hom_eq_self, Equiv.apply_symm_apply]
  exact ⟨germHom_counit f U s, counit_apply f U s⟩

end Statements

section Constant

variable (A : Type u)

/-- The constant presheaf `ΔA`. -/
abbrev constPresheaf : X.Presheaf (Type u) := (Functor.const (Opens X)ᵒᵖ).obj A

theorem germ_const {U : Opens X} {x : X} (hx : x ∈ U) (a : A) :
    germ (constPresheaf (X := X) A) U x hx a = germ (constPresheaf A) ⊤ x trivial a :=
  germ_res_apply (constPresheaf (X := X) A) (homOfLE le_top) x hx a

theorem germ_const_bijective (x : X) :
    Function.Bijective (germ (constPresheaf (X := X) A) ⊤ x trivial) := by
  refine ⟨fun a b h ↦ ?_, fun t ↦ ?_⟩
  · obtain ⟨W, -, i, j, e⟩ := germ_eq (constPresheaf (X := X) A) (U := ⊤) (V := ⊤) x _root_.trivial _root_.trivial a b h
    exact e
  · obtain ⟨U, hU, a, rfl⟩ := exists_germ_eq (constPresheaf (X := X) A) t
    exact ⟨a, (germ_const A hU a).symm⟩

/-- The value of a germ of `ΔA`. -/
def constValue (g : EtaleSpace (constPresheaf (X := X) A)) : A :=
  (Equiv.ofBijective _ (germ_const_bijective A g.base)).symm g.germ

theorem constValue_spec (g : EtaleSpace (constPresheaf (X := X) A)) :
    germ (constPresheaf A) ⊤ g.base trivial (constValue A g) = g.germ :=
  (Equiv.ofBijective _ (germ_const_bijective A g.base)).apply_symm_apply g.germ

theorem constValue_eq_of_mem {U : Opens X} {a : A} {g : EtaleSpace (constPresheaf (X := X) A)}
    (hg : g ∈ germSet _ U a) : constValue A g = a :=
  (germ_const_bijective A g.base).1 ((constValue_spec A g).trans (hg.2.trans (germ_const A _ a)))

/-- `Λ_{ΔA} ≅ A × X` for discrete `A`. -/
def constEtaleHomeo [TopologicalSpace A] [DiscreteTopology A] :
    EtaleSpace (constPresheaf (X := X) A) ≃ₜ A × X where
  toFun g := (constValue A g, g.base)
  invFun p := ⟨p.2, germ (constPresheaf A) ⊤ p.2 trivial p.1⟩
  left_inv g := by
    obtain ⟨b, t⟩ := g
    exact congrArg (EtaleSpace.mk b) (constValue_spec A ⟨b, t⟩)
  right_inv p := by
    refine Prod.ext ((germ_const_bijective A p.2).1 ?_) rfl
    exact constValue_spec A ⟨p.2, _⟩
  continuous_toFun := by
    refine .prodMk ?_ (EtaleSpace.continuous_base _)
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g ↦ ?_)
    obtain ⟨U, hU, a, ha⟩ := exists_germ_eq (constPresheaf (X := X) A) g.germ
    exact ⟨germSet _ U a, isOpen_germSet _ _ _, ⟨hU, ha.symm⟩, fun g' hg' ↦
      (constValue_eq_of_mem A hg').trans (constValue_eq_of_mem A ⟨hU, ha.symm⟩).symm⟩
  continuous_invFun := by
    refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨U, a, rfl⟩
    have : (fun p : A × X ↦ (⟨p.2, germ (constPresheaf A) ⊤ p.2 trivial p.1⟩ :
        EtaleSpace (constPresheaf (X := X) A))) ⁻¹' germSet _ U a = {a} ×ˢ (U : Set X) := by
      ext ⟨b, x⟩
      simp only [Set.mem_preimage, germSet, Set.mem_ofPred_eq, Set.mem_prod,
        Set.mem_singleton_iff, SetLike.mem_coe]
      constructor
      · rintro ⟨hx, h⟩
        exact ⟨(germ_const_bijective A x).1 (h.trans (germ_const A hx a)), hx⟩
      · rintro ⟨rfl, hx⟩
        exact ⟨hx, (germ_const A hx b).symm⟩
    change IsOpen (_ ⁻¹' germSet _ U a)
    rw [this]
    exact (isOpen_discrete ({a} : Set A)).prod U.isOpen

/-- Sections of `Λ_{ΔA} → X` are the locally constant maps `U → A` (condition (22)). -/
def constSectionsEquiv (U : Opens X) :
    {s : (Opens.toTopCat X).obj U ⟶ ((etale X).obj (constPresheaf A)).left //
        s ≫ ((etale X).obj (constPresheaf A)).hom = U.inclusion'} ≃
      {k : U → A // ∀ x : U, ∃ V : Opens X, x.1 ∈ V ∧ V ≤ U ∧ ∀ y : U, y.1 ∈ V → k y = k x} :=
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  let e := constEtaleHomeo (X := X) A
  { toFun := fun s ↦ ⟨fun x ↦ constValue A (s.1 x), (locallyConstant_iff _).2
      (continuous_fst.comp (e.continuous.comp s.1.hom.continuous))⟩
    invFun := fun k ↦ ⟨TopCat.ofHom ⟨fun x ↦ e.symm (k.1 x, x.1),
        e.symm.continuous.comp (((locallyConstant_iff k.1).1 k.2).prodMk
          continuous_subtype_val)⟩, rfl⟩
    left_inv := fun s ↦ by
      apply Subtype.ext
      ext x
      have hx : (s.1 x).base = x.1 := congrArg (fun m ↦ m x) s.2
      change e.symm (constValue A (s.1 x), x.1) = s.1 x
      rw [← hx]
      exact e.symm_apply_apply (s.1 x)
    right_inv := fun k ↦ by
      apply Subtype.ext
      funext x
      exact congrArg Prod.fst (e.apply_symm_apply (k.1 x, x.1)) }

/-- `ALGD-C2-SHEAF2-21` (例 21, §4, p.16–17).
The constant presheaf `ΔA`: `Δ ⊣ lim`; `lim P ≅ P(X)` since `X` is initial in `O_X^op`;
`L ∘ Δ ⊣ Γ` with `Γ(Q) = Q(X)` the global section functor; `(ΔA)_x ≅ A` by `a ↦ a_x`;
`Λ_{ΔA} ≅ A × X` over `X` for discrete `A`; and `LΔA(U)` is the set of maps `k : U → A`
satisfying (22), so the constant sheaf is the sheaf of locally constant functions. -/
theorem constant_sheaf :
    Nonempty ((Functor.const (Opens X)ᵒᵖ : Type u ⥤ X.Presheaf (Type u)) ⊣ lim) ∧
    (∀ Q : X.Presheaf (Type u), Nonempty (limit Q ≅ Q.obj (op ⊤))) ∧
    Nonempty ((Functor.const (Opens X)ᵒᵖ ⋙ sheafification X) ⊣
      (Sheaf.forget (Type u) X ⋙ (evaluation _ _).obj (op ⊤))) ∧
    (∀ x : X, Function.Bijective (germ (constPresheaf (X := X) A) ⊤ x _root_.trivial)) ∧
    (∀ [TopologicalSpace A] [DiscreteTopology A],
      ∃ e : ((etale X).obj (constPresheaf A)).left ≃ₜ A × X,
        ∀ g, (e g).2 = ((etale X).obj (constPresheaf A)).hom g) ∧
    ∀ U : Opens X, Nonempty (((sheafification X).obj (constPresheaf A)).obj.obj (op U) ≃
      {k : U → A // ∀ x : U, ∃ V : Opens X, x.1 ∈ V ∧ V ≤ U ∧ ∀ y : U, y.1 ∈ V → k y = k x}) :=
  ⟨⟨constLimAdj⟩, fun Q ↦ ⟨(limit.isLimit Q).conePointUniqueUpToIso
      (limitOfDiagramInitial (isTerminalTop (α := Opens X)).op Q)⟩,
    ⟨(constantPresheafAdj (Type u) (isTerminalTop (α := Opens X))).comp (sheafificationAdj X)⟩,
    germ_const_bijective A, fun {_ _} ↦ ⟨constEtaleHomeo A, fun _ ↦ rfl⟩,
    fun U ↦ ⟨(sectionsEquiv _ U).trans (constSectionsEquiv A U)⟩⟩

end Constant

section Covering

/-- The source's definition of a covering map (定義, p.17): every `z` has an open neighbourhood
`U` and a family of pairwise disjoint open sets `V i` with `f⁻¹(U) = ⋃ V i` and each
`f|_{V i} : V i → U` a homeomorphism. -/
def IsCoveringMapSrc {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] (f : Y → Z) :
    Prop :=
  ∀ z : Z, ∃ U : Set Z, z ∈ U ∧ IsOpen U ∧ ∃ (I : Type u) (V : I → Set Y),
    (∀ i, IsOpen (V i)) ∧ Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧ f ⁻¹' U = ⋃ i, V i ∧
      ∀ i, ∃ e : V i ≃ₜ U, ∀ y, (e y : Z) = f y

/-- `ALGD-C2-SHEAF2-D10` (定義, §4, p.17).
A continuous map is a covering map in the source's sense (`IsCoveringMapSrc`) iff it is one in
mathlib's sense (`IsCoveringMap`: every point has an evenly covered neighbourhood with discrete
fibre). -/
theorem isCoveringMapSrc_iff {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : Y → Z) (hf : Continuous f) : IsCoveringMapSrc f ↔ IsCoveringMap f := by
  constructor
  · intro h z
    obtain ⟨U, hzU, hU, I, V, hV, hdisj, hcov, he⟩ := h z
    choose e he using he
    let _ : TopologicalSpace I := ⊥
    have : DiscreteTopology I := ⟨rfl⟩
    have hmem : ∀ y : f ⁻¹' U, ∃ i, y.1 ∈ V i := fun y ↦ Set.mem_iUnion.1 (hcov ▸ y.2)
    choose idx hidx using hmem
    have idx_eq : ∀ (y : f ⁻¹' U) (i : I), y.1 ∈ V i → idx y = i := fun y i hy ↦ by
      by_contra hne
      exact Set.disjoint_left.1 (hdisj hne) (hidx y) hy
    have hfU : IsOpen (f ⁻¹' U) := hcov ▸ isOpen_iUnion hV
    refine IsEvenlyCovered.to_isEvenlyCovered_preimage (I := I) ⟨inferInstance, U, hzU, hU, hfU,
      { toFun := fun y ↦ (⟨f y, y.2⟩, idx y)
        invFun := fun p ↦ ⟨(e p.2 |>.symm p.1).1, by
          rw [hcov]
          exact Set.mem_iUnion.2 ⟨p.2, (e p.2 |>.symm p.1).2⟩⟩
        left_inv := fun y ↦ by
          apply Subtype.ext
          change ((e (idx y)).symm ⟨f y, y.2⟩).1 = y.1
          have : e (idx y) ⟨y.1, hidx y⟩ = ⟨f y, y.2⟩ := Subtype.ext (he _ _)
          rw [← this, Homeomorph.symm_apply_apply]
        right_inv := fun p ↦ by
          obtain ⟨u, i⟩ := p
          have h1 : f ((e i).symm u).1 = u.1 := by
            rw [← he i, Homeomorph.apply_symm_apply]
          refine Prod.ext (Subtype.ext h1) ?_
          exact idx_eq _ i ((e i).symm u).2
        continuous_toFun := by
          refine .prodMk ((hf.comp continuous_subtype_val).subtype_mk _) ?_
          refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun y ↦ ?_)
          refine ⟨Subtype.val ⁻¹' V (idx y), (hV _).preimage continuous_subtype_val, hidx y,
            fun y' hy' ↦ idx_eq y' _ hy'⟩
        continuous_invFun := by
          refine continuous_prod_of_discrete_right.2 fun i ↦ ?_
          exact ((continuous_subtype_val.comp (e i).symm.continuous)).subtype_mk _ },
      fun _ ↦ rfl⟩
  · intro h z
    obtain ⟨hdisc, U, hzU, hU, hfU, H, hH⟩ := h z
    let V : f ⁻¹' {z} → Set Y := fun i ↦ {y | ∃ hy : f y ∈ U, (H ⟨y, hy⟩).2 = i}
    have hV : ∀ i, V i = Subtype.val '' ((fun y ↦ (H y).2) ⁻¹' {i}) := fun i ↦ by
      ext y
      exact ⟨fun ⟨hy, e⟩ ↦ ⟨⟨y, hy⟩, e, rfl⟩, fun ⟨y', e, hy'⟩ ↦ hy' ▸ ⟨y'.2, e⟩⟩
    refine ⟨U, hzU, hU, f ⁻¹' {z}, V, fun i ↦ ?_, fun i j hij ↦ ?_, ?_, fun i ↦ ?_⟩
    · rw [hV]
      exact hfU.isOpenMap_subtype_val _ ((isOpen_discrete {i}).preimage
        (continuous_snd.comp H.continuous))
    · refine Set.disjoint_left.2 ?_
      rintro y ⟨hy, e⟩ ⟨hy', e'⟩
      exact hij (e.symm.trans e')
    · ext y
      simp only [Set.mem_preimage, Set.mem_iUnion]
      exact ⟨fun hy ↦ ⟨(H ⟨y, hy⟩).2, hy, rfl⟩, fun ⟨_, hy, _⟩ ↦ hy⟩
    · have hsymm : ∀ u : U, f (H.symm (u, i)).1 ∈ U := fun u ↦ (H.symm (u, i)).2
      have hHs : ∀ u : U, H ⟨(H.symm (u, i)).1, hsymm u⟩ = (u, i) := fun u ↦ by
        rw [Subtype.coe_eta, Homeomorph.apply_symm_apply]
      refine ⟨{ toFun := fun y ↦ (H ⟨y.1, y.2.1⟩).1
                invFun := fun u ↦ ⟨(H.symm (u, i)).1, hsymm u, by rw [hHs]⟩
                left_inv := fun y ↦ ?_
                right_inv := fun u ↦ by
                  change (H ⟨(H.symm (u, i)).1, hsymm u⟩).1 = u
                  rw [hHs]
                continuous_toFun := ?_
                continuous_invFun := ?_ }, fun y ↦ hH _⟩
      · obtain ⟨y, hy, e⟩ := y
        apply Subtype.ext
        change (H.symm ((H ⟨y, hy⟩).1, i)).1 = y
        rw [← e]
        rw [Prod.mk.eta, Homeomorph.symm_apply_apply]
      · exact continuous_fst.comp (H.continuous.comp (continuous_subtype_val.subtype_mk _))
      · exact (continuous_subtype_val.comp (H.symm.continuous.comp
          (continuous_id.prodMk continuous_const))).subtype_mk _

/-- `ALGD-C2-SHEAF2-R11` (prose, §4, p.17).
By 命題 16 every covering map is an étale bundle. -/
theorem isEtaleBundle_of_isCoveringMap (f : Over X) (hf : IsCoveringMap f.hom) :
    IsEtaleBundle f :=
  isIso_counit_of_localHomeoCond f ((localHomeoCond_iff f).2 hf.isLocalHomeomorph)

end Covering

section LocallyConstant

/-- `f⁻¹(U) → U` as an object of `Top/U`. -/
def restrictOver (f : Over X) (U : Opens X) : Over ((Opens.toTopCat X).obj U) :=
  Over.mk (Y := TopCat.of (f.hom ⁻¹' (U : Set X)))
    (TopCat.ofHom ⟨fun y ↦ ⟨f.hom y.1, y.2⟩,
      (f.hom.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩)

/-- `Y × I → Y` as an object of `Top/Y`. -/
def prodOver (Y : TopCat.{u}) (I : Type u) [TopologicalSpace I] : Over Y :=
  Over.mk (Y := TopCat.of (Y × I)) (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩)

/-- An evenly covered neighbourhood gives `f⁻¹(U) ≅ U × I` over `U`. -/
def isoOfEvenlyCovered (f : Over X) (U : Opens X) {I : Type u} [TopologicalSpace I]
    (H : f.hom ⁻¹' (U : Set X) ≃ₜ U × I) (hH : ∀ y, ((H y).1 : X) = f.hom y) :
    restrictOver f U ≅ prodOver ((Opens.toTopCat X).obj U) I :=
  Over.isoMk (TopCat.isoOfHomeo H) (by
    ext y
    exact Subtype.ext (hH y))

theorem evenlyCovered_of_iso (f : Over X) (U : Opens X) {I : Type u} [TopologicalSpace I]
    (φ : restrictOver f U ≅ prodOver ((Opens.toTopCat X).obj U) I) :
    ∃ H : f.hom ⁻¹' (U : Set X) ≃ₜ U × I, ∀ y, ((H y).1 : X) = f.hom y :=
  ⟨TopCat.homeoOfIso ((Over.forget _).mapIso φ), fun y ↦
    congrArg Subtype.val (congrArg (fun m ↦ m y) (Over.w φ.hom))⟩

theorem isEtaleBundle_of_iso {Y : TopCat.{u}} {f g : Over Y} (φ : f ≅ g)
    (hf : IsEtaleBundle f) : IsEtaleBundle g := by
  have : IsIso ((etaleAdj Y).counit.app f) := hf
  have e := (etaleAdj Y).counit.naturality φ.hom
  have h : (etaleAdj Y).counit.app g =
      inv ((Presheaf.restrictedULiftYoneda.{u} (toOver Y) ⋙ etale Y).map φ.hom) ≫
        (etaleAdj Y).counit.app f ≫ φ.hom := by
    rw [IsIso.eq_inv_comp]
    exact e
  change IsIso ((etaleAdj Y).counit.app g)
  rw [h]
  infer_instance

theorem prodOver_isEtaleBundle (Y : TopCat.{u}) (A : Type u) [TopologicalSpace A]
    [DiscreteTopology A] : IsEtaleBundle (prodOver Y A) :=
  isEtaleBundle_of_iso
    (Over.isoMk (TopCat.isoOfHomeo ((constEtaleHomeo (X := Y) A).trans (Homeomorph.prodComm _ _)))
      rfl)
    (etale_isEtaleBundle (constPresheaf A))

section Restriction

variable (U : Opens X)

theorem mem_of_mem_functor {V : Opens ((Opens.toTopCat X).obj U)}
    (w : ((U.isOpenEmbedding.isOpenMap.functor.obj V : Opens X) : Set X)) : w.1 ∈ U := by
  obtain ⟨z, -, hz⟩ := w.2
  exact hz ▸ z.2

theorem mem_of_mem_functor' {V : Opens ((Opens.toTopCat X).obj U)}
    (w : ((U.isOpenEmbedding.isOpenMap.functor.obj V : Opens X) : Set X)) :
    (⟨w.1, mem_of_mem_functor U w⟩ : (Opens.toTopCat X).obj U) ∈ V := by
  obtain ⟨z, hzV, hz⟩ := w.2
  have : z = ⟨w.1, mem_of_mem_functor U w⟩ := Subtype.ext hz
  exact this ▸ hzV

/-- Sections of `f` over `j(V)` are sections of `f⁻¹(U) → U` over `V`. -/
def sectionsRestrictEquiv (f : Over X) (V : Opens ((Opens.toTopCat X).obj U)) :
    ((Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f).obj
        (op (U.isOpenEmbedding.isOpenMap.functor.obj V)) ≃
      ((Presheaf.restrictedULiftYoneda.{u} (toOver ((Opens.toTopCat X).obj U))).obj
        (restrictOver f U)).obj (op V) where
  toFun s :=
    let hin : ∀ z : ((toOver ((Opens.toTopCat X).obj U)).obj V).left,
        (z.1.1 : X) ∈ U.isOpenEmbedding.isOpenMap.functor.obj V :=
      fun z ↦ ⟨z.1, z.2, rfl⟩
    let hmem : ∀ z : ((toOver ((Opens.toTopCat X).obj U)).obj V).left,
        s.down.left ⟨z.1.1, hin z⟩ ∈ f.hom ⁻¹' (U : Set X) := fun z ↦ by
      rw [Set.mem_preimage, section_base f s]
      exact z.1.2
    have hc : Continuous (fun z : ((toOver ((Opens.toTopCat X).obj U)).obj V).left ↦
        (⟨z.1.1, hin z⟩ : ((U.isOpenEmbedding.isOpenMap.functor.obj V : Opens X) : Set X))) := by
      fun_prop
    ULift.up (Over.homMk (TopCat.ofHom
      ⟨fun z ↦ ⟨s.down.left ⟨z.1.1, hin z⟩, hmem z⟩,
        (s.down.left.hom.continuous.comp hc).subtype_mk hmem⟩) (by
      ext z
      exact Subtype.ext (section_base f s ⟨z.1.1, hin z⟩)))
  invFun t :=
    have hc : Continuous (fun w : ((U.isOpenEmbedding.isOpenMap.functor.obj V : Opens X) :
        Set X) ↦ (⟨⟨w.1, mem_of_mem_functor U w⟩, mem_of_mem_functor' U w⟩ :
          ((toOver ((Opens.toTopCat X).obj U)).obj V).left)) := by
      fun_prop
    ULift.up (Over.homMk (TopCat.ofHom
      ⟨fun w ↦ (t.down.left ⟨⟨w.1, mem_of_mem_functor U w⟩, mem_of_mem_functor' U w⟩).1,
        continuous_subtype_val.comp (t.down.left.hom.continuous.comp hc)⟩) (by
      ext w
      exact congrArg Subtype.val (section_base (restrictOver f U) t
        ⟨⟨w.1, mem_of_mem_functor U w⟩, mem_of_mem_functor' U w⟩)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- `(F † y)(f)` restricted along `j : U → X` is `F † y(f⁻¹(U) → U)`. -/
def sectionsRestrictIso (f : Over X) :
    U.isOpenEmbedding.isOpenMap.functor.op ⋙ (Presheaf.restrictedULiftYoneda.{u} (toOver X)).obj f ≅
      (Presheaf.restrictedULiftYoneda.{u} (toOver ((Opens.toTopCat X).obj U))).obj
        (restrictOver f U) :=
  NatIso.ofComponents (fun V ↦ (sectionsRestrictEquiv U f V.unop).toIso) (fun _ ↦ by
    ext
    rfl)

end Restriction

end LocallyConstant

section Prop23

/-- mathlib's constant sheaf is `F † y(Y × A → Y)` for discrete `A`. -/
def constSheafIso (Y : TopCat.{u}) (A : Type u) [TopologicalSpace A] [DiscreteTopology A] :
    ((constantSheaf (Opens.grothendieckTopology Y) (Type u)).obj A).obj ≅
      (Presheaf.restrictedULiftYoneda.{u} (toOver Y)).obj (prodOver Y A) :=
  (sheafToPresheaf _ _).mapIso
      (((sheafificationAdjunction (Opens.grothendieckTopology Y) (Type u)).leftAdjointUniq
        (sheafificationAdj Y)).app (constPresheaf A)) ≪≫
    (Presheaf.restrictedULiftYoneda.{u} (toOver Y)).mapIso
      (Over.isoMk (TopCat.isoOfHomeo ((constEtaleHomeo (X := Y) A).trans
        (Homeomorph.prodComm _ _))) rfl)

/-- `P|_U ≅ F † y(Λ_P|_U → U)` for a sheaf `P`. -/
def restrictIso (P : X.Sheaf (Type u)) (U : Opens X) :
    (Presheaf.pullback (Type u) U.inclusion').obj P.presheaf ≅
      (Presheaf.restrictedULiftYoneda.{u} (toOver ((Opens.toTopCat X).obj U))).obj
        (restrictOver ((etale X).obj P.obj) U) :=
  (U.isOpenEmbedding.isOpenMap.pullbackIso (C := Type u)).app P.presheaf ≪≫
    Functor.isoWhiskerLeft U.isOpenEmbedding.isOpenMap.functor.op (etaUnitIso P) ≪≫
    sectionsRestrictIso U _

theorem restrictOver_localHomeoCond (P : X.Presheaf (Type u)) (U : Opens X) :
    LocalHomeoCond (restrictOver ((etale X).obj P) U) := by
  intro g
  let r := rep P g.1
  let W : Opens X := r.U ⊓ U
  let s' : P.obj (op W) := P.map (homOfLE inf_le_left).op r.s
  have hg : g.1 ∈ germSet P W s' := ⟨⟨r.mem, g.2⟩, r.eq.symm.trans
    (germ_res_apply P (homOfLE inf_le_left) g.1.base ⟨r.mem, g.2⟩ r.s).symm⟩
  let O : Set (restrictOver ((etale X).obj P) U).left := Subtype.val ⁻¹' germSet P W s'
  have hO : IsOpen O := (isOpen_germSet P W s').preimage continuous_subtype_val
  let T : Set ((Opens.toTopCat X).obj U) := Subtype.val ⁻¹' (W : Set X)
  have hT : IsOpen T := W.isOpen.preimage continuous_subtype_val
  have himg : (restrictOver ((etale X).obj P) U).hom '' O = T := by
    ext z
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact hg'.1
    · intro hz
      exact ⟨⟨germMap P W s' ⟨z.1, hz⟩, z.2⟩, ⟨hz, rfl⟩, rfl⟩
  let e₀ : O ≃ₜ T :=
    { toFun := fun g' ↦ ⟨⟨g'.1.1.base, g'.1.2⟩, g'.2.1⟩
      invFun := fun z ↦ ⟨⟨germMap P W s' ⟨z.1.1, z.2⟩, z.1.2⟩, z.2, rfl⟩
      left_inv := fun g' ↦ Subtype.ext (Subtype.ext (etaleMk_eq_of_mem g'.2))
      right_inv := fun _ ↦ rfl
      continuous_toFun := by
        have := EtaleSpace.continuous_base P
        fun_prop
      continuous_invFun := by
        have := continuous_germMap P W s'
        fun_prop }
  exact ⟨O, hO, hg, himg ▸ hT, e₀.trans (Homeomorph.setCongr himg.symm), fun _ ↦ rfl⟩

/-- Étale bundles with isomorphic sheaves of sections are isomorphic. -/
def isoOfSectionsIso {Y : TopCat.{u}} {f g : Over Y} (hf : IsEtaleBundle f)
    (hg : IsEtaleBundle g)
    (φ : (Presheaf.restrictedULiftYoneda.{u} (toOver Y)).obj f ≅
      (Presheaf.restrictedULiftYoneda.{u} (toOver Y)).obj g) : f ≅ g :=
  (counitIso (X := Y) ⟨f, hf⟩).symm ≪≫ (etale Y).mapIso φ ≪≫ counitIso (X := Y) ⟨g, hg⟩

/-- `ALGD-C2-SHEAF2-23` (命題 23, §4, p.17).
For a sheaf `P` with étale bundle `p : Λ_P → X`, `P` is locally constant iff `p` is a covering
map. The source omits the proof. On an open `U`, `P|_U ≅ F † y(p⁻¹(U) → U)`, and mathlib's constant
sheaf on `U` with value `A` is `F † y(U × A → U)`; `Sh(U) ≃ Etale(U)` (定理 15 on `U`) turns an
isomorphism of these sheaves into `p⁻¹(U) ≅ U × A` over `U`, i.e. an evenly covered `U`. -/
theorem isLocallyConstantSheaf_iff (P : X.Sheaf (Type u)) :
    IsLocallyConstantSheaf P ↔ IsCoveringMap ((etale X).obj P.obj).hom := by
  constructor
  · intro hP x
    obtain ⟨U, hxU, A, ⟨ψ⟩⟩ := hP x
    let _ : TopologicalSpace A := ⊥
    have : DiscreteTopology A := ⟨rfl⟩
    let φ := isoOfSectionsIso
      (isIso_counit_of_localHomeoCond _ (restrictOver_localHomeoCond P.obj U))
      (prodOver_isEtaleBundle _ A)
      ((restrictIso P U).symm ≪≫ ψ ≪≫ constSheafIso _ A)
    obtain ⟨H, hH⟩ := evenlyCovered_of_iso _ U φ
    exact IsEvenlyCovered.to_isEvenlyCovered_preimage
      ⟨inferInstance, U, hxU, U.isOpen, U.isOpen.preimage (EtaleSpace.continuous_base _), H, hH⟩
  · intro hp x
    obtain ⟨hdisc, U', hxU', hU', -, H, hH⟩ := hp x
    let U : Opens X := ⟨U', hU'⟩
    exact ⟨U, hxU', _, ⟨restrictIso P U ≪≫
      (Presheaf.restrictedULiftYoneda.{u} (toOver _)).mapIso
        (isoOfEvenlyCovered _ U H hH) ≪≫ (constSheafIso _ _).symm⟩⟩

end Prop23

end

/-! ## Axiom audit

Each verified declaration depends only on `propext`, `Classical.choice` and `Quot.sound`
(`presheaf_def` uses only `propext` and `Quot.sound`). The output is pinned with `#guard_msgs`,
so `lake build` fails if it changes. -/

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.presheaf_def' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.presheaf_def

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.stalkFunctor_iso_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.stalkFunctor_iso_pullback

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.stalk_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.stalk_quotient

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.real_germ_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.real_germ_eq_iff

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.stalk_yoneda' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.stalk_yoneda

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.stalk_map_germ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.stalk_map_germ

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.stalk_yonedaEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.stalk_yonedaEquiv

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.toOver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.toOver

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.universal_adjunction_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.universal_adjunction_exists

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.sections_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.sections_spec

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.sections_isSheaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.sections_isSheaf

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.sheafify_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.sheafify_universal

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.sheafify_stalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.sheafify_stalk

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.locallyConstant_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.locallyConstant_iff

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.restrict_obj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.restrict_obj

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.IsLocallyConstantSheaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.IsLocallyConstantSheaf

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.skyscraper_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.skyscraper_spec

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.lan_colimit_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.lan_colimit_spec

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.fiberFunctor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.fiberFunctor

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.fiber_kanExtensions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.fiber_kanExtensions

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.stalk_iso_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.stalk_iso_fiber

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.lan_bijection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.lan_bijection

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.lan_homeomorph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.lan_homeomorph

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.unit_eq_leg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.unit_eq_leg

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.isSheaf_iff_isIso_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.isSheaf_iff_isIso_unit

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.IsEtaleBundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.IsEtaleBundle

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.sheaf_equiv_etale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.sheaf_equiv_etale

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.etale_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.etale_tfae

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.counit_leg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.counit_leg

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.sheafification_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.sheafification_spec

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.sheafification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.sheafification

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.constant_sheaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.constant_sheaf

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.isCoveringMapSrc_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.isCoveringMapSrc_iff

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.isEtaleBundle_of_isCoveringMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.isEtaleBundle_of_isCoveringMap

/-- info: 'ProjectEpisteme.AlgD.Sheaf2.isLocallyConstantSheaf_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Sheaf2.isLocallyConstantSheaf_iff
end ProjectEpisteme.AlgD.Sheaf2

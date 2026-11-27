/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# alg-d, Chapter 2: 例：位相空間上の層 その2 (Example: sheaves on a topological space, part 2)

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 2, `sheaf_kan_extension.pdf`
(<https://alg-d.com/math/kan_extension/sheaf_kan_extension.pdf>), printed date 2026-07-22,
SHA-256 `abb57620ed58bd0842f0f0bed9c031f3abe16114df46770bd0680b783e74075b`,
retrieved 2026-11-26. Ledger: `docs/ledger/algd/C2-SHEAF2.md`.

§1 restates results of 「Kan拡張」; those rows share the declarations in
`ProjectEpisteme/Category/AlgD/C2/Kan.lean`. This module covers the first batch of §2–§4.

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
* `Sh(X)` is `TopCat.Sheaf (Type u) X` with the inclusion `TopCat.Sheaf.forget`. 命題 19 and
  命題 20 are stated for every left adjoint of the inclusion, which covers the source's
  `L = F † y ∘ y † F` and mathlib's sheafification.
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
end ProjectEpisteme.AlgD.Sheaf2

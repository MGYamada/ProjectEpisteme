/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# alg-d, Chapter 2: 余米田の補題 (The co-Yoneda lemma)

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 2, `coyoneda.pdf`
(<https://alg-d.com/math/kan_extension/coyoneda.pdf>), printed date 2026-09-11,
SHA-256 `30850e653487e8b8e2aabf41f9a7df4dc11c713c12db17db36a921ea18925753`,
retrieved 2026-11-26. Ledger: `docs/ledger/algd/C2-COYONEDA.md`.

## Conventions

* `Ĉ = C^op → Set` is `Cᵒᵖ ⥤ Type v` for `C : Type u` with `[Category.{v} C]`; in 命題 2 `C` is
  small.
* Ends and coends are mathlib's `Wedge`/`Cowedge` (multiforks): for `F : Jᵒᵖ ⥤ J ⥤ 𝒱`, the
  coend `∫^j F(j, j)` is the vertex of a colimit cowedge. Here `J = C^op`, so the first variable
  of an integrand lies in `C^opᵒᵖ`.
* `y(c) × P c` is the presheaf `b ↦ Hom_C(b, c) × P c`, the copower of `y(c)` by the set `P c`.
* The source derives the results from Kan extensions (`id†`, `id‡`) and the end and coend
  formulas of 「エンド」. Those modules are not imported here; each statement is proved directly
  from its universal property.
-/

@[expose] public section

namespace ProjectEpisteme.AlgD.Coyoneda

open CategoryTheory Limits Functor Opposite MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C]

/-- `ALGD-C2-COYONEDA-R01` (prose, p.1).
For `P : C^op → Set`, the right Kan extension `id‡ P` of `P` along the identity is `P` itself
(with the identity counit). -/
theorem rightKanExtension_id (P : Cᵒᵖ ⥤ Type v) :
    P.IsRightKanExtension (Functor.leftUnitor P).hom :=
  inferInstance

/-- `ALGD-C2-COYONEDA-R02` (prose, p.1).
The Yoneda lemma from the pointwise right Kan extension `id‡ P`: for `a ∈ C^op` and `x ∈ Set`,
`Hom_Set(x, P a) ≅ Hom_{Set^{C^op}}(Hom_{C^op}(a, −), Hom_Set(x, P−))`, and for `x = 1` this gives
`P a ≅ Hom_Ĉ(y(a), P)`. The first bijection is the covariant Yoneda lemma for
`Hom_Set(x, P −)`. -/
theorem yoneda_via_rightKanExtension (P : Cᵒᵖ ⥤ Type v) (a : Cᵒᵖ) (x : Type v) :
    Nonempty ((x ⟶ P.obj a) ≃ (coyoneda.obj (op a) ⟶ P ⋙ coyoneda.obj (op x))) ∧
    Nonempty (P.obj a ≃ (yoneda.obj a.unop ⟶ P)) :=
  ⟨⟨(coyonedaEquiv (F := P ⋙ coyoneda.obj (op x))).symm⟩, ⟨yonedaEquiv.symm⟩⟩

/-! ### The integrands -/

/-- The integrand `(c, c') ↦ Hom_{C^op}(a, c) ⇒ P c'` of the end formula (p.1–2), as a functor
`C^opᵒᵖ → C^op → Set`. -/
@[simps]
def endIntegrand (P : Cᵒᵖ ⥤ Type v) (a : Cᵒᵖ) : Cᵒᵖᵒᵖ ⥤ Cᵒᵖ ⥤ Type v where
  obj X :=
    { obj j := (a ⟶ X.unop) → P.obj j
      map g := ↾ fun φ f ↦ P.map g (φ f) }
  map ψ := { app j := ↾ fun φ f ↦ φ (f ≫ ψ.unop) }

/-- The integrand `(c, c') ↦ Hom_C(a, c) × P c'` of the pointwise co-Yoneda lemma. -/
@[simps]
def coendIntegrand (P : Cᵒᵖ ⥤ Type v) (a : C) : Cᵒᵖᵒᵖ ⥤ Cᵒᵖ ⥤ Type v where
  obj X :=
    { obj j := (a ⟶ X.unop.unop) × P.obj j
      map g := ↾ fun p ↦ (p.1, P.map g p.2) }
  map ψ := { app j := ↾ fun p ↦ (p.1 ≫ ψ.unop.unop, p.2) }

/-- The integrand `(c, c') ↦ y(c) × P c'` of 定理 1, with values in `Ĉ`. -/
@[simps]
def coyonedaIntegrand (P : Cᵒᵖ ⥤ Type v) : Cᵒᵖᵒᵖ ⥤ Cᵒᵖ ⥤ Cᵒᵖ ⥤ Type v where
  obj X :=
    { obj j :=
        { obj b := (b.unop ⟶ X.unop.unop) × P.obj j
          map g := ↾ fun p ↦ (g.unop ≫ p.1, p.2) }
      map g := { app b := ↾ fun p ↦ (p.1, P.map g p.2) } }
  map ψ := { app j := { app b := ↾ fun p ↦ (p.1 ≫ ψ.unop.unop, p.2) } }

/-! ### The end formula, the co-Yoneda lemma and cartesian closedness -/

private theorem map_id_apply' (P : Cᵒᵖ ⥤ Type v) (a : Cᵒᵖ) (x : P.obj a) : P.map (𝟙 a) x = x := by
  simp

/-- The wedge `P a → Hom_Set(Hom_{C^op}(a, c), P c)`, `x ↦ (f ↦ P f x)`. -/
def endWedge (P : Cᵒᵖ ⥤ Type v) (a : Cᵒᵖ) : Wedge (endIntegrand P a) :=
  Wedge.mk (P.obj a) (fun j ↦ ↾ fun x f ↦ P.map f x) fun i j f ↦ by
    ext x
    funext g
    change P.map f (P.map g x) = P.map (g ≫ f) x
    exact (Functor.map_comp_apply P g f x).symm

/-- `ALGD-C2-COYONEDA-R03` (prose, p.1–2).
The end formula for the identity: `P ≅ ∫_{c ∈ C^op} Hom_Set(Hom_{C^op}(−, c), P c)`, that is, for
each `a`, `P a` with the maps `x ↦ (f ↦ P f x)` is an end of
`(c, c') ↦ Hom_Set(Hom_{C^op}(a, c), P c')`; this end is `Hom_Ĉ(y(a), P)`. (The source notes that
this is not an independent proof of the Yoneda lemma.) -/
theorem endWedge_isLimit (P : Cᵒᵖ ⥤ Type v) (a : Cᵒᵖ) : Nonempty (IsLimit (endWedge P a)) := by
  refine ⟨Multifork.IsLimit.mk _ (fun E ↦ ↾ fun w ↦ E.ι a w (𝟙 a)) (fun E j ↦ ?_)
    (fun E m hm ↦ ?_)⟩
  · ext w
    funext f
    have h := congrFun (ConcreteCategory.congr_hom (Wedge.condition E f) w) (𝟙 a)
    change P.map f (E.ι a w (𝟙 a)) = E.ι j w (𝟙 a ≫ f) at h
    change P.map f (E.ι a w (𝟙 a)) = E.ι j w f
    rw [h, Category.id_comp]
  · ext w
    have h := congrFun (ConcreteCategory.congr_hom (hm a) w) (𝟙 a)
    change P.map (𝟙 a) (m w) = E.ι a w (𝟙 a) at h
    exact (map_id_apply' P a (m w)).symm.trans h

/-- The cowedge `Hom_C(a, c) × P c → P a`, `(f, x) ↦ P f x`. -/
def coendCowedge (P : Cᵒᵖ ⥤ Type v) (a : C) : Cowedge (coendIntegrand P a) :=
  Cowedge.mk (P.obj (op a)) (fun j ↦ ↾ fun p ↦ P.map p.1.op p.2) fun i j f ↦ by
    ext p
    change P.map (p.1 ≫ f.unop).op p.2 = P.map p.1.op (P.map f p.2)
    rw [op_comp, Functor.map_comp_apply]
    rfl

/-- `ALGD-C2-COYONEDA-R04` (prose after 定理 1, p.2).
Pointwise co-Yoneda lemma: for `a ∈ C`, `P a ≅ ∫^{c ∈ C^op} Hom_C(a, c) × P c`, with the maps
`(f, x) ↦ P f x`. -/
theorem coendCowedge_isColimit (P : Cᵒᵖ ⥤ Type v) (a : C) :
    Nonempty (IsColimit (coendCowedge P a)) := by
  refine ⟨Multicofork.IsColimit.mk _ (fun E ↦ ↾ fun x ↦ E.π (op a) (𝟙 a, x)) (fun E j ↦ ?_)
    (fun E m hm ↦ ?_)⟩
  · ext ⟨g, x⟩
    have h := ConcreteCategory.congr_hom (Cowedge.condition E (i := j) (j := op a) g.op)
      ((𝟙 a, x) : (a ⟶ a) × P.obj j)
    change E.π j (𝟙 a ≫ g, x) = E.π (op a) (𝟙 a, P.map g.op x) at h
    change E.π (op a) (𝟙 a, P.map g.op x) = E.π j (g, x)
    rw [← h, Category.id_comp]
  · ext x
    have h := ConcreteCategory.congr_hom (hm (op a)) ((𝟙 a, x) : (a ⟶ a) × P.obj (op a))
    change m (P.map (𝟙 (op a)) x) = E.π (op a) (𝟙 a, x) at h
    exact (congrArg m (map_id_apply' P (op a) x)).symm.trans h

/-- The cowedge `y(c) × P c ⇒ P`, `(f, x) ↦ P f x`, of 定理 1. -/
def coyonedaCowedge (P : Cᵒᵖ ⥤ Type v) : Cowedge (coyonedaIntegrand P) :=
  Cowedge.mk P
    (fun j ↦
      { app b := ↾ fun p ↦ P.map p.1.op p.2
        naturality b b' g := by
          ext p
          change P.map (g.unop ≫ p.1).op p.2 = P.map g (P.map p.1.op p.2)
          rw [op_comp, Functor.map_comp_apply]
          rfl })
    fun i j f ↦ by
      ext b p
      change P.map (p.1 ≫ f.unop).op p.2 = P.map p.1.op (P.map f p.2)
      rw [op_comp, Functor.map_comp_apply]
      rfl

/-- `ALGD-C2-COYONEDA-01` (定理 1 (余米田の補題), p.2).
For `P : C^op → Set`, `P ≅ ∫^{c ∈ C^op} y(c) × P c`: `P` with the maps `y(c) × P c ⇒ P`,
`(f, x) ↦ P f x`, is a coend in `Ĉ`. The source obtains this from the coend formula for left Kan
extensions applied to `id† P`; here the universal property is checked directly. -/
theorem coyonedaCowedge_isColimit (P : Cᵒᵖ ⥤ Type v) :
    Nonempty (IsColimit (coyonedaCowedge P)) := by
  refine ⟨Multicofork.IsColimit.mk _ (fun E ↦
    { app b := ↾ fun x ↦ (E.π b).app b (𝟙 b.unop, x)
      naturality b b' g := by
        ext x
        have h1 := ConcreteCategory.congr_hom
          (congrArg (fun α ↦ NatTrans.app α b') (Cowedge.condition E g))
          ((𝟙 b'.unop, x) : (b'.unop ⟶ b'.unop) × P.obj b)
        have h2 := ConcreteCategory.congr_hom ((E.π b).naturality g)
          ((𝟙 b.unop, x) : (b.unop ⟶ b.unop) × P.obj b)
        change (E.π b).app b' (𝟙 b'.unop ≫ g.unop, x) = (E.π b').app b' (𝟙 b'.unop, P.map g x)
          at h1
        change (E.π b).app b' (g.unop ≫ 𝟙 b.unop, x) = E.pt.map g ((E.π b).app b (𝟙 b.unop, x))
          at h2
        change (E.π b').app b' (𝟙 b'.unop, P.map g x) = E.pt.map g ((E.π b).app b (𝟙 b.unop, x))
        rw [← h1, ← h2, Category.id_comp, Category.comp_id] }) (fun E j ↦ ?_) (fun E m hm ↦ ?_)⟩
  · ext b ⟨g, x⟩
    have h := ConcreteCategory.congr_hom
      (congrArg (fun α ↦ NatTrans.app α b) (Cowedge.condition E (i := j) (j := b) g.op))
      ((𝟙 b.unop, x) : (b.unop ⟶ b.unop) × P.obj j)
    change (E.π j).app b (𝟙 b.unop ≫ g, x) = (E.π b).app b (𝟙 b.unop, P.map g.op x) at h
    change (E.π b).app b (𝟙 b.unop, P.map g.op x) = (E.π j).app b (g, x)
    rw [← h, Category.id_comp]
  · ext b x
    have h := ConcreteCategory.congr_hom (congrArg (fun α ↦ NatTrans.app α b) (hm b))
      ((𝟙 b.unop, x) : (b.unop ⟶ b.unop) × P.obj b)
    change m.app b (P.map (𝟙 b) x) = (E.π b).app b (𝟙 b.unop, x) at h
    exact (congrArg (m.app b) (map_id_apply' P b x)).symm.trans h

/-- `ALGD-C2-COYONEDA-02` (命題 2, p.2–3).
For a small category `C`, `Ĉ = Set^{C^op}` is cartesian closed, and the exponential is
`Q^P(c) ≅ Hom_Ĉ(y(c) × P, Q)`, as in the source's construction. The cartesian closed
structure is mathlib's `FunctorToTypes.monoidalClosed`. -/
theorem presheaf_cartesianClosed {C : Type v} [SmallCategory C] :
    Nonempty (MonoidalClosed (Cᵒᵖ ⥤ Type v)) ∧
    ∀ (P Q : Cᵒᵖ ⥤ Type v) (c : C),
      Nonempty (((ihom P).obj Q).obj (op c) ≃ (yoneda.obj c ⊗ P ⟶ Q)) :=
  ⟨⟨inferInstance⟩, fun P Q c ↦ ⟨yonedaEquiv.symm.trans
    (((ihom.adjunction P).homEquiv _ _).symm.trans ((β_ P (yoneda.obj c)).homCongr (Iso.refl Q)))⟩⟩

/-! ## Axiom audit

Each verified declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. The
output is pinned with `#guard_msgs`, so `lake build` fails if it changes. -/

/-- info: 'ProjectEpisteme.AlgD.Coyoneda.rightKanExtension_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Coyoneda.rightKanExtension_id

/-- info: 'ProjectEpisteme.AlgD.Coyoneda.yoneda_via_rightKanExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Coyoneda.yoneda_via_rightKanExtension

/-- info: 'ProjectEpisteme.AlgD.Coyoneda.endWedge_isLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Coyoneda.endWedge_isLimit

/-- info: 'ProjectEpisteme.AlgD.Coyoneda.coendCowedge_isColimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Coyoneda.coendCowedge_isColimit

/-- info: 'ProjectEpisteme.AlgD.Coyoneda.coyonedaCowedge_isColimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Coyoneda.coyonedaCowedge_isColimit

/-- info: 'ProjectEpisteme.AlgD.Coyoneda.presheaf_cartesianClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Coyoneda.presheaf_cartesianClosed
end ProjectEpisteme.AlgD.Coyoneda

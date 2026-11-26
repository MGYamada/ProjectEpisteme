module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Products.Basic

/-!
# alg-d, Chapter 2: エンド (Ends)

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 2, `end.pdf`
(<https://alg-d.com/math/kan_extension/end.pdf>), printed date 2026-09-11,
SHA-256 `d4f708874a371b1769860c2601661a4731191e7a5f608f9494838d758e1096f4`,
retrieved 2026-11-26. Ledger: `docs/ledger/algd/C2-END.md`.

## Conventions

* The source's `T : C^op × C → D` is a functor `Cᵒᵖ × C ⥤ D`. The source's wedges, ends,
  cowedges and coends are defined for it (`IsWedge`, `IsEnd`, `IsCowedge`, `IsCoend`) and shown
  to agree with mathlib's `Wedge`, `Cowedge` and their (co)limits for the curried functor
  `Functor.curryObj T : Cᵒᵖ ⥤ C ⥤ D`. Later statements use mathlib's curried form directly.
* `Hom_D(F−, G□)` is `F.op.prod G ⋙ Functor.hom D`.
* For Fubini's theorem (定理 4) the source's `T : C^op × C × X^op × X → D` is a functor
  `Cᵒᵖ × C × Xᵒᵖ × X ⥤ D`. It is regarded as a functor of `⟨c, x⟩ ∈ C × X` through
  `C^op × C × X^op × X ≅ (C × X)^op × (C × X)` (`fubiniProd`) and as a family of functors
  `C^op × C → D` indexed by `X^op × X` (`fubiniParam`).
* Coends are ends of `T^op` (定義 (コエンド)); the coend case of R01 is stated that way, through
  `dual4`.
* Copowers and powers (§3) are universal arrows to `Hom_C(a, −)` and `Hom_C(−, a)`, i.e.
  initial objects of the comma categories `x ↓ Hom_C(a, −)` and `x ↓ Hom_C(−, a)`. They are
  coproducts and products of constant families (`isCopower_iff_isColimit`,
  `isPower_iff_isLimit`); 定理 9 and its dual take them in that form.
-/

@[expose] public section

namespace ProjectEpisteme.AlgD.Ends

open CategoryTheory Limits Functor Opposite
open scoped CategoryTheory.Prod

universe w v v₁ v₂ v₃ u u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-! ## Wedges and ends -/

/-- The source's wedges (定義, p.2): a family `σ_a : d → T(a, a)` such that
`T(id_a, f) ∘ σ_a = T(f, id_b) ∘ σ_b` for every `f : a → b`. -/
def IsWedge (T : Cᵒᵖ × C ⥤ D) (d : D) (σ : ∀ a : C, d ⟶ T.obj (op a, a)) : Prop :=
  ∀ ⦃a b : C⦄ (f : a ⟶ b), σ a ≫ T.map (𝟙 (op a) ×ₘ f) = σ b ≫ T.map (f.op ×ₘ 𝟙 b)

/-- `ALGD-C2-END-D01` (定義 (wedge), p.2).
A wedge `σ : d → T` is a family `σ_a : d → T(a, a)` with `T(id_a, f) ∘ σ_a = T(f, id_b) ∘ σ_b`
for every `f : a → b`; this is the condition of mathlib's `Wedge.mk` for the curried functor. -/
theorem isWedge_iff (T : Cᵒᵖ × C ⥤ D) (d : D) (σ : ∀ a : C, d ⟶ T.obj (op a, a)) :
    IsWedge T d σ ↔ ∀ ⦃a b : C⦄ (f : a ⟶ b),
      σ a ≫ ((curryObj T).obj (op a)).map f = σ b ≫ ((curryObj T).map f.op).app b :=
  Iff.rfl

/-- The mathlib wedge given by a wedge in the source's sense. -/
abbrev IsWedge.wedge {T : Cᵒᵖ × C ⥤ D} {d : D} {σ : ∀ a : C, d ⟶ T.obj (op a, a)}
    (h : IsWedge T d σ) : Wedge (curryObj T) :=
  Wedge.mk d σ h

/-- The source's ends (定義, p.2–3): a wedge `⟨e, l⟩` through which every wedge factors uniquely. -/
def IsEnd (T : Cᵒᵖ × C ⥤ D) (e : D) (l : ∀ a : C, e ⟶ T.obj (op a, a)) : Prop :=
  IsWedge T e l ∧ ∀ (d : D) (σ : ∀ a : C, d ⟶ T.obj (op a, a)), IsWedge T d σ →
    ∃! h : d ⟶ e, ∀ a, h ≫ l a = σ a

/-- `ALGD-C2-END-D02` (定義 (エンド), p.2–3).
An end `⟨e, λ⟩ = ∫_{c∈C} T(c, c)` of `T` is a wedge through which every wedge factors uniquely;
this is a limit wedge in mathlib's sense. -/
theorem isEnd_iff (T : Cᵒᵖ × C ⥤ D) (e : D) (l : ∀ a : C, e ⟶ T.obj (op a, a))
    (hl : IsWedge T e l) : IsEnd T e l ↔ Nonempty (IsLimit hl.wedge) := by
  constructor
  · rintro ⟨-, h⟩
    refine ⟨Multifork.IsLimit.mk _ (fun s ↦ (h s.pt s.ι fun a b f ↦ Wedge.condition s f).exists.choose)
      (fun s a ↦ (h s.pt s.ι fun a b f ↦ Wedge.condition s f).exists.choose_spec a)
      (fun s m hm ↦ (h s.pt s.ι fun a b f ↦ Wedge.condition s f).unique hm
        (h s.pt s.ι fun a b f ↦ Wedge.condition s f).exists.choose_spec)⟩
  · rintro ⟨hc⟩
    exact ⟨hl, fun d σ hσ ↦ ⟨Wedge.IsLimit.lift hc σ hσ, Wedge.IsLimit.lift_ι hc σ hσ,
      fun m hm ↦ Wedge.IsLimit.hom_ext hc fun a ↦
        (hm a).trans (Wedge.IsLimit.lift_ι hc σ hσ a).symm⟩⟩

/-- `ALGD-C2-END-01` (prose, p.1–2, and 例 1, p.2).
A family `σ_a ∈ Hom_D(Fa, Ga)` (a family of maps `1 → Hom_D(Fa, Ga)`) is a wedge from `1` to
`Hom_D(F−, G□)` iff it is natural, i.e. a natural transformation `F ⇒ G`. -/
theorem isWedge_hom_iff (F G : C ⥤ D)
    (σ : ∀ a : C, PUnit.{v₂ + 1} ⟶ (F.op.prod G ⋙ Functor.hom D).obj (op a, a)) :
    IsWedge (F.op.prod G ⋙ Functor.hom D) PUnit σ ↔
      ∀ ⦃a b : C⦄ (f : a ⟶ b), F.map f ≫ σ b PUnit.unit = σ a PUnit.unit ≫ G.map f := by
  constructor
  · intro h a b f
    have := ConcreteCategory.congr_hom (h f) PUnit.unit
    simp at this
    exact this.symm
  · intro h a b f
    ext ⟨⟩
    simp
    exact (h f).symm

/-- `ALGD-C2-END-02` (例 2, p.3).
For `F, G : C → D`, `∫_{c∈C} Hom_D(Fc, Gc) ≅ Hom_{D^C}(F, G)`: the projections
`β ↦ β_a` form an end. Here `Ob(C)` is `v₂`-small, so that `Hom_{D^C}(F, G)` is a set. -/
theorem isEnd_natTrans {C : Type v₂} [Category.{v₁} C] (F G : C ⥤ D) :
    IsEnd (F.op.prod G ⋙ Functor.hom D) (F ⟶ G) (fun a ↦ ↾fun β ↦ β.app a) := by
  refine ⟨fun a b f ↦ ?_, fun d σ hσ ↦ ?_⟩
  · ext β
    simp
    exact (β.naturality f).symm
  · have hnat : ∀ (x : d) ⦃a b : C⦄ (f : a ⟶ b), F.map f ≫ σ b x = σ a x ≫ G.map f :=
      fun x a b f ↦ by
        have := ConcreteCategory.congr_hom (hσ f) x
        simp at this
        exact this.symm
    refine ⟨↾fun x ↦ { app := fun a ↦ σ a x, naturality := fun a b f ↦ hnat x f }, fun a ↦ ?_,
      fun h hh ↦ ?_⟩
    · ext x
      rfl
    · ext x a
      exact ConcreteCategory.congr_hom (hh a) x

/-- The source's cowedges, drawn in `D` (定義, p.3): a family `σ_a : T(a, a) → d` such that
`σ_a ∘ T(id_a, f) = σ_b ∘ T(f, id_b)` for every `f : b → a`. -/
def IsCowedge (T : Cᵒᵖ × C ⥤ D) (d : D) (σ : ∀ a : C, T.obj (op a, a) ⟶ d) : Prop :=
  ∀ ⦃a b : C⦄ (f : b ⟶ a), T.map (𝟙 (op a) ×ₘ f) ≫ σ a = T.map (f.op ×ₘ 𝟙 b) ≫ σ b

/-- `ALGD-C2-END-D03` (定義 (cowedge), p.3).
A cowedge `T → d` is a wedge from `d` to `T^op` in `D^op`; drawn in `D`, it is a family
`σ_a : T(a, a) → d` with `σ_a ∘ T(id_a, f) = σ_b ∘ T(f, id_b)` for every `f : b → a`. This is
the condition of mathlib's `Cowedge.mk` for the curried functor. -/
theorem isCowedge_iff (T : Cᵒᵖ × C ⥤ D) (d : D) (σ : ∀ a : C, T.obj (op a, a) ⟶ d) :
    IsCowedge T d σ ↔ ∀ ⦃b a : C⦄ (f : b ⟶ a),
      ((curryObj T).map f.op).app b ≫ σ b = ((curryObj T).obj (op a)).map f ≫ σ a :=
  ⟨fun h _ _ f ↦ (h f).symm, fun h _ _ f ↦ (h f).symm⟩

/-- The mathlib cowedge given by a cowedge in the source's sense. -/
abbrev IsCowedge.cowedge {T : Cᵒᵖ × C ⥤ D} {d : D} {σ : ∀ a : C, T.obj (op a, a) ⟶ d}
    (h : IsCowedge T d σ) : Cowedge (curryObj T) :=
  Cowedge.mk d σ ((isCowedge_iff T d σ).1 h)

/-- The source's coends (定義, p.3–4): a cowedge through which every cowedge factors uniquely. -/
def IsCoend (T : Cᵒᵖ × C ⥤ D) (e : D) (l : ∀ a : C, T.obj (op a, a) ⟶ e) : Prop :=
  IsCowedge T e l ∧ ∀ (d : D) (σ : ∀ a : C, T.obj (op a, a) ⟶ d), IsCowedge T d σ →
    ∃! h : e ⟶ d, ∀ a, l a ≫ h = σ a

/-- `ALGD-C2-END-D04` (定義 (コエンド), p.4).
A coend `∫^{c∈C} T(c, c)` of `T` is an end of `T^op`, i.e. a cowedge through which every cowedge
factors uniquely; this is a colimit cowedge in mathlib's sense. -/
theorem isCoend_iff (T : Cᵒᵖ × C ⥤ D) (e : D) (l : ∀ a : C, T.obj (op a, a) ⟶ e)
    (hl : IsCowedge T e l) : IsCoend T e l ↔ Nonempty (IsColimit hl.cowedge) := by
  have key : ∀ s : Cowedge (curryObj T), IsCowedge T s.pt s.π := fun s a b f ↦
    (Cowedge.condition s f).symm
  constructor
  · rintro ⟨-, h⟩
    refine ⟨Multicofork.IsColimit.mk _ (fun s ↦ (h s.pt s.π (key s)).exists.choose)
      (fun s a ↦ (h s.pt s.π (key s)).exists.choose_spec a)
      (fun s m hm ↦ (h s.pt s.π (key s)).unique hm (h s.pt s.π (key s)).exists.choose_spec)⟩
  · rintro ⟨hc⟩
    exact ⟨hl, fun d σ hσ ↦ ⟨Cowedge.IsColimit.desc hc σ ((isCowedge_iff T d σ).1 hσ),
      Cowedge.IsColimit.π_desc hc σ _, fun m hm ↦ Cowedge.IsColimit.hom_ext hc fun a ↦
        (hm a).trans (Cowedge.IsColimit.π_desc hc σ _ a).symm⟩⟩

/-! ## Ends with a parameter (命題 3) -/

section Parameter

variable {X : Type u₃} [Category.{v₃} X] (T : X ⥤ Cᵒᵖ ⥤ C ⥤ D)
  (c : ∀ x, Wedge (T.obj x)) (hc : ∀ x, IsLimit (c x))

/-- The legs `λ^x_a : ∫_c T(c, c, x) → T(a, a, x)` of the chosen ends. -/
def lam (x : X) (a : C) : (c x).pt ⟶ ((T.obj x).obj (op a)).obj a := (c x).ι a

lemma lam_condition (x : X) {a b : C} (f : a ⟶ b) :
    lam T c x a ≫ ((T.obj x).obj (op a)).map f = lam T c x b ≫ ((T.obj x).map f.op).app b :=
  Wedge.condition (c x) f

include hc in
lemma lam_hom_ext (x : X) {d : D} {g h : d ⟶ (c x).pt} (w : ∀ a, g ≫ lam T c x a = h ≫ lam T c x a) :
    g = h :=
  Wedge.IsLimit.hom_ext (hc x) w

/-- The morphism `∫_c T(c, c, x) → ∫_c T(c, c, z)` induced by `k : x → z`. -/
noncomputable def endMap {x z : X} (k : x ⟶ z) : (c x).pt ⟶ (c z).pt :=
  Wedge.IsLimit.lift (hc z) (fun a ↦ lam T c x a ≫ ((T.map k).app (op a)).app a)
    (fun a b f ↦ by
      have h1 := ((T.map k).app (op a)).naturality f
      have h2 := congr_app ((T.map k).naturality f.op) b
      simp only [NatTrans.comp_app] at h2
      calc (lam T c x a ≫ ((T.map k).app (op a)).app a) ≫ ((T.obj z).obj (op a)).map f
          = lam T c x a ≫ ((T.obj x).obj (op a)).map f ≫ ((T.map k).app (op a)).app b := by
            rw [Category.assoc, h1]
        _ = (lam T c x b ≫ ((T.obj x).map f.op).app b) ≫ ((T.map k).app (op a)).app b := by
            rw [← Category.assoc, lam_condition]
        _ = (lam T c x b ≫ ((T.map k).app (op b)).app b) ≫ ((T.obj z).map f.op).app b := by
            rw [Category.assoc, h2, Category.assoc])

lemma endMap_lam {x z : X} (k : x ⟶ z) (a : C) :
    endMap T c hc k ≫ lam T c z a = lam T c x a ≫ ((T.map k).app (op a)).app a :=
  Wedge.IsLimit.lift_ι (hc z) _ _ a

/-- The functor `x ↦ ∫_c T(c, c, x)` of 命題 3, built from chosen ends. -/
noncomputable def endFunctorOf : X ⥤ D where
  obj x := (c x).pt
  map k := endMap T c hc k
  map_id x := lam_hom_ext T c hc x fun a ↦ by simp [endMap_lam]
  map_comp {x y z} k k' := lam_hom_ext T c hc z fun a ↦ by
    simp [endMap_lam, reassoc_of% endMap_lam]

/-- The morphisms `β^x_f := T(id_a, f, id_x) ∘ λ^x_a : ∫_c T(c, c, x) → T(a, b, x)`. -/
def betaOf (x : X) {a b : C} (f : a ⟶ b) : (c x).pt ⟶ ((T.obj x).obj (op a)).obj b :=
  lam T c x a ≫ ((T.obj x).obj (op a)).map f

/-- `ALGD-C2-END-03` (命題 3, p.4–5).
Let `T : C^op × C × X → D` (curried as `X ⥤ Cᵒᵖ ⥤ C ⥤ D`) have an end
`⟨∫_c T(c, c, x), λ^x⟩` for every `x ∈ X`. Then `x ↦ ∫_c T(c, c, x)` is a functor `F : X → D`
for which every `β_f : F ⇒ T(a, b, −)` is natural, and `F` is unique: any action on morphisms
that makes all `β_f` natural is `F`'s. -/
theorem endFunctorOf_spec :
    (∀ ⦃x z : X⦄ (k : x ⟶ z) ⦃a b : C⦄ (f : a ⟶ b),
      (endFunctorOf T c hc).map k ≫ betaOf T c z f =
        betaOf T c x f ≫ ((T.map k).app (op a)).app b) ∧
    ∀ (m : ∀ ⦃x z : X⦄, (x ⟶ z) → ((c x).pt ⟶ (c z).pt)),
      (∀ ⦃x z : X⦄ (k : x ⟶ z) ⦃a b : C⦄ (f : a ⟶ b),
        m k ≫ betaOf T c z f = betaOf T c x f ≫ ((T.map k).app (op a)).app b) →
      ∀ ⦃x z : X⦄ (k : x ⟶ z), m k = (endFunctorOf T c hc).map k := by
  refine ⟨fun x z k a b f ↦ ?_, fun m hm x z k ↦ ?_⟩
  · change endMap T c hc k ≫ lam T c z a ≫ _ = (lam T c x a ≫ _) ≫ _
    rw [reassoc_of% endMap_lam, ← ((T.map k).app (op a)).naturality f]
    exact (Category.assoc _ _ _).symm
  · refine lam_hom_ext T c hc z fun a ↦ ?_
    have := hm k (𝟙 a)
    simp only [betaOf, Functor.map_id, Category.comp_id] at this
    change m k ≫ lam T c z a = endMap T c hc k ≫ lam T c z a
    rw [this, endMap_lam]

end Parameter

/-! ## Fubini's theorem (定理 4) -/

section Fubini

variable {X : Type u₃} [Category.{v₃} X] (T : Cᵒᵖ × C × Xᵒᵖ × X ⥤ D)

/-- `T(−, −, u, v) : C^op × C → D` as a functor of the parameter `⟨u, v⟩ ∈ X^op × X`. -/
@[simps]
def fubiniParam : Xᵒᵖ × X ⥤ Cᵒᵖ ⥤ C ⥤ D where
  obj p :=
    { obj := fun a ↦
        { obj := fun b ↦ T.obj (a, b, p)
          map := fun f ↦ T.map (𝟙 a ×ₘ f ×ₘ 𝟙 p)
          map_id := fun b ↦ T.map_id _
          map_comp := fun f g ↦ by simp [← Functor.map_comp] }
      map := fun g ↦
        { app := fun b ↦ T.map (g ×ₘ 𝟙 b ×ₘ 𝟙 p)
          naturality := fun b b' f ↦ by simp [← Functor.map_comp] }
      map_id := fun a ↦ by ext b; exact T.map_id _
      map_comp := fun g g' ↦ by ext b; simp [← Functor.map_comp] }
  map k :=
    { app := fun a ↦
        { app := fun b ↦ T.map (𝟙 a ×ₘ 𝟙 b ×ₘ k)
          naturality := fun b b' f ↦ by simp [← Functor.map_comp] }
      naturality := fun a a' g ↦ by ext b; simp [← Functor.map_comp] }
  map_id p := by ext a b; exact T.map_id _
  map_comp k k' := by ext a b; simp [← Functor.map_comp]

/-- `T` as a functor `(C × X)^op × (C × X) → D` through
`C^op × C × X^op × X ≅ (C × X)^op × (C × X)`, curried. -/
@[simps]
def fubiniProd : (C × X)ᵒᵖ ⥤ C × X ⥤ D where
  obj p :=
    { obj := fun q ↦ T.obj (op p.unop.1, q.1, op p.unop.2, q.2)
      map := fun g ↦ T.map (𝟙 _ ×ₘ g.1 ×ₘ 𝟙 _ ×ₘ g.2)
      map_id := fun q ↦ T.map_id _
      map_comp := fun g g' ↦ by simp [← Functor.map_comp] }
  map h :=
    { app := fun q ↦ T.map (h.unop.1.op ×ₘ 𝟙 q.1 ×ₘ h.unop.2.op ×ₘ 𝟙 q.2)
      naturality := fun q q' g ↦ by simp [← Functor.map_comp] }
  map_id p := by ext q; exact T.map_id _
  map_comp h h' := by ext q; simp [← Functor.map_comp]

variable (c : ∀ p, Wedge ((fubiniParam T).obj p)) (hc : ∀ p, IsLimit (c p))

/-- The functor `X^op × X → D`, `⟨u, v⟩ ↦ ∫_c T(c, c, u, v)`, of 命題 3, curried. -/
noncomputable abbrev fubiniInner : Xᵒᵖ ⥤ X ⥤ D :=
  curryObj (endFunctorOf (fubiniParam T) c hc)

/-- The legs `λ^p_a : ∫_c T(c, c, p) → T(a, a, p)` of the chosen ends, typed through `T`. -/
def fubiniLam (p : Xᵒᵖ × X) (a : C) :
    (endFunctorOf (fubiniParam T) c hc).obj p ⟶ T.obj (op a, a, p) :=
  lam (fubiniParam T) c p a

lemma fubiniLam_condition (p : Xᵒᵖ × X) {a b : C} (f : a ⟶ b) :
    fubiniLam T c hc p a ≫ T.map (𝟙 (op a) ×ₘ f ×ₘ 𝟙 p) =
      fubiniLam T c hc p b ≫ T.map (f.op ×ₘ 𝟙 b ×ₘ 𝟙 p) :=
  lam_condition (fubiniParam T) c p f

lemma map_fubiniLam {p p' : Xᵒᵖ × X} (k : p ⟶ p') (a : C) :
    (endFunctorOf (fubiniParam T) c hc).map k ≫ fubiniLam T c hc p' a =
      fubiniLam T c hc p a ≫ T.map (𝟙 (op a) ×ₘ 𝟙 a ×ₘ k) :=
  endMap_lam (fubiniParam T) c hc k a

lemma fubiniLam_hom_ext (p : Xᵒᵖ × X) {d : D}
    {g h : d ⟶ (endFunctorOf (fubiniParam T) c hc).obj p}
    (w : ∀ a, g ≫ fubiniLam T c hc p a = h ≫ fubiniLam T c hc p a) : g = h :=
  lam_hom_ext (fubiniParam T) c hc p w

/-- The legs of a wedge over `X` of `∫_c T(c, c, −, □)`, typed through the functor of 命題 3. -/
noncomputable def innerLeg (w : Wedge (fubiniInner T c hc)) (x : X) :
    w.pt ⟶ (endFunctorOf (fubiniParam T) c hc).obj (op x, x) :=
  w.ι x

lemma innerLeg_condition (w : Wedge (fubiniInner T c hc)) {x z : X} (k : x ⟶ z) :
    innerLeg T c hc w x ≫ (endFunctorOf (fubiniParam T) c hc).map (𝟙 (op x) ×ₘ k) =
      innerLeg T c hc w z ≫ (endFunctorOf (fubiniParam T) c hc).map (k.op ×ₘ 𝟙 z) :=
  Wedge.condition w k

/-- The wedge over `C × X` attached to a wedge `μ` over `X` of `∫_c T(c, c, −, □)`: its legs are
`λ^{x,x}_a ∘ μ_x : d → T(a, a, x, x)` (the first half of the proof of 定理 4). -/
noncomputable def fubiniWedge (w : Wedge (fubiniInner T c hc)) : Wedge (fubiniProd T) :=
  Wedge.mk w.pt (fun q ↦ innerLeg T c hc w q.2 ≫ fubiniLam T c hc (op q.2, q.2) q.1) (by
    rintro ⟨a, x⟩ ⟨b, z⟩ ⟨f, k⟩
    change (innerLeg T c hc w x ≫ fubiniLam T c hc (op x, x) a) ≫
        T.map (𝟙 (op a) ×ₘ f ×ₘ 𝟙 (op x) ×ₘ k) =
      (innerLeg T c hc w z ≫ fubiniLam T c hc (op z, z) b) ≫
        T.map (f.op ×ₘ 𝟙 b ×ₘ k.op ×ₘ 𝟙 z)
    have e1 : T.map (𝟙 (op a) ×ₘ f ×ₘ 𝟙 (op x) ×ₘ k) =
        T.map (𝟙 (op a) ×ₘ f ×ₘ 𝟙 (op x, x)) ≫ T.map (𝟙 (op a) ×ₘ 𝟙 b ×ₘ (𝟙 (op x) ×ₘ k)) := by
      simp [← Functor.map_comp]
    have e2 : T.map (f.op ×ₘ 𝟙 b ×ₘ 𝟙 (op x, x)) ≫ T.map (𝟙 (op a) ×ₘ 𝟙 b ×ₘ (𝟙 (op x) ×ₘ k)) =
        T.map (𝟙 (op b) ×ₘ 𝟙 b ×ₘ (𝟙 (op x) ×ₘ k)) ≫ T.map (f.op ×ₘ 𝟙 b ×ₘ 𝟙 (op x, z)) := by
      simp [← Functor.map_comp]
    have e3 : T.map (𝟙 (op b) ×ₘ 𝟙 b ×ₘ (k.op ×ₘ 𝟙 z)) ≫ T.map (f.op ×ₘ 𝟙 b ×ₘ 𝟙 (op x, z)) =
        T.map (f.op ×ₘ 𝟙 b ×ₘ k.op ×ₘ 𝟙 z) := by
      simp [← Functor.map_comp]
    rw [e1, Category.assoc, reassoc_of% fubiniLam_condition T c hc (op x, x) f, e2,
      ← reassoc_of% map_fubiniLam T c hc (𝟙 (op x) ×ₘ k) b,
      reassoc_of% innerLeg_condition T c hc w k, reassoc_of% map_fubiniLam T c hc (k.op ×ₘ 𝟙 z) b,
      e3, Category.assoc])

lemma fubiniWedge_ι (w : Wedge (fubiniInner T c hc)) (q : C × X) :
    (fubiniWedge T c hc w).ι q = innerLeg T c hc w q.2 ≫ fubiniLam T c hc (op q.2, q.2) q.1 :=
  rfl

lemma lift_innerLeg {w : Wedge (fubiniInner T c hc)} (hw : IsLimit w) {d : D}
    (f : ∀ x : X, d ⟶ ((fubiniInner T c hc).obj (op x)).obj x)
    (hf : ∀ ⦃x z : X⦄ (k : x ⟶ z), f x ≫ ((fubiniInner T c hc).obj (op x)).map k =
      f z ≫ ((fubiniInner T c hc).map k.op).app z) (x : X) :
    Wedge.IsLimit.lift hw f hf ≫ innerLeg T c hc w x = f x :=
  Wedge.IsLimit.lift_ι hw f hf x

/-- The legs of a wedge over `C × X`, typed through `T`. -/
def prodLeg (s : Wedge (fubiniProd T)) (a : C) (x : X) : s.pt ⟶ T.obj (op a, a, op x, x) :=
  s.ι (a, x)

omit c hc in
lemma prodLeg_condition (s : Wedge (fubiniProd T)) {a b : C} {x z : X} (f : a ⟶ b)
    (k : x ⟶ z) :
    prodLeg T s a x ≫ T.map (𝟙 (op a) ×ₘ f ×ₘ 𝟙 (op x) ×ₘ k) =
      prodLeg T s b z ≫ T.map (f.op ×ₘ 𝟙 b ×ₘ k.op ×ₘ 𝟙 z) :=
  Wedge.condition s (f ×ₘ k)

/-- For fixed `x`, the legs `σ_{⟨a, x⟩}` of a wedge over `C × X` form a wedge of `T(−, −, x, x)`,
which induces `d → ∫_c T(c, c, x, x)`. -/
noncomputable def fubiniLeg (s : Wedge (fubiniProd T)) (x : X) :
    s.pt ⟶ (endFunctorOf (fubiniParam T) c hc).obj (op x, x) :=
  Wedge.IsLimit.lift (hc (op x, x)) (fun a ↦ prodLeg T s a x)
    (fun _ _ f ↦ prodLeg_condition T s f (𝟙 x))

lemma fubiniLeg_fubiniLam (s : Wedge (fubiniProd T)) (a : C) (x : X) :
    fubiniLeg T c hc s x ≫ fubiniLam T c hc (op x, x) a = prodLeg T s a x :=
  Wedge.IsLimit.lift_ι (hc (op x, x)) _ _ a

lemma fubiniLeg_condition (s : Wedge (fubiniProd T)) {x z : X} (k : x ⟶ z) :
    fubiniLeg T c hc s x ≫ (endFunctorOf (fubiniParam T) c hc).map (𝟙 (op x) ×ₘ k) =
      fubiniLeg T c hc s z ≫ (endFunctorOf (fubiniParam T) c hc).map (k.op ×ₘ 𝟙 z) := by
  refine fubiniLam_hom_ext T c hc (op x, z) fun a ↦ ?_
  rw [Category.assoc, Category.assoc, map_fubiniLam, map_fubiniLam,
    reassoc_of% fubiniLeg_fubiniLam, reassoc_of% fubiniLeg_fubiniLam]
  simpa using prodLeg_condition T s (𝟙 a) k

/-- The wedge over `X` of `∫_c T(c, c, −, □)` attached to a wedge `σ` over `C × X` (the second
half of the proof of 定理 4). -/
noncomputable def fubiniWedgeInv (s : Wedge (fubiniProd T)) : Wedge (fubiniInner T c hc) :=
  Wedge.mk s.pt (fubiniLeg T c hc s) (fun _ _ k ↦ fubiniLeg_condition T c hc s k)

/-- If `μ` is an end over `X` of `∫_c T(c, c, −, □)`, the attached wedge is an end over `C × X`. -/
noncomputable def isLimitFubiniWedge {w : Wedge (fubiniInner T c hc)} (hw : IsLimit w) :
    IsLimit (fubiniWedge T c hc w) :=
  Multifork.IsLimit.mk _
    (fun s ↦ Wedge.IsLimit.lift hw (fubiniLeg T c hc s)
      (fun _ _ k ↦ fubiniLeg_condition T c hc s k))
    (fun s (q : C × X) ↦ by
      change _ ≫ innerLeg T c hc w q.2 ≫ fubiniLam T c hc (op q.2, q.2) q.1 = prodLeg T s q.1 q.2
      rw [← Category.assoc, lift_innerLeg, fubiniLeg_fubiniLam])
    (fun s m hm ↦ Wedge.IsLimit.hom_ext hw fun (x : X) ↦ by
      change m ≫ innerLeg T c hc w x = _ ≫ innerLeg T c hc w x
      rw [lift_innerLeg]
      refine fubiniLam_hom_ext T c hc (op x, x) fun a ↦ ?_
      exact (Category.assoc _ _ _).trans
        ((hm (a, x)).trans (fubiniLeg_fubiniLam T c hc s a x).symm))

/-- If `σ` is an end over `C × X`, the attached wedge is an end over `X` of `∫_c T(c, c, −, □)`. -/
noncomputable def isLimitFubiniWedgeInv {s : Wedge (fubiniProd T)} (hs : IsLimit s) :
    IsLimit (fubiniWedgeInv T c hc s) :=
  Multifork.IsLimit.mk _
    (fun t ↦ Wedge.IsLimit.lift hs (fubiniWedge T c hc t).ι
      (fun _ _ f ↦ Wedge.condition (fubiniWedge T c hc t) f))
    (fun t (x : X) ↦ fubiniLam_hom_ext T c hc (op x, x) fun a ↦ by
      change (_ ≫ fubiniLeg T c hc s x) ≫ _ = innerLeg T c hc t x ≫ _
      rw [Category.assoc, fubiniLeg_fubiniLam]
      exact Wedge.IsLimit.lift_ι hs _ _ (a, x))
    (fun t m hm ↦ Wedge.IsLimit.hom_ext hs fun (q : C × X) ↦ by
      have h := hm q.2
      change m ≫ fubiniLeg T c hc s q.2 = innerLeg T c hc t q.2 at h
      refine Eq.trans ?_ (Wedge.IsLimit.lift_ι hs _ _ q).symm
      change m ≫ prodLeg T s q.1 q.2 =
        innerLeg T c hc t q.2 ≫ fubiniLam T c hc (op q.2, q.2) q.1
      exact (congrArg (m ≫ ·) (fubiniLeg_fubiniLam T c hc s q.1 q.2).symm).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ fubiniLam T c hc (op q.2, q.2) q.1) h)))

/-- `ALGD-C2-END-04` (定理 4 (Fubini の定理), p.5–7).
Let `T : C^op × C × X^op × X → D` have an end `⟨∫_c T(c, c, u, v), λ^{u,v}⟩` for all `u, v ∈ X`
(the chosen limit wedges `c`). Then
`∫_{⟨c,x⟩∈C×X} T(c, c, x, x) ≅ ∫_{x∈X} ∫_{c∈C} T(c, c, x, x)`: one end exists iff the other
does, and then they are isomorphic. On the left `T` is a functor of `⟨c, x⟩ ∈ C × X`
(`fubiniProd`); on the right `∫_c T(c, c, −, □)` is the functor of 命題 3 (`fubiniInner`). As in
the source's proof, wedges over `X` and over `C × X` correspond (`fubiniWedge`,
`fubiniWedgeInv`), and ends go to ends (`isLimitFubiniWedge`, `isLimitFubiniWedgeInv`). -/
theorem fubini : (HasEnd (fubiniProd T) ↔ HasEnd (fubiniInner T c hc)) ∧
    ∀ [HasEnd (fubiniProd T)] [HasEnd (fubiniInner T c hc)],
      Nonempty (end_ (fubiniProd T) ≅ end_ (fubiniInner T c hc)) := by
  refine ⟨⟨fun _ ↦ ?_, fun _ ↦ ?_⟩, ?_⟩
  · exact HasLimit.mk ⟨_, isLimitFubiniWedgeInv T c hc (limit.isLimit _)⟩
  · exact HasLimit.mk ⟨_, isLimitFubiniWedge T c hc (limit.isLimit _)⟩
  · exact ⟨IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      (isLimitFubiniWedge T c hc (limit.isLimit _))⟩

end Fubini

section Swap

variable {X : Type u₃} [Category.{v₃} X]

variable (C X) in
/-- The isomorphism `X^op × X × C^op × C → C^op × C × X^op × X`, `⟨x, z, a, b⟩ ↦ ⟨a, b, x, z⟩`. -/
@[simps]
def swap4 : Xᵒᵖ × X × Cᵒᵖ × C ⥤ Cᵒᵖ × C × Xᵒᵖ × X where
  obj p := (p.2.2.1, p.2.2.2, p.1, p.2.1)
  map f := f.2.2.1 ×ₘ f.2.2.2 ×ₘ f.1 ×ₘ f.2.1

variable (T : Cᵒᵖ × C × Xᵒᵖ × X ⥤ D)

/-- A wedge over `C × X` gives a wedge over `X × C` of the swapped functor. -/
def swapWedge (s : Wedge (fubiniProd T)) : Wedge (fubiniProd (swap4 C X ⋙ T)) :=
  Wedge.mk s.pt (fun q ↦ s.ι (q.2, q.1)) (by
    rintro ⟨x, a⟩ ⟨z, b⟩ ⟨k, f⟩
    exact Wedge.condition s (f ×ₘ k))

/-- A wedge over `X × C` of the swapped functor gives a wedge over `C × X`. -/
def swapWedgeInv (s : Wedge (fubiniProd (swap4 C X ⋙ T))) : Wedge (fubiniProd T) :=
  Wedge.mk s.pt (fun q ↦ s.ι (q.2, q.1)) (by
    rintro ⟨a, x⟩ ⟨b, z⟩ ⟨f, k⟩
    exact Wedge.condition s (k ×ₘ f))

/-- An end over `C × X` gives an end over `X × C` of the swapped functor. -/
def isLimitSwapWedge {s : Wedge (fubiniProd T)} (hs : IsLimit s) : IsLimit (swapWedge T s) :=
  Multifork.IsLimit.mk _
    (fun t ↦ Wedge.IsLimit.lift hs (swapWedgeInv T t).ι
      (fun _ _ f ↦ Wedge.condition (swapWedgeInv T t) f))
    (fun _ (q : X × C) ↦ Wedge.IsLimit.lift_ι hs _ _ (q.2, q.1))
    (fun t _ hm ↦ Wedge.IsLimit.hom_ext hs fun (q : C × X) ↦
      (hm (q.2, q.1)).trans (Wedge.IsLimit.lift_ι hs (swapWedgeInv T t).ι
        (fun _ _ f ↦ Wedge.condition (swapWedgeInv T t) f) q).symm)

/-- An end over `X × C` of the swapped functor gives an end over `C × X`. -/
def isLimitSwapWedgeInv {s : Wedge (fubiniProd (swap4 C X ⋙ T))} (hs : IsLimit s) :
    IsLimit (swapWedgeInv T s) :=
  Multifork.IsLimit.mk _
    (fun t ↦ Wedge.IsLimit.lift hs (swapWedge T t).ι
      (fun _ _ f ↦ Wedge.condition (swapWedge T t) f))
    (fun _ (q : C × X) ↦ Wedge.IsLimit.lift_ι hs _ _ (q.2, q.1))
    (fun t _ hm ↦ Wedge.IsLimit.hom_ext hs fun (q : X × C) ↦
      (hm (q.2, q.1)).trans (Wedge.IsLimit.lift_ι hs (swapWedge T t).ι
        (fun _ _ f ↦ Wedge.condition (swapWedge T t) f) q).symm)

lemma hasEnd_swap_iff : HasEnd (fubiniProd T) ↔ HasEnd (fubiniProd (swap4 C X ⋙ T)) :=
  ⟨fun _ ↦ HasLimit.mk ⟨_, isLimitSwapWedge T (limit.isLimit _)⟩,
    fun _ ↦ HasLimit.mk ⟨_, isLimitSwapWedgeInv T (limit.isLimit _)⟩⟩

/-- `∫_{⟨c,x⟩∈C×X} T(c, c, x, x) ≅ ∫_{⟨x,c⟩∈X×C} T(c, c, x, x)`. -/
noncomputable def endSwapIso [HasEnd (fubiniProd T)] [HasEnd (fubiniProd (swap4 C X ⋙ T))] :
    end_ (fubiniProd T) ≅ end_ (fubiniProd (swap4 C X ⋙ T)) :=
  IsLimit.conePointUniqueUpToIso
    (isLimitSwapWedge T (limit.isLimit (multicospanIndexEnd (fubiniProd T)).multicospan))
    (limit.isLimit (multicospanIndexEnd (fubiniProd (swap4 C X ⋙ T))).multicospan)

variable (c : ∀ p, Wedge ((fubiniParam T).obj p)) (hc : ∀ p, IsLimit (c p))
  (c' : ∀ p, Wedge ((fubiniParam (swap4 C X ⋙ T)).obj p)) (hc' : ∀ p, IsLimit (c' p))

/-- `ALGD-C2-END-R01` (prose after 定理 4, p.7).
When the ends exist, ends commute: `∫_{x∈X} ∫_{c∈C} T(c, c, x, x) ≅ ∫_{c∈C} ∫_{x∈X} T(c, c, x, x)`.
Here `c` are chosen ends `∫_c T(c, c, u, v)` and `c'` are chosen ends `∫_x T(a, b, x, x)` (ends of
the swapped functor `swap4 C X ⋙ T`). As in 定理 4, one iterated end exists iff the other does.
The proof applies 定理 4 to both sides and identifies the ends over `C × X` and over `X × C`
(`endSwapIso`). Dually, coends commute (`coend_comm`). -/
theorem end_comm :
    (HasEnd (fubiniInner T c hc) ↔ HasEnd (fubiniInner (swap4 C X ⋙ T) c' hc')) ∧
    ∀ [HasEnd (fubiniInner T c hc)] [HasEnd (fubiniInner (swap4 C X ⋙ T) c' hc')],
      Nonempty (end_ (fubiniInner T c hc) ≅ end_ (fubiniInner (swap4 C X ⋙ T) c' hc')) := by
  refine ⟨(fubini T c hc).1.symm.trans ((hasEnd_swap_iff T).trans (fubini _ c' hc').1), ?_⟩
  intro _ _
  have : HasEnd (fubiniProd T) := (fubini T c hc).1.2 inferInstance
  have : HasEnd (fubiniProd (swap4 C X ⋙ T)) := (hasEnd_swap_iff T).1 inferInstance
  exact ⟨(fubini T c hc).2.some.symm ≪≫ endSwapIso T ≪≫ (fubini _ c' hc').2.some⟩

end Swap

section CoendComm

variable {X : Type u₃} [Category.{v₃} X]

/-- The source's `T^op` for `T : C^op × C × X^op × X → D`, as a functor
`(C^op)^op × C^op × (X^op)^op × X^op → D^op`. By 定義 (コエンド) (`ALGD-C2-END-D04`), coends of
`T` over `C` or `X` are ends of `T^op` over `C^op` or `X^op`. -/
@[simps]
def dual4 (T : Cᵒᵖ × C × Xᵒᵖ × X ⥤ D) : Cᵒᵖᵒᵖ × Cᵒᵖ × Xᵒᵖᵒᵖ × Xᵒᵖ ⥤ Dᵒᵖ where
  obj p := op (T.obj (p.1.unop, p.2.1.unop, p.2.2.1.unop, p.2.2.2.unop))
  map f := (T.map (f.1.unop ×ₘ f.2.1.unop ×ₘ f.2.2.1.unop ×ₘ f.2.2.2.unop)).op
  map_id p := congrArg Quiver.Hom.op (T.map_id (p.1.unop, p.2.1.unop, p.2.2.1.unop, p.2.2.2.unop))
  map_comp f g := congrArg Quiver.Hom.op
    (T.map_comp (g.1.unop ×ₘ g.2.1.unop ×ₘ g.2.2.1.unop ×ₘ g.2.2.2.unop)
      (f.1.unop ×ₘ f.2.1.unop ×ₘ f.2.2.1.unop ×ₘ f.2.2.2.unop))

/-- Dually to `ALGD-C2-END-R01` (prose after 定理 4, p.7), coends commute:
`∫^{x∈X} ∫^{c∈C} T(c, c, x, x) ≅ ∫^{c∈C} ∫^{x∈X} T(c, c, x, x)`. With coends defined as ends of
`T^op` (定義 (コエンド)), this is `end_comm` for `C^op`, `X^op`, `D^op` and `T^op = dual4 T`: the
chosen wedges `c`, `c'` are the chosen coends of `T`, and the iterated ends in `D^op` are the
iterated coends. -/
theorem coend_comm (T : Cᵒᵖ × C × Xᵒᵖ × X ⥤ D)
    (c : ∀ p, Wedge ((fubiniParam (dual4 T)).obj p)) (hc : ∀ p, IsLimit (c p))
    (c' : ∀ p, Wedge ((fubiniParam (swap4 Cᵒᵖ Xᵒᵖ ⋙ dual4 T)).obj p))
    (hc' : ∀ p, IsLimit (c' p)) :
    (HasEnd (fubiniInner (dual4 T) c hc) ↔
        HasEnd (fubiniInner (swap4 Cᵒᵖ Xᵒᵖ ⋙ dual4 T) c' hc')) ∧
    ∀ [HasEnd (fubiniInner (dual4 T) c hc)]
      [HasEnd (fubiniInner (swap4 Cᵒᵖ Xᵒᵖ ⋙ dual4 T) c' hc')],
      Nonempty (end_ (fubiniInner (dual4 T) c hc) ≅
        end_ (fubiniInner (swap4 Cᵒᵖ Xᵒᵖ ⋙ dual4 T) c' hc')) :=
  end_comm (dual4 T) c hc c' hc'

end CoendComm

/-! ## Ends as limits -/

/-- `ALGD-C2-END-05` (定理 5, p.8).
If `C` is small and `D` is complete, every `T : C^op × C → D` has an end. -/
theorem hasEnd_of_hasLimits {C : Type v₂} [SmallCategory C] [HasLimits D] (T : Cᵒᵖ ⥤ C ⥤ D) :
    HasEnd T :=
  inferInstance

/-- The image `⟨F e, F(λ_a)⟩` of a wedge `⟨e, λ⟩` of `T` under `F : D → X`, a wedge of `F ∘ T`. -/
abbrev mapWedge {X : Type u₃} [Category.{v₃} X] {T : Cᵒᵖ ⥤ C ⥤ D} (c : Wedge T) (F : D ⥤ X) :
    Wedge (T ⋙ (whiskeringRight C D X).obj F) :=
  Wedge.mk (F.obj c.pt) (fun j ↦ F.map (c.ι j)) (fun _ _ f ↦ (F.map_comp _ _).symm.trans
    ((congrArg F.map (Wedge.condition c f)).trans (F.map_comp _ _)))

/-- `ALGD-C2-END-06` (定理 6, p.8).
A continuous functor `F : D → X` commutes with ends: if `⟨e, λ⟩` is an end of `T`, then
`⟨F e, F(λ_a)⟩` is an end of `F ∘ T`, so `F(∫_c T(c, c)) ≅ ∫_c F(T(c, c))`. -/
noncomputable def isLimitMapWedge {X : Type u₃} [Category.{v₃} X] {T : Cᵒᵖ ⥤ C ⥤ D}
    {c : Wedge T} (hc : IsLimit c) (F : D ⥤ X)
    [PreservesLimit (multicospanIndexEnd T).multicospan F] : IsLimit (mapWedge c F) := by
  let hF := isLimitOfPreserves F hc
  refine Multifork.IsLimit.mk _ (fun s ↦ hF.lift
    { pt := s.pt
      π :=
        { app := fun
            | .left j => s.ι j
            | .right f => s.ι f.left ≫ F.map ((T.obj (op f.left)).map f.hom)
          naturality := ?_ } }) (fun s j ↦ hF.fac _ (.left j)) (fun s m hm ↦ ?_)
  · rintro (j | f) (j' | f') (_ | _ | _)
    · simp
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact Category.id_comp _
    · exact (Category.id_comp _).trans (Wedge.condition s f'.hom)
    · simp
  · refine hF.hom_ext fun j ↦ ?_
    rw [hF.fac]
    rcases j with j | f
    · exact hm j
    · rw [← (F.mapCone c).w (WalkingMulticospan.Hom.fst f)]
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (hm f.left))

/-- `ALGD-C2-END-07` (系 7, p.8).
`Hom_D(d, ∫_c T(c, c)) ≅ ∫_c Hom_D(d, T(c, c))`: for an end `⟨e, λ⟩` of `T`, the set
`Hom_D(d, e)` with the maps `h ↦ λ_a ∘ h` is an end in Set, by 定理 6 since `Hom_D(d, −)` is
continuous. -/
noncomputable def isLimitCoyonedaWedge {T : Cᵒᵖ ⥤ C ⥤ D} {c : Wedge T} (hc : IsLimit c)
    (d : D) : IsLimit (mapWedge c (coyoneda.obj (op d))) :=
  isLimitMapWedge hc (coyoneda.obj (op d))

lemma mapWedge_coyoneda_ι {T : Cᵒᵖ ⥤ C ⥤ D} (c : Wedge T) (d : D) (j : C) (h : d ⟶ c.pt) :
    (mapWedge c (coyoneda.obj (op d))).ι j h = h ≫ c.ι j :=
  rfl

/-- The functor `C^op × C^op → Set`, `(a, b) ↦ Hom_D(T(a, b), d)`, curried as
`Cᵒᵖᵒᵖ ⥤ Cᵒᵖ ⥤ Type`, whose end over `C^op` is `Hom_D(∫^c T(c, c), d)`. -/
abbrev homToFunctor (T : Cᵒᵖ ⥤ C ⥤ D) (d : D) : Cᵒᵖᵒᵖ ⥤ Cᵒᵖ ⥤ Type v₂ :=
  T.op ⋙ Functor.opHom C D ⋙ (whiskeringRight Cᵒᵖ Dᵒᵖ (Type v₂)).obj (yoneda.obj d)

/-- `ALGD-C2-END-R03` (prose after 系 7, p.8, with the ※).
Dually, `Hom_D(∫^c T(c, c), d) ≅ ∫_{c∈C^op} Hom_D(T(c, c), d)`: for a coend `⟨e, λ⟩` of `T`, the
set `Hom_D(e, d)` with the maps `h ↦ h ∘ λ_a` is an end in Set over `C^op`. -/
noncomputable def isLimitHomCoendWedge {T : Cᵒᵖ ⥤ C ⥤ D} {c : Cowedge T} (hc : IsColimit c)
    (d : D) :
    IsLimit (Wedge.mk (F := homToFunctor T d) (c.pt ⟶ d) (fun j ↦ ↾fun h ↦ c.π j.unop ≫ h)
      (fun i j f ↦ by
        ext h
        have := Cowedge.condition c f.unop
        change (T.obj (op i.unop)).map f.unop ≫ c.π i.unop ≫ h =
          (T.map f.unop.op).app j.unop ≫ c.π j.unop ≫ h
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ h) this.symm).trans (Category.assoc _ _ _)))) := by
  let L : ∀ s : Multifork (multicospanIndexEnd (homToFunctor T d)), s.pt → (c.pt ⟶ d) :=
    fun s x ↦ Cowedge.IsColimit.desc hc (fun a ↦ s.ι (op a) x)
      (fun a b g ↦ (ConcreteCategory.congr_hom (Wedge.condition s g.op) x).symm)
  have hL : ∀ s x a, c.π a ≫ L s x = s.ι (op a) x := fun s x a ↦
    Cowedge.IsColimit.π_desc hc _ _ a
  refine Multifork.IsLimit.mk _ (fun s ↦ ↾(L s)) (fun s j ↦ ?_) (fun s m hm ↦ ?_)
  · ext x
    exact hL s x j.unop
  · ext x
    exact Cowedge.IsColimit.hom_ext hc fun a ↦
      (ConcreteCategory.congr_hom (hm (op a)) x).trans (hL s x a).symm

/-- `ALGD-C2-END-R02` (prose, p.7–8).
An end is an equalizer: `∫_c T(c, c)` is the equalizer of `s, t : ∏_{c ∈ Ob(C)} T(c, c) ⇉
∏_{f ∈ Mor(C)} T(dom f, cod f)`, induced by `T(id, f)` and `T(f, id)`. -/
noncomputable def endIsoEqualizer (T : Cᵒᵖ ⥤ C ⥤ D) [HasEnd T]
    [HasProduct (multicospanIndexEnd T).left] [HasProduct (multicospanIndexEnd T).right] :
    end_ T ≅ equalizer (multicospanIndexEnd T).fstPiMap (multicospanIndexEnd T).sndPiMap :=
  Multiequalizer.isoEqualizer _

/-- `ALGD-C2-END-R04` (prose, p.8).
Limits are ends: for `F : J → C`, view `F` as `F ∘ P₂ : J^op × J → C`. A cone `⟨a, θ⟩` over `F` is
a wedge for `F ∘ P₂`, and it is a limit iff it is an end, so `∫_{j∈J} F(j) = lim F`. -/
theorem nonempty_isLimit_iff_end {J : Type u₃} [Category.{v₃} J] {F : J ⥤ C} (c : Cone F) :
    Nonempty (IsLimit c) ↔ Nonempty (IsLimit (Wedge.mk (F := (Functor.const Jᵒᵖ).obj F) c.pt
      c.π.app (fun i j f ↦ by simp))) := by
  constructor
  · rintro ⟨hc⟩
    refine ⟨Multifork.IsLimit.mk _ (fun s ↦ hc.lift
      { pt := s.pt
        π := { app := s.ι, naturality := fun i j f ↦
          (Category.id_comp _).trans ((Wedge.condition s f).trans (Category.comp_id _)).symm } })
      (fun s j ↦ hc.fac _ j) (fun s m hm ↦ hc.hom_ext fun j ↦ ?_)⟩
    rw [hc.fac]
    exact hm j
  · rintro ⟨hw⟩
    exact ⟨{ lift := fun s ↦ Wedge.IsLimit.lift hw s.π.app (fun i j f ↦ by simp),
              fac := fun s j ↦ Wedge.IsLimit.lift_ι hw _ _ j,
              uniq := fun s m hm ↦ Wedge.IsLimit.hom_ext hw fun j ↦
                (hm j).trans (Wedge.IsLimit.lift_ι hw _ _ j).symm }⟩

/-! ## Copowers and powers -/

section Copower

variable {E : Type u} [Category.{v} E]

/-- The source's copowers (定義, p.9): `⟨c, u⟩` with `u : x → Hom_E(a, c)` a universal arrow from
`x ∈ Set` to `Hom_E(a, −)`. -/
def IsCopower (x : Type v) (a c : E) (u : x → (a ⟶ c)) : Prop :=
  ∀ (b : E) (g : x → (a ⟶ b)), ∃! h : c ⟶ b, ∀ i, u i ≫ h = g i

/-- The source's powers (定義, p.9): `⟨c, u⟩` with `u : x → Hom_E(c, a)` a universal arrow from
`x ∈ Set` to `Hom_E(−, a)`. -/
def IsPower (x : Type v) (a c : E) (u : x → (c ⟶ a)) : Prop :=
  ∀ (b : E) (g : x → (b ⟶ a)), ∃! h : b ⟶ c, ∀ i, h ≫ u i = g i

/-- `ALGD-C2-END-D05` (定義 (copower), p.9).
`c = x ⊙ a` is a copower iff `u : x → Hom_E(a, c)` is a universal arrow from `x` to `Hom_E(a, −)`,
i.e. an initial object of `x ↓ Hom_E(a, −)`. -/
theorem isCopower_iff (x : Type v) (a c : E) (u : x → (a ⟶ c)) :
    IsCopower x a c u ↔
      Nonempty (IsInitial (StructuredArrow.mk (Y := c) (↾u : x ⟶ (coyoneda.obj (op a)).obj c))) := by
  constructor
  · intro h
    refine ⟨IsInitial.ofUniqueHom (fun s ↦ StructuredArrow.homMk (h s.right (s.hom ·)).exists.choose
      ?_) fun s m ↦ ?_⟩
    · ext i
      exact (h s.right (s.hom ·)).exists.choose_spec i
    · ext
      exact (h s.right (s.hom ·)).unique (fun i ↦ ConcreteCategory.congr_hom (StructuredArrow.w m) i)
        (h s.right (s.hom ·)).exists.choose_spec
  · rintro ⟨hI⟩ b g
    let s : StructuredArrow x (coyoneda.obj (op a)) := StructuredArrow.mk (Y := b) (↾g)
    refine ⟨(hI.to s).right, fun i ↦ ConcreteCategory.congr_hom (StructuredArrow.w (hI.to s)) i,
      fun h' hh' ↦ ?_⟩
    have := hI.hom_ext (StructuredArrow.homMk h' (by ext i; exact hh' i) :
      StructuredArrow.mk (Y := c) (↾u : x ⟶ (coyoneda.obj (op a)).obj c) ⟶ s) (hI.to s)
    exact congrArg CommaMorphism.right this

/-- `ALGD-C2-END-D06` (定義 (power), p.9).
`c = x ⋔ a` is a power iff `u : x → Hom_E(c, a)` is a universal arrow from `x` to
`Hom_E(−, a) : E^op → Set`, i.e. an initial object of `x ↓ Hom_E(−, a)`. -/
theorem isPower_iff (x : Type v) (a c : E) (u : x → (c ⟶ a)) :
    IsPower x a c u ↔
      Nonempty (IsInitial (StructuredArrow.mk (Y := op c) (↾u : x ⟶ (yoneda.obj a).obj (op c)))) := by
  constructor
  · intro h
    refine ⟨IsInitial.ofUniqueHom
      (fun s ↦ StructuredArrow.homMk (h s.right.unop (s.hom ·)).exists.choose.op ?_)
      fun s m ↦ ?_⟩
    · ext i
      exact (h s.right.unop (s.hom ·)).exists.choose_spec i
    · ext
      have key : m.right.unop = (h s.right.unop (s.hom ·)).exists.choose :=
        (h s.right.unop (s.hom ·)).unique
          (fun i ↦ ConcreteCategory.congr_hom (StructuredArrow.w m) i)
          (h s.right.unop (s.hom ·)).exists.choose_spec
      exact key
  · rintro ⟨hI⟩ b g
    let s : StructuredArrow x (yoneda.obj a) := StructuredArrow.mk (Y := op b) (↾g)
    refine ⟨(hI.to s).right.unop, fun i ↦ ConcreteCategory.congr_hom (StructuredArrow.w (hI.to s)) i,
      fun h' hh' ↦ ?_⟩
    have := hI.hom_ext (StructuredArrow.homMk h'.op (by ext i; exact hh' i) :
      StructuredArrow.mk (Y := op c) (↾u : x ⟶ (yoneda.obj a).obj (op c)) ⟶ s) (hI.to s)
    exact congrArg (fun m ↦ (CommaMorphism.right m).unop) this

/-- `ALGD-C2-END-R05` (prose after 定義, p.9).
By the universal property, `Hom_E(x ⊙ a, b) ≅ Hom_Set(x, Hom_E(a, b))` and
`Hom_E(b, x ⋔ a) ≅ Hom_Set(x, Hom_E(b, a))`; if all copowers (powers) of `a` exist, then
`− ⊙ a ⊣ Hom_E(a, −) : Set → E` and `− ⋔ a ⊣ Hom_E(−, a) : Set → E^op`. -/
theorem copower_power_adjunctions (a : E) :
    (∀ (x : Type v) (c : E) (u : x → (a ⟶ c)), IsCopower x a c u →
      ∀ b, Function.Bijective fun h : c ⟶ b ↦ fun i ↦ u i ≫ h) ∧
    (∀ (x : Type v) (c : E) (u : x → (c ⟶ a)), IsPower x a c u →
      ∀ b, Function.Bijective fun h : b ⟶ c ↦ fun i ↦ h ≫ u i) ∧
    ((∀ x : Type v, ∃ (c : E) (u : x → (a ⟶ c)), IsCopower x a c u) →
      (coyoneda.obj (op a)).IsRightAdjoint) ∧
    ((∀ x : Type v, ∃ (c : E) (u : x → (c ⟶ a)), IsPower x a c u) →
      (yoneda.obj a).IsRightAdjoint) := by
  refine ⟨fun x c u hu b ↦ ⟨fun h h' e ↦ ?_, fun g ↦ ?_⟩, fun x c u hu b ↦
    ⟨fun h h' e ↦ ?_, fun g ↦ ?_⟩, fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (hu b _).unique (fun i ↦ rfl) (fun i ↦ (congrFun e i).symm)
  · exact ⟨(hu b g).exists.choose, funext (hu b g).exists.choose_spec⟩
  · exact (hu b _).unique (fun i ↦ rfl) (fun i ↦ (congrFun e i).symm)
  · exact ⟨(hu b g).exists.choose, funext (hu b g).exists.choose_spec⟩
  · have : ∀ x : Type v, HasInitial (StructuredArrow x (coyoneda.obj (op a))) := fun x ↦ by
      obtain ⟨c, u, hu⟩ := h x
      exact ((isCopower_iff x a c u).1 hu).some.hasInitial
    exact isRightAdjointOfStructuredArrowInitials _
  · have : ∀ x : Type v, HasInitial (StructuredArrow x (yoneda.obj a)) := fun x ↦ by
      obtain ⟨c, u, hu⟩ := h x
      exact ((isPower_iff x a c u).1 hu).some.hasInitial
    exact isRightAdjointOfStructuredArrowInitials _

/-- `ALGD-C2-END-08` (例 8, p.9).
In Set, `x ⊙ a ≅ x × a` (since `− × a ⊣ Hom_Set(a, −)`) and `x ⋔ a ≅ Hom_Set(x, a) = a^x`. -/
theorem isCopower_prod_isPower_fun (x a : Type v) :
    IsCopower x a (x × a) (fun i ↦ ↾fun y ↦ (i, y)) ∧
      IsPower x a (x → a) (fun i ↦ ↾fun φ ↦ φ i) := by
  refine ⟨fun b g ↦ ⟨↾fun p ↦ g p.1 p.2, fun i ↦ rfl, fun h hh ↦ ?_⟩,
    fun b g ↦ ⟨↾fun y i ↦ g i y, fun i ↦ rfl, fun h hh ↦ ?_⟩⟩
  · ext ⟨i, y⟩
    change h (i, y) = g i y
    exact ConcreteCategory.congr_hom (hh i) y
  · ext y i
    change h y i = g i y
    exact ConcreteCategory.congr_hom (hh i) y

/-- A copower `x ⊙ a` is a coproduct of the constant family `a` indexed by `x`. -/
theorem isCopower_iff_isColimit (x : Type v) (a c : E) (u : x → (a ⟶ c)) :
    IsCopower x a c u ↔ Nonempty (IsColimit (Cofan.mk (f := fun _ : x ↦ a) c u)) := by
  constructor
  · intro h
    exact ⟨Cofan.IsColimit.mk _ (fun t ↦ (h t.pt t.inj).exists.choose)
      (fun t i ↦ (h t.pt t.inj).exists.choose_spec i)
      (fun t m hm ↦ (h t.pt t.inj).unique hm (h t.pt t.inj).exists.choose_spec)⟩
  · rintro ⟨hc⟩ b g
    refine ⟨Cofan.IsColimit.desc hc g, fun i ↦ Cofan.IsColimit.fac hc g i, fun m hm ↦ ?_⟩
    exact Cofan.IsColimit.hom_ext hc _ _ fun i ↦ (hm i).trans (Cofan.IsColimit.fac hc g i).symm

/-- A power `x ⋔ a` is a product of the constant family `a` indexed by `x`. -/
theorem isPower_iff_isLimit (x : Type v) (a c : E) (u : x → (c ⟶ a)) :
    IsPower x a c u ↔ Nonempty (IsLimit (Fan.mk (f := fun _ : x ↦ a) c u)) := by
  constructor
  · intro h
    exact ⟨Fan.IsLimit.mk _ (fun t ↦ (h t.pt t.proj).exists.choose)
      (fun t i ↦ (h t.pt t.proj).exists.choose_spec i)
      (fun t m hm ↦ (h t.pt t.proj).unique hm (h t.pt t.proj).exists.choose_spec)⟩
  · rintro ⟨hc⟩ b g
    refine ⟨Fan.IsLimit.lift hc g, fun i ↦ Fan.IsLimit.fac hc g i, fun m hm ↦ ?_⟩
    exact Fan.IsLimit.hom_ext hc _ _ fun i ↦ (hm i).trans (Fan.IsLimit.fac hc g i).symm

end Copower

/-! ## Kan extensions as coends (定理 9) -/

section KanCoend

variable {U : Type u₃} [Category.{v₃} U] (F : C ⥤ D) (E : C ⥤ U)

section Left

variable [∀ (c' c : C) (d : D), HasCoproduct fun _ : F.obj c' ⟶ d ↦ E.obj c]

/-- `(c', c) ↦ Hom_D(F c', d) ⊙ E c : C^op × C → U`, with the copowers taken as coproducts. -/
@[simps]
noncomputable abbrev copowerFunctor (d : D) : Cᵒᵖ ⥤ C ⥤ U where
  obj c' :=
    { obj := fun c ↦ ∐ fun _ : F.obj c'.unop ⟶ d ↦ E.obj c
      map := fun g ↦ Limits.Sigma.map fun _ ↦ E.map g
      map_id := fun c ↦ by apply Sigma.hom_ext; intro; simp
      map_comp := fun g g' ↦ by apply Sigma.hom_ext; intro; simp }
  map h :=
    { app := fun c ↦ Sigma.map' (fun φ ↦ F.map h.unop ≫ φ) fun _ ↦ 𝟙 (E.obj c)
      naturality := fun c c₂ g ↦ by apply Sigma.hom_ext; intro; simp }
  map_id c' := by ext c φ; simp
  map_comp h h' := by ext c φ; simp

@[ext]
lemma copowerFunctor_hom_ext {d : D} {c' : Cᵒᵖ} {c : C} {X : U}
    {f g : ((copowerFunctor F E d).obj c').obj c ⟶ X}
    (h : ∀ φ : F.obj c'.unop ⟶ d, Sigma.ι (fun _ ↦ E.obj c) φ ≫ f = Sigma.ι _ φ ≫ g) : f = g :=
  Sigma.hom_ext _ _ h

/-- Postcomposition with `d → d'` induces `Hom_D(F c', d) ⊙ E c → Hom_D(F c', d') ⊙ E c`. -/
@[simps]
noncomputable def copowerMap {d d' : D} (h : d ⟶ d') :
    copowerFunctor F E d ⟶ copowerFunctor F E d' where
  app c' :=
    { app := fun c ↦ Sigma.map' (fun φ ↦ φ ≫ h) fun _ ↦ 𝟙 (E.obj c)
      naturality := fun c c₂ g ↦ by ext; simp }
  naturality c' c'' g := by ext c φ; simp

variable [∀ d, HasCoend (copowerFunctor F E d)]

/-- The functor `T : D → U`, `T d = ∫^c Hom_D(F c, d) ⊙ E c`, of the proof of 定理 9. -/
@[simps]
noncomputable abbrev coendKan : D ⥤ U where
  obj d := coend (copowerFunctor F E d)
  map h := coend.map (copowerMap F E h)
  map_id d := by ext c φ; simp
  map_comp h h' := by ext c φ; simp

/-- The morphism `E c → Hom_D(F c, d) ⊙ E c → ∫^c Hom_D(F c, d) ⊙ E c` at `φ : F c → d`. -/
noncomputable def coendLeg (d : D) (c : C) (φ : F.obj c ⟶ d) :
    E.obj c ⟶ (coendKan F E).obj d :=
  Sigma.ι (fun _ : F.obj c ⟶ d ↦ E.obj c) φ ≫ coend.ι (copowerFunctor F E d) c

lemma map_coendLeg (d : D) {c c₂ : C} (g : c ⟶ c₂) (ψ : F.obj c₂ ⟶ d) :
    E.map g ≫ coendLeg F E d c₂ ψ = coendLeg F E d c (F.map g ≫ ψ) := by
  have := coend.condition (copowerFunctor F E d) g
  have h := Sigma.ι _ ψ ≫= this
  simp at h
  simp only [coendLeg]
  exact h.symm

lemma coendLeg_map {d d' : D} (c : C) (φ : F.obj c ⟶ d) (h : d ⟶ d') :
    coendLeg F E d c φ ≫ coend.map (copowerMap F E h) = coendLeg F E d' c (φ ≫ h) := by
  simp [coendLeg]

/-- The unit `E ⇒ T ∘ F`, `E c → Hom_D(F c, F c) ⊙ E c → T(F c)` at `id_{F c}`. -/
@[simps]
noncomputable def coendUnit : E ⟶ F ⋙ coendKan F E where
  app c := coendLeg F E (F.obj c) c (𝟙 (F.obj c))
  naturality c c₂ g := by
    simp only [Functor.comp_map]
    rw [map_coendLeg, coendLeg_map]
    simp

/-- The left extension `⟨T, E ⇒ T ∘ F⟩` of `E` along `F`. -/
noncomputable abbrev coendLeftExtension : LeftExtension F E :=
  LeftExtension.mk (coendKan F E) (coendUnit F E)

lemma coendLeftExtension_coconeAt_ι (d : D) (g : CostructuredArrow F d) :
    ((coendLeftExtension F E).coconeAt d).ι.app g = coendLeg F E d g.left g.hom := by
  simp [coendLeg_map]

/-- For each `d`, the cocone `⟨T d, E c → T d⟩` over `F ↓ d` is a colimit. -/
noncomputable def isPointwiseLeftKanExtensionCoend :
    (coendLeftExtension F E).IsPointwiseLeftKanExtension := fun d ↦
  { desc := fun s ↦ coend.desc (fun c ↦ Sigma.desc fun φ ↦ s.ι.app (CostructuredArrow.mk φ))
      (fun i j g ↦ by
        ext ψ
        have := s.w (CostructuredArrow.homMk' (CostructuredArrow.mk ψ) g)
        simp at this ⊢
        exact this.symm)
    fac := fun s g ↦ by
      rw [coendLeftExtension_coconeAt_ι]
      simp [coendLeg]
      rfl
    uniq := fun s m hm ↦ by
      refine coend.hom_ext fun c ↦ ?_
      ext φ
      have := hm (CostructuredArrow.mk φ)
      rw [coendLeftExtension_coconeAt_ι] at this
      simp [coendLeg] at this ⊢
      exact this }

/-- `ALGD-C2-END-09` (定理 9, p.9–10).
Let `F : C → D` and `E : C → U`. Suppose the copowers `Hom_D(F c', d) ⊙ E c` exist for all
`c, c' ∈ C` and `d ∈ D` (as coproducts of constant families, see `isCopower_iff_isColimit`), and the
coend `∫^c Hom_D(F c, d) ⊙ E c` exists for every `d ∈ D`. Then the pointwise left Kan extension of
`E` along `F` exists. It is `T d = ∫^c Hom_D(F c, d) ⊙ E c` (`coendKan`, a functor of `d` as in
命題 3) with the unit `E c → Hom_D(F c, F c) ⊙ E c → T(F c)` at `id_{F c}`, so
`F†E ≅ ∫^c Hom_D(F c, −) ⊙ E c` (`leftKanExtensionIsoCoendKan`). -/
theorem coendKan_isPointwiseLeftKanExtension :
    Nonempty (coendLeftExtension F E).IsPointwiseLeftKanExtension ∧
      F.HasPointwiseLeftKanExtension E ∧ (coendKan F E).IsLeftKanExtension (coendUnit F E) :=
  ⟨⟨isPointwiseLeftKanExtensionCoend F E⟩,
    (isPointwiseLeftKanExtensionCoend F E).hasPointwiseLeftKanExtension,
    (isPointwiseLeftKanExtensionCoend F E).isLeftKanExtension⟩

/-- `F†E ≅ ∫^c Hom_D(F c, −) ⊙ E c`. -/
noncomputable def leftKanExtensionIsoCoendKan :
    have := (isPointwiseLeftKanExtensionCoend F E).hasLeftKanExtension
    F.leftKanExtension E ≅ coendKan F E :=
  have := (isPointwiseLeftKanExtensionCoend F E).hasLeftKanExtension
  have : (coendKan F E).IsLeftKanExtension (coendUnit F E) :=
    (isPointwiseLeftKanExtensionCoend F E).isLeftKanExtension
  leftKanExtensionUnique _ (F.leftKanExtensionUnit E) _ (coendUnit F E)

end Left

section Right

variable [∀ (c' c : C) (d : D), HasProduct fun _ : d ⟶ F.obj c' ↦ E.obj c]

/-- `(c', c) ↦ Hom_D(d, F c') ⋔ E c : C^op × C → U`, with the powers taken as products. -/
@[simps]
noncomputable abbrev powerFunctor (d : D) : Cᵒᵖ ⥤ C ⥤ U where
  obj c' :=
    { obj := fun c ↦ ∏ᶜ fun _ : d ⟶ F.obj c'.unop ↦ E.obj c
      map := fun g ↦ Limits.Pi.map fun _ ↦ E.map g
      map_id := fun c ↦ by apply Pi.hom_ext; intro; simp
      map_comp := fun g g' ↦ by apply Pi.hom_ext; intro; simp }
  map h :=
    { app := fun c ↦ Pi.map' (fun ψ ↦ ψ ≫ F.map h.unop) fun _ ↦ 𝟙 (E.obj c)
      naturality := fun c c₂ g ↦ by apply Pi.hom_ext; intro; simp }
  map_id c' := by ext c φ; simp
  map_comp h h' := by ext c φ; simp

@[ext]
lemma powerFunctor_hom_ext {d : D} {c' : Cᵒᵖ} {c : C} {X : U}
    {f g : X ⟶ ((powerFunctor F E d).obj c').obj c}
    (h : ∀ φ : d ⟶ F.obj c'.unop, f ≫ Pi.π (fun _ ↦ E.obj c) φ = g ≫ Pi.π _ φ) : f = g :=
  Pi.hom_ext _ _ h

/-- Precomposition with `d → d'` induces `Hom_D(d, F c') ⋔ E c → Hom_D(d', F c') ⋔ E c`. -/
@[simps]
noncomputable def powerMap {d d' : D} (h : d ⟶ d') :
    powerFunctor F E d ⟶ powerFunctor F E d' where
  app c' :=
    { app := fun c ↦ Pi.map' (fun ψ ↦ h ≫ ψ) fun _ ↦ 𝟙 (E.obj c)
      naturality := fun c c₂ g ↦ by ext; simp }
  naturality c' c'' g := by ext c φ; simp

variable [∀ d, HasEnd (powerFunctor F E d)]

/-- The functor `D → U`, `d ↦ ∫_c Hom_D(d, F c) ⋔ E c`. -/
@[simps]
noncomputable abbrev endKan : D ⥤ U where
  obj d := end_ (powerFunctor F E d)
  map h := end_.map (powerMap F E h)
  map_id d := by ext c φ; simp
  map_comp h h' := by ext c φ; simp

/-- The morphism `∫_c Hom_D(d, F c) ⋔ E c → Hom_D(d, F c) ⋔ E c → E c` at `φ : d → F c`. -/
noncomputable def endLeg (d : D) (c : C) (φ : d ⟶ F.obj c) :
    end_ (powerFunctor F E d) ⟶ E.obj c :=
  end_.π (powerFunctor F E d) c ≫ Pi.π (fun _ : d ⟶ F.obj c ↦ E.obj c) φ

lemma endLeg_map (d : D) {c c₂ : C} (g : c ⟶ c₂) (ψ : d ⟶ F.obj c) :
    endLeg F E d c ψ ≫ E.map g = endLeg F E d c₂ (ψ ≫ F.map g) := by
  have h := end_.condition (powerFunctor F E d) g =≫ Pi.π _ ψ
  simp at h
  simp only [endLeg, Category.assoc]
  exact h

lemma map_endLeg {d d' : D} (c : C) (φ : d' ⟶ F.obj c) (h : d ⟶ d') :
    end_.map (powerMap F E h) ≫ endLeg F E d' c φ = endLeg F E d c (h ≫ φ) := by
  simp [endLeg]

/-- The counit `T ∘ F ⇒ E`, `T(F c) → Hom_D(F c, F c) ⋔ E c → E c` at `id_{F c}`. -/
@[simps]
noncomputable def endCounit : F ⋙ endKan F E ⟶ E where
  app c := endLeg F E (F.obj c) c (𝟙 (F.obj c))
  naturality c c₂ g := by
    simp only [Functor.comp_map]
    rw [endLeg_map, map_endLeg]
    simp

/-- The right extension `⟨T, T ∘ F ⇒ E⟩` of `E` along `F`. -/
noncomputable abbrev endRightExtension : RightExtension F E :=
  RightExtension.mk (endKan F E) (endCounit F E)

lemma endRightExtension_coneAt_π (d : D) (g : StructuredArrow d F) :
    ((endRightExtension F E).coneAt d).π.app g = endLeg F E d g.right g.hom := by
  simp [map_endLeg]

/-- For each `d`, the cone `⟨T d, T d → E c⟩` over `d ↓ F` is a limit. -/
noncomputable def isPointwiseRightKanExtensionEnd :
    (endRightExtension F E).IsPointwiseRightKanExtension := fun d ↦
  { lift := fun s ↦ end_.lift (fun c ↦ Pi.lift fun φ ↦ s.π.app (StructuredArrow.mk φ))
      (fun i j g ↦ by
        ext ψ
        have := s.w (StructuredArrow.homMk' (StructuredArrow.mk ψ) g)
        simp at this ⊢
        exact this)
    fac := fun s g ↦ by
      rw [endRightExtension_coneAt_π]
      simp [endLeg]
      rfl
    uniq := fun s m hm ↦ by
      refine end_.hom_ext fun c ↦ ?_
      ext φ
      have := hm (StructuredArrow.mk φ)
      rw [endRightExtension_coneAt_π] at this
      simp [endLeg] at this ⊢
      exact this }

/-- `ALGD-C2-END-R06` (prose after 定理 9, p.10).
Dually, if the powers `Hom_D(d, F c') ⋔ E c` exist (as products of constant families, see
`isPower_iff_isLimit`) and the end `∫_c Hom_D(d, F c) ⋔ E c` exists for every `d`, then
`d ↦ ∫_c Hom_D(d, F c) ⋔ E c` (`endKan`) with the counit `T(F c) → Hom_D(F c, F c) ⋔ E c → E c`
at `id_{F c}` is a pointwise right Kan extension of `E` along `F`, so
`F‡E ≅ ∫_c Hom_D(−, F c) ⋔ E c` (`rightKanExtensionIsoEndKan`). -/
theorem endKan_isPointwiseRightKanExtension :
    Nonempty (endRightExtension F E).IsPointwiseRightKanExtension ∧
      F.HasPointwiseRightKanExtension E ∧ (endKan F E).IsRightKanExtension (endCounit F E) :=
  ⟨⟨isPointwiseRightKanExtensionEnd F E⟩,
    (isPointwiseRightKanExtensionEnd F E).hasPointwiseRightKanExtension,
    (isPointwiseRightKanExtensionEnd F E).isRightKanExtension⟩

/-- `F‡E ≅ ∫_c Hom_D(−, F c) ⋔ E c`. -/
noncomputable def rightKanExtensionIsoEndKan :
    have := (isPointwiseRightKanExtensionEnd F E).hasRightKanExtension
    F.rightKanExtension E ≅ endKan F E :=
  have := (isPointwiseRightKanExtensionEnd F E).hasRightKanExtension
  have : (endKan F E).IsRightKanExtension (endCounit F E) :=
    (isPointwiseRightKanExtensionEnd F E).isRightKanExtension
  rightKanExtensionUnique _ (F.rightKanExtensionCounit E) _ (endCounit F E)

end Right

end KanCoend

/-! ## Axiom audit

Each verified declaration depends only on `propext`, `Classical.choice` and `Quot.sound`, or on a
subset of them. The output is pinned with `#guard_msgs`, so `lake build` fails if it changes. -/

/-- info: 'ProjectEpisteme.AlgD.Ends.isWedge_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.isWedge_iff

/-- info: 'ProjectEpisteme.AlgD.Ends.isEnd_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.isEnd_iff

/-- info: 'ProjectEpisteme.AlgD.Ends.isWedge_hom_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.isWedge_hom_iff

/-- info: 'ProjectEpisteme.AlgD.Ends.isEnd_natTrans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.isEnd_natTrans

/-- info: 'ProjectEpisteme.AlgD.Ends.isCowedge_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.isCowedge_iff

/-- info: 'ProjectEpisteme.AlgD.Ends.isCoend_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.isCoend_iff

/-- info: 'ProjectEpisteme.AlgD.Ends.endFunctorOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.endFunctorOf_spec

/-- info: 'ProjectEpisteme.AlgD.Ends.hasEnd_of_hasLimits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.hasEnd_of_hasLimits

/-- info: 'ProjectEpisteme.AlgD.Ends.isLimitMapWedge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.isLimitMapWedge

/-- info: 'ProjectEpisteme.AlgD.Ends.isLimitCoyonedaWedge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.isLimitCoyonedaWedge

/-- info: 'ProjectEpisteme.AlgD.Ends.endIsoEqualizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.endIsoEqualizer

/-- info: 'ProjectEpisteme.AlgD.Ends.nonempty_isLimit_iff_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.nonempty_isLimit_iff_end

/-- info: 'ProjectEpisteme.AlgD.Ends.isCopower_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.isCopower_iff

/-- info: 'ProjectEpisteme.AlgD.Ends.isPower_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.isPower_iff

/-- info: 'ProjectEpisteme.AlgD.Ends.copower_power_adjunctions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.copower_power_adjunctions

/-- info: 'ProjectEpisteme.AlgD.Ends.isCopower_prod_isPower_fun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.isCopower_prod_isPower_fun

/-- info: 'ProjectEpisteme.AlgD.Ends.isLimitHomCoendWedge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.isLimitHomCoendWedge

/-- info: 'ProjectEpisteme.AlgD.Ends.fubini' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.fubini

/-- info: 'ProjectEpisteme.AlgD.Ends.end_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.end_comm

/-- info: 'ProjectEpisteme.AlgD.Ends.coend_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.coend_comm

/-- info: 'ProjectEpisteme.AlgD.Ends.isCopower_iff_isColimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.isCopower_iff_isColimit

/-- info: 'ProjectEpisteme.AlgD.Ends.isPower_iff_isLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.isPower_iff_isLimit

/-- info: 'ProjectEpisteme.AlgD.Ends.coendKan_isPointwiseLeftKanExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.coendKan_isPointwiseLeftKanExtension

/-- info: 'ProjectEpisteme.AlgD.Ends.leftKanExtensionIsoCoendKan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.leftKanExtensionIsoCoendKan

/-- info: 'ProjectEpisteme.AlgD.Ends.endKan_isPointwiseRightKanExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.endKan_isPointwiseRightKanExtension

/-- info: 'ProjectEpisteme.AlgD.Ends.rightKanExtensionIsoEndKan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProjectEpisteme.AlgD.Ends.rightKanExtensionIsoEndKan

end ProjectEpisteme.AlgD.Ends

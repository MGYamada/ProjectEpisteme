module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
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
* Copowers and powers (§3) are universal arrows to `Hom_C(a, −)` and `Hom_C(−, a)`, i.e.
  initial objects of the comma categories `x ↓ Hom_C(a, −)` and `x ↓ Hom_C(−, a)`.
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

end Copower

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

end ProjectEpisteme.AlgD.Ends

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Filtered.OfColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Sifted
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.Tactic.TFAE

/-!
# alg-d, Chapter 2: フィルター圏 (Filtered categories)

Source: alg-d, 「全ての概念はKan拡張である」, Chapter 2, `filtered.pdf`
(<https://alg-d.com/math/kan_extension/filtered.pdf>), printed date 2026-08-11,
SHA-256 `3bf65b1477ec69092f0319f0afe5b6239eea76daa390748f5c7395ed05108495`,
retrieved 2026-11-26. Ledger: `docs/ledger/algd/C2-FILTERED.md`.

## Conventions

* `IsFiltered` and `IsCofiltered` are mathlib's classes (the three conditions of 命題 1).
* "Finite category" is mathlib's `FinCategory`.
* `1 ↓ F` for `F : C → Set` is the category of elements `F.Elements`
  (`CategoryOfElements.structuredArrowEquivalence` identifies it with `StructuredArrow PUnit F`).
* `F † y` for `F : C → Set` and small `C` is `yoneda.leftKanExtension F : Ĉ → Set`; flat and
  sifted flat functors are defined by it, as in the source.
* `Span(a, b)` is `CostructuredArrow (diag C) (a, b)` and `Cospan(a, b)` is
  `StructuredArrow (a, b) (diag C)`.
* Sifted categories are defined as in the source (`colim : Set^C → Set` preserves finite
  products) and compared with mathlib's `IsSifted`.
-/

@[expose] public section

namespace ProjectEpisteme.AlgD.Filtered

open CategoryTheory Limits Functor Opposite

universe w v u u₂

variable {C : Type u} [Category.{v} C]

/-! ## Filtered categories -/

/-- `ALGD-C2-FILTERED-D01` (定義 (フィルター圏), p.1).
`C` is filtered iff every functor `F : J → C` from a finite category admits a natural
transformation `F ⇒ ∆c`, that is, a cocone. This is mathlib's `IsFiltered`, by
`IsFiltered.iff_cocone_nonempty`; the finite categories may be taken in any universe `w`. -/
theorem isFiltered_iff_cocone :
    IsFiltered C ↔ ∀ {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
      Nonempty (Cocone F) :=
  IsFiltered.iff_cocone_nonempty C

/-- `ALGD-C2-FILTERED-D02` (定義 (余フィルター圏), p.1).
`C` is cofiltered iff `C^op` is filtered. -/
theorem isCofiltered_iff_op : IsCofiltered C ↔ IsFiltered Cᵒᵖ :=
  (isFiltered_op_iff_isCofiltered C).symm

/-- `ALGD-C2-FILTERED-01` (命題 1, p.1–3).
`C` is filtered iff (1) `C` is nonempty, (2) any two objects map to a common object, and (3) any
two parallel morphisms are equalized by some morphism. (Footnote 1: some texts take this as the
definition; mathlib does.) -/
theorem isFiltered_iff :
    IsFiltered C ↔ Nonempty C ∧ (∀ a₀ a₁ : C, ∃ (c : C) (_ : a₀ ⟶ c) (_ : a₁ ⟶ c), True) ∧
      ∀ ⦃a₀ a₁ : C⦄ (f₀ f₁ : a₀ ⟶ a₁), ∃ (c : C) (g : a₁ ⟶ c), f₀ ≫ g = f₁ ≫ g := by
  constructor
  · intro _
    exact ⟨IsFiltered.nonempty, IsFilteredOrEmpty.cocone_objs, IsFilteredOrEmpty.cocone_maps⟩
  · rintro ⟨h₁, h₂, h₃⟩
    have : IsFilteredOrEmpty C := ⟨h₂, h₃⟩
    exact { nonempty := h₁ }

/-- `ALGD-C2-FILTERED-02` (例 2, p.3).
A finitely cocomplete category is filtered. -/
theorem isFiltered_of_hasFiniteColimits [HasFiniteColimits C] : IsFiltered C :=
  IsFiltered.of_hasFiniteColimits C

/-- `ALGD-C2-FILTERED-03` (例 3, p.3).
A category with a terminal object is filtered. -/
theorem isFiltered_of_hasTerminal [HasTerminal C] : IsFiltered C :=
  inferInstance

/-- `ALGD-C2-FILTERED-04` (例 4, p.3).
A preorder `X`, viewed as a category, is filtered iff it is nonempty and directed. -/
theorem preorder_isFiltered_iff (X : Type u) [Preorder X] :
    IsFiltered X ↔ Nonempty X ∧ IsDirected X (· ≤ ·) :=
  ⟨fun _ ↦ ⟨IsFiltered.nonempty, IsFiltered.isDirectedOrder X⟩,
    fun ⟨_, _⟩ ↦ inferInstance⟩

/-- `ALGD-C2-FILTERED-05` (命題 5, p.3–4).
For a filtered small category `I`, `colim : Set^I → Set` preserves finite limits; hence for a
finite `J` and `T : J × I → Set` the canonical map `colim_i lim_j T(j, i) → lim_j colim_i T(j, i)`
is an isomorphism. -/
theorem colim_preservesFiniteLimits {I : Type v} [SmallCategory I] [IsFiltered I] :
    PreservesFiniteLimits (colim : (I ⥤ Type v) ⥤ Type v) ∧
    ∀ {J : Type v} [SmallCategory J] [FinCategory J] (T : J × I ⥤ Type v),
      IsIso (colimitLimitToLimitColimit T) :=
  ⟨inferInstance, fun _ ↦ inferInstance⟩

/-- `ALGD-C2-FILTERED-06` (補題 6, p.4–6).
If `C` is finitely complete and `F : C → D` preserves finite limits, then `d ↓ F` is cofiltered
for every `d ∈ D`. -/
theorem structuredArrow_isCofiltered {D : Type u₂} [Category.{v} D] [HasFiniteLimits C]
    (F : C ⥤ D) [PreservesFiniteLimits F] (d : D) : IsCofiltered (StructuredArrow d F) :=
  (flat_of_preservesFiniteLimits F).cofiltered d

/-! ## Flat functors -/

section Flat

variable {C : Type v} [SmallCategory C]

/-- `ALGD-C2-FILTERED-D04` (定義 (平坦), p.6).
For a small category `C`, a functor `F : C → Set` is flat iff `y † F : Ĉ → Set` preserves finite
limits. -/
def IsFlat (F : C ⥤ Type v) : Prop :=
  PreservesFiniteLimits (yoneda.leftKanExtension F)

/-- A full and faithful functor into a cofiltered category, such that every object receives a
morphism from its image, has a cofiltered domain. -/
private theorem isCofiltered_of_fullyFaithful {A : Type*} [Category A] {B : Type*} [Category B]
    [IsCofiltered B] (ι : A ⥤ B) [ι.Full] [ι.Faithful] (h : ∀ b, ∃ a, Nonempty (ι.obj a ⟶ b)) :
    IsCofiltered A := by
  have : IsCofilteredOrEmpty A :=
    { cone_objs := fun a₁ a₂ ↦ by
        obtain ⟨a, ⟨k⟩⟩ := h (IsCofiltered.min (ι.obj a₁) (ι.obj a₂))
        exact ⟨a, ι.preimage (k ≫ IsCofiltered.minToLeft _ _),
          ι.preimage (k ≫ IsCofiltered.minToRight _ _), trivial⟩
      cone_maps := fun a₁ a₂ f g ↦ by
        obtain ⟨a, ⟨k⟩⟩ := h (IsCofiltered.eq (ι.map f) (ι.map g))
        refine ⟨a, ι.preimage (k ≫ IsCofiltered.eqHom _ _), ι.map_injective ?_⟩
        simp only [Functor.map_comp, Functor.map_preimage, Category.assoc]
        rw [IsCofiltered.eq_condition] }
  obtain ⟨b⟩ := IsCofiltered.nonempty (C := B)
  obtain ⟨a, -⟩ := h b
  exact { nonempty := ⟨a⟩ }

/-- The unit `F ⇒ (y † F) y` is an isomorphism, since `y` is fully faithful. -/
instance (F : C ⥤ Type v) : IsIso (yoneda.leftKanExtensionUnit F) :=
  (isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _
    (yoneda.leftKanExtensionUnit F)).isIso_hom

/-- The functor `1 ↓ F → 1 ↓ (y † F)`, `⟨c, x⟩ ↦ ⟨y c, η_c x⟩`. -/
noncomputable def elementsToLan (F : C ⥤ Type v) : F.Elements ⥤ (yoneda.leftKanExtension F).Elements where
  obj x := (yoneda.leftKanExtension F).elementsMk (yoneda.obj x.obj)
    ((yoneda.leftKanExtensionUnit F).app x.obj x.val)
  map {x y} f :=
    { hom := yoneda.map f.hom
      map_val := by
        have h := ConcreteCategory.congr_hom
          ((yoneda.leftKanExtensionUnit F).naturality f.hom) x.val
        change (yoneda.leftKanExtension F).map (yoneda.map f.hom)
          ((yoneda.leftKanExtensionUnit F).app x.obj x.val) =
          (yoneda.leftKanExtensionUnit F).app y.obj y.val
        rw [← f.map_val]
        exact h.symm }
  map_id x := Functor.Elements.hom_ext (yoneda.map_id x.obj)
  map_comp f g := Functor.Elements.hom_ext (yoneda.map_comp f.hom g.hom)

instance (F : C ⥤ Type v) : (elementsToLan F).Faithful where
  map_injective {_ _} _ _ h :=
    Functor.Elements.hom_ext (yoneda.map_injective (congrArg Functor.Elements.Hom.hom h))

instance (F : C ⥤ Type v) : (elementsToLan F).Full where
  map_surjective {x y} g := by
    refine ⟨{ hom := yoneda.preimage g.hom, map_val := ?_ }, ?_⟩
    · apply ((isIso_iff_bijective ((yoneda.leftKanExtensionUnit F).app y.obj)).1 inferInstance).1
      have h := ConcreteCategory.congr_hom
        ((yoneda.leftKanExtensionUnit F).naturality (yoneda.preimage g.hom)) x.val
      have hg : (yoneda.leftKanExtension F).map (yoneda.map (yoneda.preimage g.hom))
          ((yoneda.leftKanExtensionUnit F).app x.obj x.val) =
          (yoneda.leftKanExtensionUnit F).app y.obj y.val :=
        (congrArg (fun φ : yoneda.obj x.obj ⟶ yoneda.obj y.obj ↦
          (yoneda.leftKanExtension F).map φ ((yoneda.leftKanExtensionUnit F).app x.obj x.val))
          (yoneda.map_preimage g.hom)).trans g.map_val
      exact h.trans hg
    · exact Functor.Elements.hom_ext (yoneda.map_preimage g.hom)

/-- Every element of `y † F` receives a morphism from an element of `F`: `y † F(P)` is a colimit
of the sets `F c` over `y ↓ P`. -/
private theorem elementsToLan_surjective (F : C ⥤ Type v) (b : (yoneda.leftKanExtension F).Elements) :
    ∃ a, Nonempty ((elementsToLan F).obj a ⟶ b) := by
  have hpt := isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _
    (yoneda.leftKanExtensionUnit F) b.obj
  obtain ⟨g, s, hs⟩ := Types.jointly_surjective_of_isColimit hpt b.val
  exact ⟨F.elementsMk g.left s, ⟨{ hom := g.hom, map_val := hs }⟩⟩

/-- The canonical cocone exhibiting `F` as a colimit of representables `Hom_C(c, −)` over
`(1 ↓ F)^op`. -/
def elementsCocone (F : C ⥤ Type v) : Cocone ((Functor.Elements.π F).op ⋙ coyoneda) where
  pt := F
  ι :=
    { app x :=
        { app d := ↾ fun f ↦ F.map f x.unop.val
          naturality d d' g := by
            ext f
            change F.map (f ≫ g) x.unop.val = F.map g (F.map f x.unop.val)
            exact Functor.map_comp_apply F f g x.unop.val }
      naturality x x' φ := by
        ext d f
        change F.map (φ.unop.hom ≫ f) x'.unop.val = F.map f x.unop.val
        rw [Functor.map_comp_apply, φ.unop.map_val] }

private theorem map_id_apply' (F : C ⥤ Type v) (c : C) (x : F.obj c) : F.map (𝟙 c) x = x := by
  simp

/-- `F` is the colimit of the representables over `(1 ↓ F)^op`. -/
def elementsCoconeIsColimit (F : C ⥤ Type v) : IsColimit (elementsCocone F) where
  desc s :=
    { app d := ↾ fun y ↦ (s.ι.app (op (F.elementsMk d y))).app d (𝟙 d)
      naturality d d' g := by
        ext y
        have h1 := ConcreteCategory.congr_hom
          (congrArg (fun α ↦ NatTrans.app α d')
            (s.w (Quiver.Hom.op ({ hom := g, map_val := rfl } :
              F.elementsMk d y ⟶ F.elementsMk d' (F.map g y))))) (𝟙 d')
        have h2 := ConcreteCategory.congr_hom
          ((s.ι.app (op (F.elementsMk d y))).naturality g) (𝟙 d)
        change (s.ι.app (op (F.elementsMk d y))).app d' (g ≫ 𝟙 d') =
          (s.ι.app (op (F.elementsMk d' (F.map g y)))).app d' (𝟙 d') at h1
        change (s.ι.app (op (F.elementsMk d y))).app d' (𝟙 d ≫ g) =
          s.pt.map g ((s.ι.app (op (F.elementsMk d y))).app d (𝟙 d)) at h2
        change (s.ι.app (op (F.elementsMk d' (F.map g y)))).app d' (𝟙 d') =
          s.pt.map g ((s.ι.app (op (F.elementsMk d y))).app d (𝟙 d))
        rw [← h1, ← h2]
        simp }
  fac s x := by
    ext d f
    have h := ConcreteCategory.congr_hom
      (congrArg (fun α ↦ NatTrans.app α d)
        (s.w (Quiver.Hom.op ({ hom := f, map_val := rfl } :
          x.unop ⟶ F.elementsMk d (F.map f x.unop.val))))) (𝟙 d)
    change (s.ι.app x).app d (f ≫ 𝟙 d) =
      (s.ι.app (op (F.elementsMk d (F.map f x.unop.val)))).app d (𝟙 d) at h
    change (s.ι.app (op (F.elementsMk d (F.map f x.unop.val)))).app d (𝟙 d) = (s.ι.app x).app d f
    rw [← h, Category.comp_id]
  uniq s m hm := by
    ext d y
    have h := ConcreteCategory.congr_hom
      (congrArg (fun α ↦ NatTrans.app α d) (hm (op (F.elementsMk d y)))) (𝟙 d)
    change m.app d (F.map (𝟙 d) y) = (s.ι.app (op (F.elementsMk d y))).app d (𝟙 d) at h
    exact (congrArg (m.app d) (map_id_apply' F d y)).symm.trans h

/-- A colimit-preserving functor `K : Ĉ → U` is a left Kan extension of `K y` along `y` with the
identity unit (from the density of `y`). -/
theorem isLeftKanExtension_of_preservesColimit {U : Type u₂} [Category.{v} U]
    (K : (Cᵒᵖ ⥤ Type v) ⥤ U)
    [∀ P : Cᵒᵖ ⥤ Type v, PreservesColimit (CostructuredArrow.proj yoneda P ⋙ yoneda) K] :
    K.IsLeftKanExtension (𝟙 (yoneda ⋙ K)) := by
  obtain ⟨h⟩ := (isDense_iff_nonempty_isPointwiseLeftKanExtension (yoneda (C := C))).1
    inferInstance
  have h' := LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
    (LeftExtension.postcompose₂ObjMkIso K (Functor.rightUnitor (yoneda (C := C))).inv)
    (h.postcompose K)
  have h'' : (LeftExtension.mk K (𝟙 (yoneda ⋙ K))).IsPointwiseLeftKanExtension :=
    LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
      (StructuredArrow.isoMk (Functor.leftUnitor K) (by ext; simp)) h'
  exact h''.isLeftKanExtension

/-- If `F` is the colimit of the representables `Hom_C(S j, −)` over `J`, then
`y † F ≅ colim_j ev_{S j}`: the right side preserves colimits, so it is a left Kan extension of
`F` along `y`. -/
noncomputable def lanIsoOfColimit (F : C ⥤ Type v) {J : Type v} [SmallCategory J] (S : J ⥤ Cᵒᵖ)
    {c : Cocone (S ⋙ coyoneda)} (hc : IsColimit c) (e : c.pt ≅ F) :
    yoneda.leftKanExtension F ≅ (whiskeringLeft J Cᵒᵖ (Type v)).obj S ⋙ colim :=
  let K : (Cᵒᵖ ⥤ Type v) ⥤ Type v := (whiskeringLeft J Cᵒᵖ (Type v)).obj S ⋙ colim
  let e' : F ≅ yoneda ⋙ K :=
    e.symm ≪≫ hc.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫
      colimitIsoFlipCompColim (S ⋙ coyoneda)
  have hK : K.IsLeftKanExtension (𝟙 (yoneda ⋙ K)) := isLeftKanExtension_of_preservesColimit K
  have hK' : K.IsLeftKanExtension e'.hom :=
    (isLeftKanExtension_iff_of_iso₂ e'.hom (𝟙 (yoneda ⋙ K)) e' (Iso.refl K)
      (by ext; simp)).2 hK
  (leftKanExtensionUnique K e'.hom _ (yoneda.leftKanExtensionUnit F)).symm

/-- `ALGD-C2-FILTERED-07` (定理 7, p.6–9).
For a small category `C` and `F : C → Set` the following are equivalent: (1) `F` is flat; (2)
`1 ↓ F` is cofiltered; (3) `F` is a filtered colimit of representable functors
`Hom_C(S j, −)`. -/
theorem isFlat_tfae (F : C ⥤ Type v) :
    List.TFAE [IsFlat F, IsCofiltered F.Elements,
      ∃ (J : Type v) (_ : SmallCategory J) (_ : IsFiltered J) (S : J ⥤ Cᵒᵖ)
        (c : Cocone (S ⋙ coyoneda)), Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ F)] := by
  tfae_have 1 → 2 := by
    intro h
    have : PreservesFiniteLimits (yoneda.leftKanExtension F) := h
    have := (yoneda.leftKanExtension F).isCofiltered_elements
    exact isCofiltered_of_fullyFaithful (elementsToLan F) (elementsToLan_surjective F)
  tfae_have 2 → 3 := fun _ ↦ ⟨(F.Elements)ᵒᵖ, inferInstance, inferInstance,
    (Functor.Elements.π F).op, elementsCocone F, ⟨elementsCoconeIsColimit F⟩, ⟨Iso.refl _⟩⟩
  tfae_have 3 → 1 := by
    rintro ⟨J, _, _, S, c, ⟨hc⟩, ⟨e⟩⟩
    have : PreservesFiniteLimits ((whiskeringLeft J Cᵒᵖ (Type v)).obj S ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    exact preservesFiniteLimits_of_natIso (lanIsoOfColimit F S hc e).symm
  tfae_finish

/-- `ALGD-C2-FILTERED-08` (系 8, p.9–10).
For a small category `C`, `colim : Set^C → Set` preserves finite limits iff `C` is filtered.
(⇐) is 命題 5; (⇒) is mathlib's `isFiltered_of_nonempty_limit_colimit_to_colimit_limit`, a direct
argument, whereas the source goes through 定理 7 with `F := colim ∘ y`. -/
theorem colim_preservesFiniteLimits_iff :
    PreservesFiniteLimits (colim : (C ⥤ Type v) ⥤ Type v) ↔ IsFiltered C := by
  refine ⟨fun _ ↦ isFiltered_of_nonempty_limit_colimit_to_colimit_limit fun {J} _ _ G ↦ ?_,
    fun _ ↦ inferInstance⟩
  exact ⟨(lim.mapIso (colimitIsoFlipCompColim G.flip)).hom ≫ (preservesLimitIso colim G).inv⟩

/-- `ALGD-C2-FILTERED-09` (系 9, p.10).
A flat functor `F : C → Set` preserves finite limits. Conversely, if `C` is finitely complete,
every functor that preserves finite limits is flat. -/
theorem isFlat_preservesFiniteLimits (F : C ⥤ Type v) :
    (IsFlat F → PreservesFiniteLimits F) ∧
    (∀ [HasFiniteLimits C], PreservesFiniteLimits F → IsFlat F) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : PreservesFiniteLimits (yoneda.leftKanExtension F) := h
    have : PreservesFiniteLimits (yoneda ⋙ yoneda.leftKanExtension F) :=
      comp_preservesFiniteLimits _ _
    exact preservesFiniteLimits_of_natIso (asIso (yoneda.leftKanExtensionUnit F)).symm
  · have := F.isCofiltered_elements
    exact ((isFlat_tfae F).out 2 1).1 this

/-- `ALGD-C2-FILTERED-10` (例 10, p.10).
For `a ∈ C`, `Hom_C(a, −) : C → Set` is flat: `1 ↓ Hom_C(a, −)` has the initial object
`⟨a, id_a⟩`. -/
theorem coyoneda_isFlat (a : C) : IsFlat (coyoneda.obj (op a)) := by
  have hi : IsInitial ((coyoneda.obj (op a)).elementsMk a (𝟙 a)) :=
    IsInitial.ofUniqueHom (fun y ↦ { hom := y.val, map_val := by simp })
      fun y m ↦ Functor.Elements.hom_ext (by
        have := m.map_val
        simpa using this)
  have : IsCofiltered (coyoneda.obj (op a)).Elements := IsCofiltered.of_isInitial _ hi
  exact ((isFlat_tfae (coyoneda.obj (op a))).out 2 1).1 this

/-- `ALGD-C2-FILTERED-11` (定理 11, p.10–11).
For small categories `C`, `D` with `C` finitely complete, `F : C → D` preserves finite limits iff
`F† : Ĉ → D̂` preserves finite limits. mathlib's version does not need `C` finitely complete. -/
theorem preservesFiniteLimits_iff_lan {D : Type v} [SmallCategory D] [HasFiniteLimits C]
    (F : C ⥤ D) :
    PreservesFiniteLimits F ↔
      PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ Type v) ⥤ (Dᵒᵖ ⥤ Type v)) :=
  preservesFiniteLimits_iff_lan_preservesFiniteLimits F

end Flat

/-! ## Sifted categories -/

section Sifted

variable {C : Type v} [SmallCategory C]

/-- `C` is sifted in the sense of the source: `colim : Set^C → Set` preserves finite products
(the definition `ALGD-C2-FILTERED-D05`). -/
def IsSiftedSet (C : Type v) [SmallCategory C] : Prop :=
  PreservesFiniteProducts (colim : (C ⥤ Type v) ⥤ Type v)

/-- `C` is cosifted iff `C^op` is sifted. -/
def IsCosiftedSet (C : Type v) [SmallCategory C] : Prop :=
  IsSiftedSet Cᵒᵖ

/-- `ALGD-C2-FILTERED-D05` (定義 (sifted), p.11).
A small category `C` is sifted iff `colim : Set^C → Set` preserves finite products, and cosifted
iff `C^op` is sifted. This is equivalent to mathlib's `IsSifted` (the diagonal is final and `C`
is nonempty). -/
theorem isSiftedSet_iff : IsSiftedSet C ↔ IsSifted C :=
  ⟨fun h ↦ @IsSifted.of_colim_preservesFiniteProducts _ _ h,
    fun _ ↦ (inferInstance : PreservesFiniteProducts (colim : (C ⥤ Type v) ⥤ Type v))⟩

/-- `ALGD-C2-FILTERED-R01` (prose after 定義 (sifted flat), p.12).
By 系 8, every filtered category is sifted; in particular every finitely cocomplete category is
sifted. -/
theorem isSiftedSet_of_isFiltered :
    (IsFiltered C → IsSiftedSet C) ∧ (HasFiniteColimits C → IsSiftedSet C) := by
  have h : IsFiltered C → IsSiftedSet C := fun _ ↦
    (inferInstance : PreservesFiniteProducts (colim : (C ⥤ Type v) ⥤ Type v))
  exact ⟨h, fun _ ↦ h (IsFiltered.of_hasFiniteColimits C)⟩

/-- `ALGD-C2-FILTERED-D07` (定義 (sifted flat), p.12).
For a small category `C`, `F : C → Set` is sifted flat iff `y † F : Ĉ → Set` preserves finite
products. -/
def IsSiftedFlat (F : C ⥤ Type v) : Prop :=
  PreservesFiniteProducts (yoneda.leftKanExtension F)

end Sifted

section Spans

/-- `ALGD-C2-FILTERED-D09` (定義 (Span(a, b), Cospan(a, b)), p.12).
The category `Span(a, b)` of spans `a ← c → b` (a morphism `⟨f, g⟩ → ⟨f', g'⟩` is `h : c → c'`
with `f' h = f`, `g' h = g`) is the comma category `∆ ↓ ⟨a, b⟩` for the diagonal
`∆ : C → C × C`; dually `Cospan(a, b) = ⟨a, b⟩ ↓ ∆` (`Cospan`). -/
abbrev Span (a b : C) : Type _ := CostructuredArrow (Functor.diag C) (a, b)

/-- The category `Cospan(a, b)` of cospans `a → c ← b` (part of `ALGD-C2-FILTERED-D09`). -/
abbrev Cospan (a b : C) : Type _ := StructuredArrow (a, b) (Functor.diag C)

end Spans

section Sifted2

variable {C : Type v} [SmallCategory C]

/-- `ALGD-C2-FILTERED-14` (命題 14, p.14–15).
For a small category `C` the following are equivalent: (1) `C` is sifted; (2) `C` is nonempty and
`Cospan(a, b)` is connected for all `a, b ∈ C`; (3) `C` is nonempty and the diagonal
`∆ : C → C × C` is final. The source omits "nonempty" in (2) and (3); without it the empty
category satisfies (2) and (3) but not (1), since `colim` of the empty diagram is `∅`, not `1`.
The source omits the proof of (2) ⇒ (1); here (1) ⇔ (3) is mathlib's description of `IsSifted`
(`IsSifted.of_colim_preservesFiniteProducts`) and (2) ⇔ (3) is the definition of a final
functor. -/
theorem isSifted_tfae :
    List.TFAE [IsSiftedSet C, Nonempty C ∧ ∀ a b : C, IsConnected (Cospan a b),
      Nonempty C ∧ (Functor.diag C).Final] := by
  tfae_have 1 ↔ 3 := by
    rw [isSiftedSet_iff]
    exact ⟨fun h ↦ ⟨h.nonempty, h.toFinal⟩, fun ⟨h₁, h₂⟩ ↦ @IsSifted.mk C _ h₂ h₁⟩
  tfae_have 2 ↔ 3 :=
    and_congr_right fun _ ↦ ⟨fun h ↦ ⟨fun x ↦ h x.1 x.2⟩, fun h a b ↦ h.out (a, b)⟩
  tfae_finish

/-- `ALGD-C2-FILTERED-R02` (prose after 命題 14, p.15).
A category with finite coproducts is sifted. -/
theorem isSiftedSet_of_hasFiniteCoproducts [HasFiniteCoproducts C] : IsSiftedSet C := by
  have : Nonempty C := ⟨⊥_ C⟩
  exact isSiftedSet_iff.2 inferInstance

/-- `ALGD-C2-FILTERED-R03` (prose after 命題 14, p.15).
Dually, a small category `C` is cosifted iff `C` is nonempty and `Span(a, b)` is connected for all
`a, b ∈ C` (with the same nonemptiness correction as 命題 14). -/
theorem isCosifted_iff : IsCosiftedSet C ↔ Nonempty C ∧ ∀ a b : C, IsConnected (Span a b) := by
  have key : ∀ a b : C, IsConnected (Cospan (op a) (op b)) ↔ IsConnected (Span a b) := by
    intro a b
    let e₁ := costructuredArrowOpEquivalence (Functor.diag C) (a, b)
    let e₂ : StructuredArrow (op (a, b)) (Functor.diag C).op ≌ Cospan (op a) (op b) :=
      (StructuredArrow.post (op (a, b)) (Functor.diag C).op (prodOpEquiv C).functor).asEquivalence
    constructor
    · intro _
      have : IsConnected (Span a b)ᵒᵖ := isConnected_of_equivalent (e₁.trans e₂).symm
      exact isConnected_of_isConnected_op
    · intro _
      exact isConnected_of_equivalent (e₁.trans e₂)
  have h14 : IsSiftedSet Cᵒᵖ ↔ Nonempty Cᵒᵖ ∧ ∀ a b : Cᵒᵖ, IsConnected (Cospan a b) :=
    (isSifted_tfae (C := Cᵒᵖ)).out 1 2
  unfold IsCosiftedSet
  rw [h14]
  constructor
  · rintro ⟨⟨c⟩, h⟩
    exact ⟨⟨c.unop⟩, fun a b ↦ (key a b).1 (h (op a) (op b))⟩
  · rintro ⟨⟨c⟩, h⟩
    exact ⟨⟨op c⟩, fun a b ↦ (key a.unop b.unop).2 (h a.unop b.unop)⟩

end Sifted2

/-! ## Sifted flat functors (補題 13, 定理 15) -/

section SiftedFlat

variable {C : Type v} [SmallCategory C] (F : C ⥤ Type v)

/-- Two representatives of the same element of `y † F (P) = colim(y ↓ P → C → Set)` are related
by the equivalence relation generated by the morphisms of `y ↓ P`. -/
private theorem coconeAt_eqvGen {P : Cᵒᵖ ⥤ Type v} {j j' : CostructuredArrow yoneda P}
    {x : F.obj j.left} {x' : F.obj j'.left}
    (h : ((LeftExtension.mk _ (yoneda.leftKanExtensionUnit F)).coconeAt P).ι.app j x =
      ((LeftExtension.mk _ (yoneda.leftKanExtensionUnit F)).coconeAt P).ι.app j' x') :
    Relation.EqvGen (CostructuredArrow.proj yoneda P ⋙ F).ColimitTypeRel ⟨j, x⟩ ⟨j', x'⟩ := by
  have hpt := isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _
    (yoneda.leftKanExtensionUnit F) P
  apply Types.colimit_eq
  have e1 := ConcreteCategory.congr_hom
    (hpt.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) j) x
  have e2 := ConcreteCategory.congr_hom
    (hpt.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) j') x'
  change (hpt.coconePointUniqueUpToIso (colimit.isColimit _)).hom
    (((LeftExtension.mk _ (yoneda.leftKanExtensionUnit F)).coconeAt P).ι.app j x) =
    colimit.ι (CostructuredArrow.proj yoneda P ⋙ F) j x at e1
  change (hpt.coconePointUniqueUpToIso (colimit.isColimit _)).hom
    (((LeftExtension.mk _ (yoneda.leftKanExtensionUnit F)).coconeAt P).ι.app j' x') =
    colimit.ι (CostructuredArrow.proj yoneda P ⋙ F) j' x' at e2
  rw [← e1, ← e2, h]

/-- The object of `ι ↓ b` given by a representative `(j, z)` of the element `b` of `y † F`. -/
private noncomputable def fiberObj {b : (yoneda.leftKanExtension F).Elements}
    (j : CostructuredArrow yoneda b.obj) (z : F.obj j.left)
    (h : ((LeftExtension.mk _ (yoneda.leftKanExtensionUnit F)).coconeAt b.obj).ι.app j z =
      b.val) :
    CostructuredArrow (elementsToLan F) b :=
  CostructuredArrow.mk (Y := F.elementsMk j.left z) { hom := j.hom, map_val := h }

/-- The comma categories `ι ↓ b` are connected (`ι` is initial). -/
private theorem fiber_zigzag (b : (yoneda.leftKanExtension F).Elements) :
    ∀ X Y : CostructuredArrow (elementsToLan F) b, Zigzag X Y := by
  let c := (LeftExtension.mk _ (yoneda.leftKanExtensionUnit F)).coconeAt b.obj
  have val : ∀ σ τ : Σ j, (CostructuredArrow.proj yoneda b.obj ⋙ F).obj j,
      Relation.EqvGen (CostructuredArrow.proj yoneda b.obj ⋙ F).ColimitTypeRel σ τ →
      c.ι.app σ.1 σ.2 = c.ι.app τ.1 τ.2 := by
    intro σ τ h
    induction h with
    | rel x y hxy =>
      obtain ⟨f, hf⟩ := hxy
      rw [hf]
      exact (ConcreteCategory.congr_hom (c.w f) x.2).symm
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have key : ∀ σ τ : Σ j, (CostructuredArrow.proj yoneda b.obj ⋙ F).obj j,
      Relation.EqvGen (CostructuredArrow.proj yoneda b.obj ⋙ F).ColimitTypeRel σ τ →
      ∀ (hσ : c.ι.app σ.1 σ.2 = b.val) (hτ : c.ι.app τ.1 τ.2 = b.val),
        Zigzag (fiberObj F σ.1 σ.2 hσ) (fiberObj F τ.1 τ.2 hτ) := by
    intro σ τ h
    induction h with
    | rel x y hxy =>
      intro hx hy
      obtain ⟨f, hf⟩ := hxy
      refine Zigzag.of_hom (CostructuredArrow.homMk { hom := f.left, map_val := hf.symm } ?_)
      exact Functor.Elements.hom_ext (CostructuredArrow.w f)
    | refl => intro _ _; rfl
    | symm _ _ _ ih => intro hx hy; exact (ih hy hx).symm
    | trans x y z hxy _ ih₁ ih₂ =>
      intro hx hz
      have hy : c.ι.app y.1 y.2 = b.val := (val x y hxy).symm.trans hx
      exact (ih₁ hx hy).trans (ih₂ hy hz)
  intro X Y
  exact key ⟨CostructuredArrow.mk X.hom.hom, X.left.val⟩ ⟨CostructuredArrow.mk Y.hom.hom, Y.left.val⟩
    (coconeAt_eqvGen F (X.hom.map_val.trans Y.hom.map_val.symm)) X.hom.map_val Y.hom.map_val

/-- `ALGD-C2-FILTERED-13` (補題 13, p.12–14).
If `F : C → Set` is sifted flat, then for all `s, t ∈ 1 ↓ F` the category `Span(s, t)` of spans in
`1 ↓ F` is connected. -/
theorem span_isConnected_of_isSiftedFlat (h : IsSiftedFlat F) (s t : F.Elements) :
    IsConnected (Span s t) := by
  have : PreservesFiniteProducts (yoneda.leftKanExtension F) := h
  let L := yoneda.leftKanExtension F
  let η := yoneda.leftKanExtensionUnit F
  let ι := elementsToLan F
  let P : Cᵒᵖ ⥤ Type v := yoneda.obj s.obj ⨯ yoneda.obj t.obj
  let φ : L.obj P ≅ L.obj (yoneda.obj s.obj) × L.obj (yoneda.obj t.obj) :=
    PreservesLimitPair.iso L _ _ ≪≫ Types.binaryProductIso _ _
  have hφ₁ : ∀ w, (φ.hom w).1 = L.map prod.fst w := fun w ↦ by
    simp only [φ, PreservesLimitPair.iso_hom, Iso.trans_hom]
    exact ConcreteCategory.congr_hom (prodComparison_fst L _ _) w
  have hφ₂ : ∀ w, (φ.hom w).2 = L.map prod.snd w := fun w ↦ by
    simp only [φ, PreservesLimitPair.iso_hom, Iso.trans_hom]
    exact ConcreteCategory.congr_hom (prodComparison_snd L _ _) w
  let w₀ : L.obj P := φ.inv (η.app s.obj s.val, η.app t.obj t.val)
  have hw₀ : φ.hom w₀ = (η.app s.obj s.val, η.app t.obj t.val) := by simp [w₀]
  let W : L.Elements := L.elementsMk P w₀
  let p₀ : W ⟶ ι.obj s :=
    { hom := prod.fst, map_val := (hφ₁ w₀).symm.trans (congrArg Prod.fst hw₀) }
  let p₁ : W ⟶ ι.obj t :=
    { hom := prod.snd, map_val := (hφ₂ w₀).symm.trans (congrArg Prod.snd hw₀) }
  -- every span maps to `W`
  let m : ∀ σ : Span s t, ι.obj σ.left ⟶ W := fun σ ↦
    { hom := prod.lift (yoneda.map σ.hom.1.hom) (yoneda.map σ.hom.2.hom)
      map_val := by
        apply φ.toEquiv.injective
        change φ.hom (L.map (prod.lift (yoneda.map σ.hom.1.hom) (yoneda.map σ.hom.2.hom))
          (η.app σ.left.obj σ.left.val)) = φ.hom w₀
        rw [hw₀]
        refine Prod.ext ?_ ?_
        · rw [hφ₁, ← Functor.map_comp_apply, prod.lift_fst]
          exact (ι.map σ.hom.1).map_val
        · rw [hφ₂, ← Functor.map_comp_apply, prod.lift_snd]
          exact (ι.map σ.hom.2).map_val }
  -- spans from objects over `W`
  let Ψ : CostructuredArrow ι W ⥤ Span s t :=
    { obj Y := CostructuredArrow.mk (Y := Y.left)
        ((ι.preimage (Y.hom ≫ p₀), ι.preimage (Y.hom ≫ p₁)) :
          (Functor.diag F.Elements).obj Y.left ⟶ (s, t))
      map {Y Y'} g := CostructuredArrow.homMk g.left (by
        refine Prod.ext (ι.map_injective ?_) (ι.map_injective ?_)
        · change ι.map (g.left ≫ ι.preimage (Y'.hom ≫ p₀)) = ι.map (ι.preimage (Y.hom ≫ p₀))
          rw [ι.map_comp, ι.map_preimage, ι.map_preimage, ← Category.assoc, CostructuredArrow.w g]
        · change ι.map (g.left ≫ ι.preimage (Y'.hom ≫ p₁)) = ι.map (ι.preimage (Y.hom ≫ p₁))
          rw [ι.map_comp, ι.map_preimage, ι.map_preimage, ← Category.assoc, CostructuredArrow.w g])
      map_id _ := CostructuredArrow.hom_ext _ _ rfl
      map_comp _ _ := CostructuredArrow.hom_ext _ _ rfl }
  have hΨ : ∀ σ : Span s t, Zigzag σ (Ψ.obj (CostructuredArrow.mk (m σ))) := fun σ ↦ by
    refine Zigzag.of_hom (CostructuredArrow.homMk (𝟙 σ.left) ?_)
    refine Prod.ext (ι.map_injective ?_) (ι.map_injective ?_)
    · change ι.map (𝟙 σ.left ≫ ι.preimage (m σ ≫ p₀)) = ι.map σ.hom.1
      rw [Category.id_comp, ι.map_preimage]
      exact Functor.Elements.hom_ext (prod.lift_fst _ _)
    · change ι.map (𝟙 σ.left ≫ ι.preimage (m σ ≫ p₁)) = ι.map σ.hom.2
      rw [Category.id_comp, ι.map_preimage]
      exact Functor.Elements.hom_ext (prod.lift_snd _ _)
  obtain ⟨a, ⟨k⟩⟩ := elementsToLan_surjective F W
  have : Nonempty (Span s t) := ⟨Ψ.obj (CostructuredArrow.mk k)⟩
  refine zigzag_isConnected fun σ τ ↦ ?_
  exact (hΨ σ).trans ((zigzag_obj_of_zigzag Ψ (fiber_zigzag F W _ _)).trans (hΨ τ).symm)

/-- `ALGD-C2-FILTERED-15` (定理 15, p.15–16).
For a small category `C` and `F : C → Set` the following are equivalent: (1) `F` is sifted flat;
(2) `1 ↓ F` is cosifted; (3) `F` is a sifted colimit of representables: `F ≅ colim_j Hom_C(S j, −)`
for a sifted `J` and `S : J → C^op`. -/
theorem isSiftedFlat_tfae :
    List.TFAE [IsSiftedFlat F, IsCosiftedSet F.Elements,
      ∃ (J : Type v) (_ : SmallCategory J) (_ : IsSiftedSet J) (S : J ⥤ Cᵒᵖ)
        (c : Cocone (S ⋙ coyoneda)), Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ F)] := by
  tfae_have 1 → 2 := by
    intro h
    have : PreservesFiniteProducts (yoneda.leftKanExtension F) := h
    have ht : IsTerminal ((yoneda.leftKanExtension F).obj (⊤_ (Cᵒᵖ ⥤ Type v))) :=
      IsTerminal.isTerminalObj _ _ terminalIsTerminal
    obtain ⟨a, -⟩ := elementsToLan_surjective F
      ((yoneda.leftKanExtension F).elementsMk _ (ht.from PUnit PUnit.unit))
    exact isCosifted_iff.2 ⟨⟨a⟩, span_isConnected_of_isSiftedFlat F h⟩
  tfae_have 2 → 3 := fun h ↦ ⟨(F.Elements)ᵒᵖ, inferInstance, h,
    (Functor.Elements.π F).op, elementsCocone F, ⟨elementsCoconeIsColimit F⟩, ⟨Iso.refl _⟩⟩
  tfae_have 3 → 1 := by
    rintro ⟨J, _, hJ, S, c, ⟨hc⟩, ⟨e⟩⟩
    have : PreservesFiniteProducts (colim : (J ⥤ Type v) ⥤ Type v) := hJ
    have : PreservesFiniteProducts ((whiskeringLeft J Cᵒᵖ (Type v)).obj S ⋙ colim) :=
      inferInstance
    exact ⟨fun _ ↦ preservesLimitsOfShape_of_natIso (lanIsoOfColimit F S hc e).symm⟩
  tfae_finish

end SiftedFlat

/-! ## Axiom audit

Each verified declaration depends only on `propext`, `Classical.choice` and `Quot.sound`, or on a
subset of them. The output is pinned with `#guard_msgs`, so `lake build` fails if it changes. -/

/-- info: 'ProjectEpisteme.AlgD.Filtered.isFiltered_iff_cocone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.isFiltered_iff_cocone

/-- info: 'ProjectEpisteme.AlgD.Filtered.isCofiltered_iff_op' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.isCofiltered_iff_op

/-- info: 'ProjectEpisteme.AlgD.Filtered.isFiltered_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.isFiltered_iff

/-- info: 'ProjectEpisteme.AlgD.Filtered.isFiltered_of_hasFiniteColimits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.isFiltered_of_hasFiniteColimits

/-- info: 'ProjectEpisteme.AlgD.Filtered.isFiltered_of_hasTerminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.isFiltered_of_hasTerminal

/-- info: 'ProjectEpisteme.AlgD.Filtered.preorder_isFiltered_iff' depends on axioms: [Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.preorder_isFiltered_iff

/-- info: 'ProjectEpisteme.AlgD.Filtered.colim_preservesFiniteLimits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.colim_preservesFiniteLimits

/-- info: 'ProjectEpisteme.AlgD.Filtered.structuredArrow_isCofiltered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.structuredArrow_isCofiltered

/-- info: 'ProjectEpisteme.AlgD.Filtered.IsFlat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.IsFlat

/-- info: 'ProjectEpisteme.AlgD.Filtered.isFlat_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.isFlat_tfae

/-- info: 'ProjectEpisteme.AlgD.Filtered.colim_preservesFiniteLimits_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.colim_preservesFiniteLimits_iff

/-- info: 'ProjectEpisteme.AlgD.Filtered.isFlat_preservesFiniteLimits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.isFlat_preservesFiniteLimits

/-- info: 'ProjectEpisteme.AlgD.Filtered.coyoneda_isFlat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.coyoneda_isFlat

/-- info: 'ProjectEpisteme.AlgD.Filtered.preservesFiniteLimits_iff_lan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.preservesFiniteLimits_iff_lan

/-- info: 'ProjectEpisteme.AlgD.Filtered.isSiftedSet_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.isSiftedSet_iff

/-- info: 'ProjectEpisteme.AlgD.Filtered.isSiftedSet_of_isFiltered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.isSiftedSet_of_isFiltered

/-- info: 'ProjectEpisteme.AlgD.Filtered.IsSiftedFlat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.IsSiftedFlat

/-- info: 'ProjectEpisteme.AlgD.Filtered.Span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.Span

/-- info: 'ProjectEpisteme.AlgD.Filtered.isSifted_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.isSifted_tfae

/-- info: 'ProjectEpisteme.AlgD.Filtered.isSiftedSet_of_hasFiniteCoproducts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.isSiftedSet_of_hasFiniteCoproducts

/-- info: 'ProjectEpisteme.AlgD.Filtered.isCosifted_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.isCosifted_iff

/-- info: 'ProjectEpisteme.AlgD.Filtered.span_isConnected_of_isSiftedFlat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.span_isConnected_of_isSiftedFlat

/-- info: 'ProjectEpisteme.AlgD.Filtered.isSiftedFlat_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ProjectEpisteme.AlgD.Filtered.isSiftedFlat_tfae

end ProjectEpisteme.AlgD.Filtered

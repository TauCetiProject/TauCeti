/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic

import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.Order.Zorn

/-!
# Baer's criterion for modules over a preadditive category

A module is injective if maps into it from subobjects of representables extend over their
representables. The proof orders partial extensions by inclusion of their graphs. A chain of
graphs has a pointwise union, whose projection to the source module is still monic. A maximal
graph can be enlarged by adjoining any map out of a representable, using a pullback and a
pushout.

This is the many-object analogue of Wisbauer, *Foundations of Module and Ring Theory*,
§16.2 (2) and §16.4. The pullback-pushout step uses the abelian category argument in Mathlib's
`IsGrothendieckAbelian.generatingMonomorphisms.exists_pushouts`.
-/

public section

open CategoryTheory Category Limits Opposite

namespace TauCeti.ModCat

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The extension condition of Baer's criterion: every map from a subobject of a representable
into `E` extends to the representable. -/
def Baer (E : ModCat.{v} C) : Prop :=
  ∀ (X : C) (S : Subobject ((yoneda C).obj X)) (f : (S : ModCat.{v} C) ⟶ E),
    ∃ g : (yoneda C).obj X ⟶ E, S.arrow ≫ g = f

/-- A module satisfies Baer's condition exactly when maps from subobjects of representables
extend across the subobject inclusions. -/
theorem baer_iff_forall_subobject (E : ModCat.{v} C) :
    E.Baer ↔ ∀ (X : C) (S : Subobject ((yoneda C).obj X)) (f : (S : ModCat.{v} C) ⟶ E),
      ∃ g : (yoneda C).obj X ⟶ E, S.arrow ≫ g = f := (Iff.rfl)

/-- Baer's extension condition applied to any monomorphism into a representable. -/
theorem Baer.extend {E : ModCat.{v} C} (hE : E.Baer) {X : C} {I : ModCat.{v} C}
    (i : I ⟶ (yoneda C).obj X) [Mono i] (f : I ⟶ E) :
    ∃ g : (yoneda C).obj X ⟶ E, i ≫ g = f := by
  obtain ⟨g, hg⟩ := hE X (Subobject.mk i) ((Subobject.underlyingIso i).hom ≫ f)
  exact ⟨g, by simpa using (Subobject.underlyingIso i).inv ≫= hg⟩

section

variable {M E : ModCat.{v} C}

private noncomputable def graphRange (S : Subobject (M ⊞ E)) (X : Cᵒᵖ) :
    AddSubgroup ((M ⊞ E).obj.obj X) :=
  (S.arrow.hom.app X).hom.range

private theorem graphRange_mono (X : Cᵒᵖ) :
    Monotone (fun S : Subobject (M ⊞ E) ↦ graphRange S X) := by
  intro S T h x hx
  obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.1 hx
  exact ⟨(Subobject.ofLE S T h).hom.app X y,
    ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app X) (Subobject.ofLE_arrow h)) y⟩

private noncomputable abbrev graphUnionGroup (S : Set (Subobject (M ⊞ E))) (X : Cᵒᵖ) :
    AddSubgroup ((M ⊞ E).obj.obj X) :=
  ⨆ s : S, graphRange s.val X

private theorem graphUnionGroup_map_mem (S : Set (Subobject (M ⊞ E))) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) {x : (M ⊞ E).obj.obj X} (hx : x ∈ graphUnionGroup S X) :
    (M ⊞ E).obj.map f x ∈ graphUnionGroup S Y := by
  suffices h : graphUnionGroup S X ≤ (graphUnionGroup S Y).comap ((M ⊞ E).obj.map f).hom from h hx
  refine iSup_le (fun s ↦ ?_)
  intro x hx
  obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.1 hx
  exact (le_iSup (fun s : S ↦ graphRange s.val Y) s) ⟨(s.val : ModCat.{v} C).obj.map f y,
    NatTrans.naturality_apply s.val.arrow.hom f y⟩

private noncomputable def graphUnionFunctor (S : Set (Subobject (M ⊞ E))) :
    Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj X := AddCommGrpCat.of (graphUnionGroup S X)
  map f := AddCommGrpCat.ofHom (((M ⊞ E).obj.map f).hom.comp
    (graphUnionGroup S _).subtype |>.codRestrict _ fun x ↦ graphUnionGroup_map_mem S f x.property)
  map_id X := by
    apply AddCommGrpCat.ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((M ⊞ E).obj.map_id X) x
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((M ⊞ E).obj.map_comp f g) x

private noncomputable def graphUnion (S : Set (Subobject (M ⊞ E))) : ModCat.{v} C :=
  ⟨graphUnionFunctor S, (additiveFunctor_iff _).2 ⟨by
    intro X Y f g
    apply AddCommGrpCat.ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((M ⊞ E).obj.map_add (f := f) (g := g))
      (x : graphUnionGroup S X).val⟩⟩

private noncomputable def graphUnionι (S : Set (Subobject (M ⊞ E))) :
    graphUnion S ⟶ M ⊞ E :=
  ObjectProperty.homMk
    { app X := AddCommGrpCat.ofHom (graphUnionGroup S X).subtype
      naturality X Y f := by
        ext x
        rfl }

private theorem graphUnion_upperBound (S : Set (Subobject (M ⊞ E))) {s : Subobject (M ⊞ E)}
    (hs : s ∈ S) :
    ∃ k : (s : ModCat.{v} C) ⟶ graphUnion S, k ≫ graphUnionι S = s.arrow := by
  refine ⟨ObjectProperty.homMk
    { app X := AddCommGrpCat.ofHom ((s.arrow.hom.app X).hom.codRestrict _
        (fun x ↦ (le_iSup (fun t : S ↦ graphRange t.val X) ⟨s, hs⟩) ⟨x, rfl⟩))
      naturality X Y f := by
        ext x
        exact Subtype.ext (NatTrans.naturality_apply s.arrow.hom f x) }, ?_⟩
  apply ObjectProperty.hom_ext
  ext X x
  rfl

private theorem mono_graphUnion_comp_fst (S : Set (Subobject (M ⊞ E))) [Nonempty S]
    (hS : DirectedOn (· ≤ ·) S) (h : ∀ s ∈ S, Mono (s.arrow ≫ biprod.fst)) :
    Mono (graphUnionι S ≫ biprod.fst) := by
  let P := additiveFunctor Cᵒᵖ AddCommGrpCat.{v}
  have := P.preservesMonomorphisms_ι_of_isNormalEpiCategory
  apply P.ι.mono_of_mono_map
  apply (NatTrans.mono_iff_mono_app _).2
  intro X
  apply (AddCommGrpCat.mono_iff_injective _).2
  apply (injective_iff_map_eq_zero _).2
  intro x hx
  have hd : Directed (· ≤ ·) (fun s : S ↦ graphRange s.val X) :=
    hS.directed_val.mono_comp _ (graphRange_mono X)
  obtain ⟨s, y, hy⟩ := (AddSubgroup.mem_iSup_of_directed hd).1 x.property
  have := h s.val s.property
  have hm : Mono ((P.ι.map (s.val.arrow ≫ biprod.fst)).app X) := inferInstance
  -- The union inclusion is subtype coercion at every object.
  have hx0 : (biprod.fst : M ⊞ E ⟶ M).hom.app X x.val = 0 := hx
  have hy0 : ((P.ι.map (s.val.arrow ≫ biprod.fst)).app X) y = 0 := by
    simpa only [ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      AddCommGrpCat.comp_apply, hy] using hx0
  have hz : y = 0 := (AddCommGrpCat.mono_iff_injective _).1 hm (by simpa using hy0)
  apply Subtype.ext
  refine hy.symm.trans ?_
  rw [hz, map_zero]
  rfl

private theorem mono_graph_mk {T : ModCat.{v} C} (f : T ⟶ M ⊞ E) [Mono f]
    [Mono (f ≫ biprod.fst)] : Mono ((Subobject.mk f).arrow ≫ biprod.fst) := by
  rw [← Subobject.underlyingIso_hom_comp_eq_mk, assoc]
  infer_instance

private theorem exists_maximal_graph (p : Subobject (M ⊞ E)) (hp : Mono (p.arrow ≫ biprod.fst)) :
    ∃ s, p ≤ s ∧ Maximal (fun t : Subobject (M ⊞ E) ↦ Mono (t.arrow ≫ biprod.fst)) s := by
  apply zorn_le_nonempty₀ {s | Mono (s.arrow ≫ biprod.fst)} _ p hp
  intro S hS hc s hs
  let : Nonempty S := ⟨⟨s, hs⟩⟩
  have := mono_graphUnion_comp_fst S hc.directedOn (fun t ht ↦ hS ht)
  have : Mono (graphUnionι S) := mono_of_mono _ biprod.fst
  refine ⟨Subobject.mk (graphUnionι S), mono_graph_mk _, fun t ht ↦ ?_⟩
  obtain ⟨k, hk⟩ := graphUnion_upperBound S ht
  exact Subobject.le_mk_of_comm k hk

private theorem maximal_graph_factors (hE : E.Baer)
    (s : Subobject (M ⊞ E))
    (hs : Maximal (fun t : Subobject (M ⊞ E) ↦ Mono (t.arrow ≫ biprod.fst)) s)
    {X : C} (f : (yoneda C).obj X ⟶ M) :
    ∃ g : (yoneda C).obj X ⟶ (s : ModCat.{v} C), g ≫ s.arrow ≫ biprod.fst = f := by
  let p := s.arrow ≫ biprod.fst
  have : Mono p := hs.prop
  let a := pullback.fst p f
  let b := pullback.snd p f
  obtain ⟨e, he⟩ := hE.extend b (a ≫ s.arrow ≫ biprod.snd)
  have hp : a ≫ p = b ≫ f := pullback.condition
  let m : pushout a b ⟶ M := pushout.desc p f hp
  let n : pushout a b ⟶ E := pushout.desc (s.arrow ≫ biprod.snd) e he.symm
  have : Mono m := (IsPushout.of_hasPushout a b).mono_of_isPullback_of_mono
    (IsPullback.of_hasPullback p f) m (by simp [m]) (by simp [m])
  let q := biprod.lift m n
  have hq : q ≫ biprod.fst = m := biprod.lift_fst _ _
  have : Mono (q ≫ biprod.fst) := hq ▸ ‹Mono m›
  have : Mono q := mono_of_mono q biprod.fst
  have hleft : pushout.inl a b ≫ q = s.arrow := by
    apply biprod.hom_ext <;> simp [q, m, n, p]
  have hle : s ≤ Subobject.mk q := Subobject.le_mk_of_comm _ hleft
  have heq : Subobject.mk q = s := le_antisymm (hs.le_of_ge (mono_graph_mk q) hle) hle
  refine ⟨pushout.inr a b ≫ Subobject.ofMkLE q s heq.le, ?_⟩
  rw [assoc, ← assoc (Subobject.ofMkLE q s heq.le), Subobject.ofMkLE_arrow, hq]
  exact pushout.inr_desc _ _ _

private theorem maximal_graph_isIso (hE : E.Baer)
    (s : Subobject (M ⊞ E))
    (hs : Maximal (fun t : Subobject (M ⊞ E) ↦ Mono (t.arrow ≫ biprod.fst)) s) :
    IsIso (s.arrow ≫ biprod.fst) := by
  let p := s.arrow ≫ biprod.fst
  have : Mono p := hs.prop
  have : Epi p := by
    let P := additiveFunctor Cᵒᵖ AddCommGrpCat.{v}
    apply P.ι.epi_of_epi_map
    apply (NatTrans.epi_iff_epi_app _).2
    intro X
    apply (AddCommGrpCat.epi_iff_surjective _).2
    intro x
    obtain ⟨g, hg⟩ := maximal_graph_factors hE s hs (yonedaHomEquiv.symm x)
    refine ⟨yonedaHomEquiv g, ?_⟩
    exact (yonedaHomEquiv_comp g p).symm.trans
      ((congrArg yonedaHomEquiv hg).trans (yonedaHomEquiv.apply_symm_apply x))
  exact isIso_of_mono_of_epi p

end

/-- **Baer's criterion.** A module over a preadditive category is injective if and only if every
map from a subobject of a representable extends to that representable. -/
theorem baer_iff_injective (E : ModCat.{v} C) : E.Baer ↔ Injective E := by
  constructor
  · intro hE
    constructor
    intro A M f i _
    let p := biprod.lift i f
    have hp : p ≫ biprod.fst = i := biprod.lift_fst _ _
    have : Mono (p ≫ biprod.fst) := hp ▸ ‹Mono i›
    have : Mono p := mono_of_mono p biprod.fst
    obtain ⟨s, hle, hs⟩ := exists_maximal_graph _ (mono_graph_mk p)
    have := maximal_graph_isIso hE s hs
    let k := Subobject.ofMkLE p s hle
    have hk : k ≫ s.arrow = p := Subobject.ofMkLE_arrow hle
    refine ⟨inv (s.arrow ≫ biprod.fst) ≫ s.arrow ≫ biprod.snd, ?_⟩
    have hi : i = k ≫ s.arrow ≫ biprod.fst := by rw [← assoc, hk, hp]
    calc
      i ≫ inv (s.arrow ≫ biprod.fst) ≫ s.arrow ≫ biprod.snd =
          k ≫ s.arrow ≫ biprod.snd := by
        rw [hi, assoc, IsIso.hom_inv_id_assoc]
      _ = f := by rw [← assoc, hk, biprod.lift_snd]
  · intro hE
    exact (baer_iff_forall_subobject E).2 (fun _ S f ↦ Injective.factors f S.arrow)

end TauCeti.ModCat

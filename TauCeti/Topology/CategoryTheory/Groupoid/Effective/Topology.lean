/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocalAtTarget
public import TauCeti.Topology.CategoryTheory.Groupoid.Effective.Basic
public import TauCeti.Topology.CategoryTheory.Functor.Continuous

/-!
# The arrow topology of the effective quotient

The total arrows of `EffectiveQuotient C` carry the quotient topology of the total arrows of
`C`. For an étale topological groupoid the arrow projection is an open quotient map and a
local homeomorphism. Source and target remain local homeomorphisms, and properness of the
source-target map descends. Thus passing to germs preserves the local topology of arrow
charts, while identifying ineffective labels globally. The quotient is a topological groupoid,
and its only ineffective arrows are units.

No Hausdorffness or properness is needed for the local-homeomorphism statements. In particular,
they do not assert Hausdorffness of the effective arrow space of an arbitrary étale groupoid.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public section

open CategoryTheory Set Topology

namespace TauCeti

variable {C : Type*} [Groupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)]

namespace EffectiveQuotient

variable (C) in
/-- Effective arrows carry the quotient topology from the original total arrow space. -/
instance instTopologicalSpaceArrows : TopologicalSpace (Quiver.Total (EffectiveQuotient C)) :=
  .coinduced (toEffectiveQuotient C).toPrefunctor.mapTotal inferInstance

omit [TopologicalSpace C] in
/-- Every total arrow of the effective quotient lifts with its endpoints fixed. -/
theorem mapTotal_surjective :
    Function.Surjective (toEffectiveQuotient C).toPrefunctor.mapTotal := by
  rintro ⟨⟨x⟩, ⟨y⟩, f⟩
  obtain ⟨g, rfl⟩ := (toEffectiveQuotient C).map_surjective f
  exact ⟨⟨x, y, g⟩, rfl⟩

omit [TopologicalSpace C] in
/-- The arrow projection is a quotient map by construction. -/
theorem isQuotientMap_mapTotal :
    IsQuotientMap (toEffectiveQuotient C).toPrefunctor.mapTotal :=
  ⟨⟨rfl⟩, mapTotal_surjective⟩

/-- Effective reduction is continuous on objects and total arrows. -/
theorem isTopologicallyContinuous_toEffectiveQuotient :
    (toEffectiveQuotient C).IsTopologicallyContinuous :=
  ⟨isHomeomorph_toEffectiveQuotient_obj.continuous, isQuotientMap_mapTotal.continuous⟩

variable [IsTopologicalGroupoid C]

/-- Source is continuous for the effective arrow quotient topology. -/
@[fun_prop]
theorem continuous_source :
    Continuous (Quiver.Total.left : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) :=
  isQuotientMap_mapTotal.continuous_iff.mpr
    (isHomeomorph_toEffectiveQuotient_obj.continuous.comp IsTopologicalGroupoid.continuous_source)

/-- Target is continuous for the effective arrow quotient topology. -/
@[fun_prop]
theorem continuous_target :
    Continuous (Quiver.Total.right : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) :=
  isQuotientMap_mapTotal.continuous_iff.mpr
    (isHomeomorph_toEffectiveQuotient_obj.continuous.comp IsTopologicalGroupoid.continuous_target)

variable
  (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))

include hs

/-- The arrow projection is open: saturation of an open set is obtained by composing with
the open set of ineffective arrows. -/
theorem isOpenMap_mapTotal :
    IsOpenMap (toEffectiveQuotient C).toPrefunctor.mapTotal := by
  intro U hU
  apply isQuotientMap_mapTotal.isOpen_preimage.mp
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨x, y, b⟩ ⟨⟨x', y', a⟩, ha, hab⟩
  have hx : x' = x := (isHomeomorph_toEffectiveQuotient_obj (C := C)).injective
    (congrArg Quiver.Total.left hab)
  have hy : y' = y := (isHomeomorph_toEffectiveQuotient_obj (C := C)).injective
    (congrArg Quiver.Total.right hab)
  subst x' y'
  have hm : (toEffectiveQuotient C).map a = (toEffectiveQuotient C).map b :=
    eq_of_heq (Quiver.Total.mk.inj hab).2.2
  have hk : (⟨x, x, b ≫ inv a⟩ : Quiver.Total C) ∈ ineffectiveArrows C :=
    (toEffectiveQuotient_map_eq_iff hs).mp hm.symm
  have hev := eventually_exists_comp_eq hs.isOpenMap
    (a := (⟨x, x, b ≫ inv a⟩ : Quiver.Total C)) (b := ⟨x, y, a⟩) rfl
    (isOpen_ineffectiveArrows.mem_nhds hk) (hU.mem_nhds ha)
  have hcomp : (⟨x, x, b ≫ inv a⟩ : Quiver.Total C).comp ⟨x, y, a⟩ rfl = ⟨x, y, b⟩ := by
    simp
  rw [hcomp] at hev
  filter_upwards [hev] with c ⟨k, hk, d, hd, hkd, hcomp⟩
  refine ⟨d, hd, ?_⟩
  obtain ⟨z, z', k⟩ := k
  obtain ⟨w, v, d⟩ := d
  have hzz' := left_eq_right_of_mem_ineffectiveArrows hk
  dsimp only at hzz' hkd
  subst z' w
  rw [← hcomp, Quiver.Total.mk_comp_mk]
  have hkid : (toEffectiveQuotient C).map k = 𝟙 _ :=
    (toEffectiveQuotient_map_eq_id_iff hs).mpr hk
  simp only [Prefunctor.mapTotal_mk, Functor.toPrefunctor_map,
    Functor.map_comp, hkid, Category.id_comp]

/-- Effective reduction is an open quotient on the actual total arrow spaces. -/
theorem isOpenQuotientMap_mapTotal :
    IsOpenQuotientMap (toEffectiveQuotient C).toPrefunctor.mapTotal :=
  .of_isOpenMap_isQuotientMap (isOpenMap_mapTotal hs) isQuotientMap_mapTotal

/-- Each source chart of the original groupoid embeds openly in the effective arrow space;
in particular the projection to effective arrows is a local homeomorphism. -/
theorem isLocalHomeomorph_mapTotal :
    IsLocalHomeomorph (toEffectiveQuotient C).toPrefunctor.mapTotal := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro a
  obtain ⟨U, hU, haU, hinj⟩ := hs.isLocallyInjective a
  refine ⟨U, hU.mem_nhds haU, .of_continuous_injective_isOpenMap
    (isQuotientMap_mapTotal.continuous.comp continuous_subtype_val) ?_
    ((isOpenMap_mapTotal hs).comp hU.isOpenMap_subtype_val)⟩
  intro b c hbc
  apply Subtype.ext
  exact hinj b.2 c.2
    ((isHomeomorph_toEffectiveQuotient_obj (C := C)).injective (congrArg Quiver.Total.left hbc))

/-- The source of the effective quotient remains a local homeomorphism. -/
theorem isLocalHomeomorph_source :
    IsLocalHomeomorph
      (Quiver.Total.left : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) := by
  apply IsLocalHomeomorph.of_comp_of_surjective
    (f := (toEffectiveQuotient C).toPrefunctor.mapTotal) ?_
    (isLocalHomeomorph_mapTotal hs) mapTotal_surjective
  simpa only [Function.comp_def, objHomeomorph_apply, Prefunctor.mapTotal_left,
    Functor.toPrefunctor_obj] using
    (objHomeomorph C).isLocalHomeomorph.comp hs

/-- The target of the effective quotient remains a local homeomorphism. -/
theorem isLocalHomeomorph_target :
    IsLocalHomeomorph
      (Quiver.Total.right : Quiver.Total (EffectiveQuotient C) → EffectiveQuotient C) := by
  apply IsLocalHomeomorph.of_comp_of_surjective
    (f := (toEffectiveQuotient C).toPrefunctor.mapTotal) ?_
    (isLocalHomeomorph_mapTotal hs) mapTotal_surjective
  simpa only [Function.comp_def, objHomeomorph_apply, Prefunctor.mapTotal_right,
    Functor.toPrefunctor_obj] using
    (objHomeomorph C).isLocalHomeomorph.comp
      ((IsTopologicalGroupoid.isLocalHomeomorph_source_iff_target C).mp hs)

omit hs [IsTopologicalGroupoid C] in
/-- Properness of source-target descends to the effective quotient. No separation hypothesis
on either arrow space is needed. -/
theorem isProperMap_source_target
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right)) :
    IsProperMap fun a : Quiver.Total (EffectiveQuotient C) ↦ (a.left, a.right) := by
  have hcomp : IsProperMap ((fun a : Quiver.Total (EffectiveQuotient C) ↦
      (a.left, a.right)) ∘ (toEffectiveQuotient C).toPrefunctor.mapTotal) := by
    simpa only [Function.comp_def, Prod.map_apply,
      Prefunctor.mapTotal_left, Prefunctor.mapTotal_right,
      Functor.toPrefunctor_obj] using
    ((isHomeomorph_toEffectiveQuotient_obj (C := C)).isProperMap.prodMap
      (isHomeomorph_toEffectiveQuotient_obj (C := C)).isProperMap).comp hp
  exact isProperMap_of_comp_of_surj isQuotientMap_mapTotal.continuous
    (isQuotientMap_mapTotal.continuous_iff.mpr hcomp.continuous) hcomp mapTotal_surjective

/-- The effective quotient of an étale topological groupoid is a topological groupoid for
the quotient topology on its total arrows. -/
theorem isTopologicalGroupoid : IsTopologicalGroupoid (EffectiveQuotient C) where
  continuous_source := continuous_source
  continuous_target := continuous_target
  continuous_unit := by
    apply (isHomeomorph_toEffectiveQuotient_obj (C := C)).isQuotientMap.continuous_iff.mpr
    simpa [Function.comp_def, Prefunctor.mapTotal] using
      isQuotientMap_mapTotal.continuous.comp
        (IsTopologicalGroupoid.continuous_unit (C := C))
  continuous_inverse := by
    apply isQuotientMap_mapTotal.continuous_iff.mpr
    simpa [Function.comp_def, Prefunctor.mapTotal] using
      isQuotientMap_mapTotal.continuous.comp
        (IsTopologicalGroupoid.continuous_inverse (C := C))
  continuous_comp := by
    let q := (toEffectiveQuotient C).toPrefunctor.mapTotal
    let S : Set (Quiver.Total (EffectiveQuotient C) × Quiver.Total (EffectiveQuotient C)) :=
      {p | p.1.right = p.2.left}
    have hq := isOpenQuotientMap_mapTotal hs
    have hp := (hq.prodMap hq).restrictPreimage S
    apply hp.isQuotientMap.continuous_iff.mpr
    -- The object map is injective, so a pair of effective arrows is composable precisely
    -- when any pair of its lifts is composable.
    let lift : (Prod.map q q) ⁻¹' S →
        {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} := fun p ↦
      ⟨p.1, (isHomeomorph_toEffectiveQuotient_obj (C := C)).injective p.2⟩
    have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
    convert hq.continuous.comp (IsTopologicalGroupoid.continuous_comp.comp hlift) using 1
    funext p
    obtain ⟨⟨⟨x, y, a⟩, ⟨z, w, b⟩⟩, h⟩ := p
    have hyz : y = z := (isHomeomorph_toEffectiveQuotient_obj (C := C)).injective h
    subst z
    simp [Set.restrictPreimage, q, lift, Quiver.Total.comp_def, Prefunctor.mapTotal]

/-- An arrow becomes ineffective in the quotient exactly when it was already ineffective. -/
@[simp]
theorem preimage_ineffectiveArrows :
    (toEffectiveQuotient C).toPrefunctor.mapTotal ⁻¹'
      ineffectiveArrows (EffectiveQuotient C) = ineffectiveArrows C := by
  ext a
  rw [Set.mem_preimage, mem_ineffectiveArrows_iff, mem_ineffectiveArrows_iff,
    ← (isOpenQuotientMap_mapTotal hs).map_nhds_eq a, Filter.eventually_map]
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun b ↦
    (isHomeomorph_toEffectiveQuotient_obj (C := C)).injective.eq_iff)

/-- Only unit arrows of the effective quotient induce identity germs on objects. -/
theorem ineffectiveArrows_eq_range_unit :
    ineffectiveArrows (EffectiveQuotient C) =
      Set.range fun x : EffectiveQuotient C ↦
        (⟨x, x, 𝟙 x⟩ : Quiver.Total (EffectiveQuotient C)) := by
  apply Subset.antisymm
  · intro a ha
    obtain ⟨⟨x, y, f⟩, rfl⟩ := mapTotal_surjective a
    have hf : (⟨x, y, f⟩ : Quiver.Total C) ∈ ineffectiveArrows C := by
      rwa [← preimage_ineffectiveArrows hs]
    have hxy : x = y := left_eq_right_of_mem_ineffectiveArrows hf
    subst y
    refine ⟨(toEffectiveQuotient C).obj x, ?_⟩
    simp [Prefunctor.mapTotal, (toEffectiveQuotient_map_eq_id_iff hs).mpr hf]
  · rintro _ ⟨x, rfl⟩
    let := isTopologicalGroupoid hs
    exact id_mem_ineffectiveArrows (isLocalHomeomorph_source hs) x

end EffectiveQuotient

end TauCeti

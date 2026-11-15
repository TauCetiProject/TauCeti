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
and its only ineffective arrows are units, so its ineffective kernels are trivial and iterating
effective reduction is faithful. Second countability of objects and arrows descends, and the
effective arrow space is Hausdorff if and only if the object space is Hausdorff and
`ineffectiveArrows C` is closed in the original arrow space.

No Hausdorffness or properness is needed for the local-homeomorphism statements. In particular,
an arbitrary étale groupoid need not have a Hausdorff effective arrow space unless its
ineffective arrows are closed.

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

omit hs [IsTopologicalGroupoid C] [TopologicalSpace (Quiver.Total C)] in
/-- The objects of the effective quotient are Hausdorff when those of the groupoid are. -/
instance instT2SpaceObjects [T2Space C] : T2Space (EffectiveQuotient C) :=
  (objHomeomorph C).t2Space

omit hs [IsTopologicalGroupoid C] [TopologicalSpace (Quiver.Total C)] in
/-- The objects of the effective quotient are second countable when those of the groupoid are. -/
instance instSecondCountableTopologyObjects [SecondCountableTopology C] :
    SecondCountableTopology (EffectiveQuotient C) :=
  (objHomeomorph C).symm.isInducing.secondCountableTopology

/-- The total arrows of the effective quotient of an étale groupoid are second countable when
those of the original groupoid are, since the arrow projection is an open quotient map. -/
theorem secondCountableTopology_arrows [SecondCountableTopology (Quiver.Total C)] :
    SecondCountableTopology (Quiver.Total (EffectiveQuotient C)) :=
  (isOpenQuotientMap_mapTotal hs).secondCountableTopology

/-- Every ineffective kernel of the effective quotient is trivial: effective reduction leaves no
nontrivial ineffective isotropy. -/
theorem ineffectiveKernel_eq_bot (y : EffectiveQuotient C) :
    letI := isTopologicalGroupoid hs
    ineffectiveKernel (isLocalHomeomorph_source hs) y = ⊥ := by
  let _ := isTopologicalGroupoid hs
  rw [eq_bot_iff]
  intro g hg
  rw [mem_ineffectiveKernel, ineffectiveArrows_eq_range_unit hs] at hg
  obtain ⟨z, hz⟩ := hg
  have hzy : z = y := congrArg Quiver.Total.left hz
  subst z
  exact Subgroup.mem_bot.mpr (Aut.ext (Iso.ext (eq_of_heq (Quiver.Total.mk.inj hz).2.2).symm))

/-- Iterating effective reduction does not collapse any further arrows: the projection from the
effective quotient to its own effective quotient is faithful. -/
theorem toEffectiveQuotient_faithful :
    letI := isTopologicalGroupoid hs
    (toEffectiveQuotient (EffectiveQuotient C)).Faithful := by
  let _ := isTopologicalGroupoid hs
  exact (toEffectiveQuotient_faithful_iff (isLocalHomeomorph_source hs)).mpr
    (ineffectiveKernel_eq_bot hs)

/-- **Hausdorffness criterion for the effective arrow space.** For an étale topological groupoid,
the total arrow space of `EffectiveQuotient C` is Hausdorff if and only if the object space is
Hausdorff and the ineffective arrows form a closed subset of the original arrow space. -/
theorem t2Space_arrows_iff :
    T2Space (Quiver.Total (EffectiveQuotient C)) ↔
      T2Space C ∧ IsClosed (ineffectiveArrows C) := by
  refine ⟨fun hT2 ↦ ?_, fun ⟨hT2, hclosed⟩ ↦ ?_⟩
  · let _ := isTopologicalGroupoid hs
    let _ := hT2
    let _ : T2Space (EffectiveQuotient C) :=
      (IsTopologicalGroupoid.isEmbedding_unit (EffectiveQuotient C)).t2Space
    refine ⟨(objHomeomorph C).symm.t2Space, ?_⟩
    rw [← preimage_ineffectiveArrows hs, ineffectiveArrows_eq_range_unit hs]
    exact (isClosed_range_unit IsTopologicalGroupoid.continuous_unit
      continuous_source).preimage isQuotientMap_mapTotal.continuous
  · let _ := hT2
    rw [t2Space_iff_of_isOpenQuotientMap (isOpenQuotientMap_mapTotal hs)]
    let S : Set (Quiver.Total C × Quiver.Total C) := {p | p.1.right = p.2.right}
    have hS : IsClosed S := isClosed_eq
      (IsTopologicalGroupoid.continuous_target.comp continuous_fst)
      (IsTopologicalGroupoid.continuous_target.comp continuous_snd)
    -- On pairs of arrows with the same target, `p.1 ≫ inv p.2` is continuous and detects equal
    -- germs (which automatically forces equal sources).
    let δ : S → Quiver.Total C := fun p ↦
      p.1.1.comp ⟨p.1.2.right, p.1.2.left, inv p.1.2.hom⟩ p.2
    have hδ : Continuous δ := IsTopologicalGroupoid.continuous_comp.comp
      (((continuous_fst.comp continuous_subtype_val).prodMk
        (IsTopologicalGroupoid.continuous_inverse.comp
          (continuous_snd.comp continuous_subtype_val))).subtype_mk fun p ↦ p.2)
    have hrel :
        {p : Quiver.Total C × Quiver.Total C |
          (toEffectiveQuotient C).toPrefunctor.mapTotal p.1 =
            (toEffectiveQuotient C).toPrefunctor.mapTotal p.2} =
          Subtype.val '' (δ ⁻¹' ineffectiveArrows C) := by
      ext ⟨⟨x₁, y₁, f₁⟩, ⟨x₂, y₂, f₂⟩⟩
      constructor
      · intro h
        have hx : x₁ = x₂ :=
          (isHomeomorph_toEffectiveQuotient_obj (C := C)).injective (congrArg Quiver.Total.left h)
        have hy : y₁ = y₂ :=
          (isHomeomorph_toEffectiveQuotient_obj (C := C)).injective (congrArg Quiver.Total.right h)
        subst x₂ y₂
        have hm : (toEffectiveQuotient C).map f₁ = (toEffectiveQuotient C).map f₂ :=
          eq_of_heq (Quiver.Total.mk.inj h).2.2
        refine ⟨⟨(⟨x₁, y₁, f₁⟩, ⟨x₁, y₁, f₂⟩), rfl⟩, ?_, rfl⟩
        simpa only [Set.mem_preimage, δ, Quiver.Total.mk_comp_mk] using
          (toEffectiveQuotient_map_eq_iff hs).mp hm
      · rintro ⟨p, hmem, heq⟩
        have hy : y₁ = y₂ := by simpa only [S, Set.mem_ofPred_eq, heq] using p.2
        subst y₂
        have hp : p = ⟨(⟨x₁, y₁, f₁⟩, ⟨x₂, y₁, f₂⟩), rfl⟩ := Subtype.ext heq
        subst hp
        have hmem' : (⟨x₁, x₂, f₁ ≫ inv f₂⟩ : Quiver.Total C) ∈ ineffectiveArrows C := by
          simpa only [Set.mem_preimage, δ, Quiver.Total.mk_comp_mk] using hmem
        have hx : x₁ = x₂ := left_eq_right_of_mem_ineffectiveArrows hmem'
        subst x₂
        simp [Prefunctor.mapTotal, (toEffectiveQuotient_map_eq_iff hs).mpr hmem']
    rw [hrel]
    exact hS.isClosedEmbedding_subtypeVal.isClosedMap _ (hclosed.preimage hδ)

/-- In an étale topological groupoid with Hausdorff arrow space, closedness of the ineffective
arrows makes the effective arrow space Hausdorff. -/
theorem t2Space_arrows_of_isClosed [T2Space (Quiver.Total C)]
    (hclosed : IsClosed (ineffectiveArrows C)) :
    T2Space (Quiver.Total (EffectiveQuotient C)) :=
  (t2Space_arrows_iff hs).mpr ⟨(IsTopologicalGroupoid.isEmbedding_unit C).t2Space, hclosed⟩

end EffectiveQuotient

end TauCeti

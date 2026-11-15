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

No Hausdorffness or properness is needed for the local-homeomorphism statements, and second
countability descends directly along the open arrow quotient. Every ineffective kernel of the
effective quotient is trivial, so applying effective reduction a second time is faithful. When
the object space is Hausdorff, the effective arrow space is Hausdorff if and only if the
ineffective arrows of `C` form a closed subset of the original arrow space.

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
/-- Objects of the effective quotient inherit the Hausdorff property from `C`. -/
instance instT2SpaceObjects [T2Space C] : T2Space (EffectiveQuotient C) :=
  (objHomeomorph C).symm.isEmbedding.t2Space

omit hs [IsTopologicalGroupoid C] [TopologicalSpace (Quiver.Total C)] in
/-- Objects of the effective quotient inherit second countability from `C`. -/
instance instSecondCountableTopologyObjects [SecondCountableTopology C] :
    SecondCountableTopology (EffectiveQuotient C) :=
  (objHomeomorph C).symm.secondCountableTopology

/-- Second countability of the total arrow space descends along the open arrow quotient map of an
étale topological groupoid. -/
theorem secondCountableTopology_arrows [SecondCountableTopology (Quiver.Total C)] :
    SecondCountableTopology (Quiver.Total (EffectiveQuotient C)) :=
  (isOpenQuotientMap_mapTotal hs).secondCountableTopology

/-- Every ineffective kernel of the effective quotient is trivial: no nonidentity automorphism of
`EffectiveQuotient C` induces the identity germ. -/
@[simp]
theorem ineffectiveKernel_eq_bot (x : EffectiveQuotient C) :
    letI := isTopologicalGroupoid hs
    ineffectiveKernel (isLocalHomeomorph_source hs) x = ⊥ := by
  let := isTopologicalGroupoid hs
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦ ?_
  rw [mem_ineffectiveKernel, ineffectiveArrows_eq_range_unit hs] at hg
  obtain ⟨y, hy⟩ := hg
  have hyx : y = x := congrArg Quiver.Total.left hy
  subst hyx
  exact Aut.ext (Iso.ext (eq_of_heq (Quiver.Total.mk.inj hy).2.2).symm)

/-- Effective reduction is idempotent up to isomorphism: the projection from `EffectiveQuotient C`
to its own effective quotient is faithful. -/
theorem faithful_toEffectiveQuotient :
    letI := isTopologicalGroupoid hs
    (toEffectiveQuotient (EffectiveQuotient C)).Faithful := by
  let := isTopologicalGroupoid hs
  exact (toEffectiveQuotient_faithful_iff (isLocalHomeomorph_source hs)).mpr
    (ineffectiveKernel_eq_bot hs)

/-- If the effective arrow space is Hausdorff, the ineffective arrows of `C` form a closed set:
they are the preimage of the unit retract of `EffectiveQuotient C`. -/
theorem isClosed_ineffectiveArrows_of_t2Space_arrows
    [T2Space (Quiver.Total (EffectiveQuotient C))] :
    IsClosed (ineffectiveArrows C) := by
  let := isTopologicalGroupoid hs
  rw [← preimage_ineffectiveArrows hs, ineffectiveArrows_eq_range_unit hs]
  exact (Function.LeftInverse.isClosed_range (f := Quiver.Total.left) (fun _ ↦ rfl)
    continuous_source IsTopologicalGroupoid.continuous_unit).preimage
    isQuotientMap_mapTotal.continuous

/-- For an étale topological groupoid over a Hausdorff object space, closedness of
`ineffectiveArrows C` makes the effective arrow space Hausdorff. -/
theorem t2Space_arrows_of_isClosed_ineffectiveArrows [T2Space C]
    (hcl : IsClosed (ineffectiveArrows C)) :
    T2Space (Quiver.Total (EffectiveQuotient C)) := by
  rw [t2Space_iff_of_isOpenQuotientMap (isOpenQuotientMap_mapTotal hs)]
  let E : Set (Quiver.Total C × Quiver.Total C) := {p | p.1.right = p.2.right}
  have hE : IsClosed E := isClosed_eq
    (IsTopologicalGroupoid.continuous_target.comp continuous_fst)
    (IsTopologicalGroupoid.continuous_target.comp continuous_snd)
  let pair : E → {q : Quiver.Total C × Quiver.Total C // q.1.right = q.2.left} :=
    fun p ↦ ⟨(p.1.1, ⟨p.1.2.right, p.1.2.left, inv p.1.2.hom⟩), p.2⟩
  have hpair : Continuous pair :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (IsTopologicalGroupoid.continuous_inverse.comp
        (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  let δ : E → Quiver.Total C :=
    (fun q : {q : Quiver.Total C × Quiver.Total C // q.1.right = q.2.left} ↦
      q.1.1.comp q.1.2 q.2) ∘ pair
  have hδ : Continuous δ := IsTopologicalGroupoid.continuous_comp.comp hpair
  have himg : IsClosed ((Subtype.val : E → _) '' (δ ⁻¹' ineffectiveArrows C)) :=
    hE.isClosedEmbedding_subtypeVal.isClosedMap _ (hcl.preimage hδ)
  convert himg using 1
  ext ⟨⟨x₁, y₁, f⟩, ⟨x₂, y₂, g⟩⟩
  constructor
  · intro hm
    have hx : x₁ = x₂ := (isHomeomorph_toEffectiveQuotient_obj (C := C)).injective
      (congrArg Quiver.Total.left hm)
    have hy : y₁ = y₂ := (isHomeomorph_toEffectiveQuotient_obj (C := C)).injective
      (congrArg Quiver.Total.right hm)
    subst hx hy
    have hmf : (toEffectiveQuotient C).map f = (toEffectiveQuotient C).map g :=
      eq_of_heq (Quiver.Total.mk.inj hm).2.2
    refine ⟨⟨(⟨x₁, y₁, f⟩, ⟨x₁, y₁, g⟩), rfl⟩, ?_, rfl⟩
    simpa [δ, pair, Quiver.Total.comp_def] using (toEffectiveQuotient_map_eq_iff hs).mp hmf
  · rintro ⟨⟨⟨a, b⟩, hab⟩, hmem, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have hy : y₁ = y₂ := hab
    subst hy
    have hmem' : (⟨x₁, x₂, f ≫ inv g⟩ : Quiver.Total C) ∈ ineffectiveArrows C := by
      simpa [δ, pair, Quiver.Total.comp_def] using hmem
    have hx : x₁ = x₂ := left_eq_right_of_mem_ineffectiveArrows hmem'
    subst hx
    have hmf : (toEffectiveQuotient C).map f = (toEffectiveQuotient C).map g :=
      (toEffectiveQuotient_map_eq_iff hs).mpr hmem'
    simp [Prefunctor.mapTotal, hmf]

/-- **Hausdorff criterion for the effective arrow space.** For an étale topological groupoid over a
Hausdorff object space, the total arrow space of `EffectiveQuotient C` is Hausdorff if and only if
`ineffectiveArrows C` is closed in `Quiver.Total C`. -/
theorem t2Space_arrows_iff_isClosed_ineffectiveArrows [T2Space C] :
    T2Space (Quiver.Total (EffectiveQuotient C)) ↔ IsClosed (ineffectiveArrows C) :=
  ⟨fun _ ↦ isClosed_ineffectiveArrows_of_t2Space_arrows hs,
    t2Space_arrows_of_isClosed_ineffectiveArrows hs⟩

end EffectiveQuotient

end TauCeti

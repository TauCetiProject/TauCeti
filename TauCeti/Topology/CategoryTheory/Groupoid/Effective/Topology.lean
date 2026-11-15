/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocalAtTarget
public import TauCeti.Topology.CategoryTheory.Groupoid.Effective.Basic
public import TauCeti.Topology.CategoryTheory.Functor.Continuous

import Mathlib.Topology.Bases

/-!
# The arrow topology of the effective quotient

The total arrows of `EffectiveQuotient C` carry the quotient topology of the total arrows of
`C`. For an étale topological groupoid the arrow projection is an open quotient map and a
local homeomorphism. Source and target remain local homeomorphisms, and properness of the
source-target map descends. Thus passing to germs preserves the local topology of arrow
charts, while identifying ineffective labels globally. The quotient is a topological groupoid,
its only ineffective arrows are units, and every ineffective kernel in the quotient is trivial.

No Hausdorffness or properness is needed for the local-homeomorphism statements. Instead,
`TauCeti.EffectiveQuotient.t2Space_arrows_iff` characterizes Hausdorffness of the effective arrow
space: for an étale topological groupoid, `Quiver.Total (EffectiveQuotient C)` is Hausdorff
precisely when `C` is Hausdorff and `TauCeti.ineffectiveArrows C` is closed. Second countability
descends to both objects and total arrows. When every arrow of `C` is ineffective, the effective
quotient is categorically equivalent to `Discrete C` and its arrow space is homeomorphic to its
object space via the source map.

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

/-- The objects of the effective quotient of a Hausdorff space are Hausdorff. -/
instance instT2SpaceObjects [T2Space C] : T2Space (EffectiveQuotient C) :=
  (objHomeomorph C).symm.isEmbedding.t2Space

/-- The objects of the effective quotient of a second-countable space are second countable. -/
instance instSecondCountableTopologyObjects [SecondCountableTopology C] :
    SecondCountableTopology (EffectiveQuotient C) :=
  (objHomeomorph C).symm.isInducing.secondCountableTopology

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

/-- Second countability of the total arrow space descends to the effective quotient along the open
arrow quotient map. -/
theorem secondCountableTopology_arrows [SecondCountableTopology (Quiver.Total C)] :
    SecondCountableTopology (Quiver.Total (EffectiveQuotient C)) :=
  (isOpenQuotientMap_mapTotal hs).secondCountableTopology

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

/-- Every ineffective kernel of the effective quotient is trivial: effective reduction leaves no
nontrivial ineffective isotropy. -/
@[simp]
theorem ineffectiveKernel_eq_bot (y : EffectiveQuotient C) :
    letI := isTopologicalGroupoid hs
    ineffectiveKernel (isLocalHomeomorph_source hs) y = ⊥ := by
  let := isTopologicalGroupoid hs
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rw [mem_ineffectiveKernel, ineffectiveArrows_eq_range_unit hs] at hg
  obtain ⟨x, hx⟩ := hg
  have hxy : x = y := congrArg Quiver.Total.left hx
  subst hxy
  exact Aut.ext (Iso.ext (eq_of_heq (Quiver.Total.mk.inj hx).2.2).symm)

/-- Two total arrows have the same image in the effective quotient precisely when they share a
target and the first followed by the inverse of the second is ineffective. -/
private theorem setOf_mapTotal_eq :
    {p : Quiver.Total C × Quiver.Total C |
      (toEffectiveQuotient C).toPrefunctor.mapTotal p.1 =
        (toEffectiveQuotient C).toPrefunctor.mapTotal p.2} =
      Subtype.val '' ((fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.right} ↦
        p.1.1.comp ⟨p.1.2.right, p.1.2.left, inv p.1.2.hom⟩ p.2) ⁻¹' ineffectiveArrows C) := by
  ext ⟨⟨x, y, f⟩, ⟨x', y', g⟩⟩
  constructor
  · intro h
    have hx : x = x' :=
      (isHomeomorph_toEffectiveQuotient_obj (C := C)).injective (congrArg Quiver.Total.left h)
    have hy : y = y' :=
      (isHomeomorph_toEffectiveQuotient_obj (C := C)).injective (congrArg Quiver.Total.right h)
    subst x' y'
    have hm : (toEffectiveQuotient C).map f = (toEffectiveQuotient C).map g :=
      eq_of_heq (Quiver.Total.mk.inj h).2.2
    exact ⟨⟨(⟨x, y, f⟩, ⟨x, y, g⟩), rfl⟩, by simpa using (toEffectiveQuotient_map_eq_iff hs).mp hm,
      rfl⟩
  · rintro ⟨⟨⟨⟨x, y, f⟩, ⟨x', y', g⟩⟩, (hy : y = y')⟩, hmem, hval⟩
    cases hval
    subst y'
    have hf : (⟨x, x', f ≫ inv g⟩ : Quiver.Total C) ∈ ineffectiveArrows C := by simpa using hmem
    obtain rfl : x = x' := left_eq_right_of_mem_ineffectiveArrows hf
    simp [Prefunctor.mapTotal, (toEffectiveQuotient_map_eq_iff hs).mpr hf]

/-- **Hausdorffness of the effective arrow space.** For an étale topological groupoid, the total
arrow space of `EffectiveQuotient C` is Hausdorff if and only if the object space `C` is Hausdorff
and `ineffectiveArrows C` is closed in `Quiver.Total C`. -/
theorem t2Space_arrows_iff :
    T2Space (Quiver.Total (EffectiveQuotient C)) ↔
      T2Space C ∧ IsClosed (ineffectiveArrows C) := by
  let := isTopologicalGroupoid hs
  refine ⟨fun _ ↦ ?_, fun ⟨_, hc⟩ ↦ ?_⟩
  · have : T2Space (EffectiveQuotient C) :=
      (IsTopologicalGroupoid.isEmbedding_unit (EffectiveQuotient C)).t2Space
    refine ⟨(objHomeomorph C).isEmbedding.t2Space, ?_⟩
    rw [← preimage_ineffectiveArrows hs, ineffectiveArrows_eq_range_unit hs]
    exact (isClosed_range_unit IsTopologicalGroupoid.continuous_unit continuous_source).preimage
      isQuotientMap_mapTotal.continuous
  · rw [t2Space_iff_of_isOpenQuotientMap (isOpenQuotientMap_mapTotal hs), setOf_mapTotal_eq hs]
    have hR : IsClosed {p : Quiver.Total C × Quiver.Total C | p.1.right = p.2.right} :=
      isClosed_eq (IsTopologicalGroupoid.continuous_target.comp continuous_fst)
        (IsTopologicalGroupoid.continuous_target.comp continuous_snd)
    have hδ : Continuous (fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.right} ↦
        p.1.1.comp ⟨p.1.2.right, p.1.2.left, inv p.1.2.hom⟩ p.2) :=
      IsTopologicalGroupoid.continuous_comp.comp
        (((continuous_fst.comp continuous_subtype_val).prodMk
          (IsTopologicalGroupoid.continuous_inverse.comp
            (continuous_snd.comp continuous_subtype_val))).subtype_mk fun p ↦ p.2)
    exact hR.isClosedEmbedding_subtypeVal.isClosedMap _ (hc.preimage hδ)

/-- The effective arrow space is Hausdorff when the object space is Hausdorff and the ineffective
arrows are closed. -/
theorem t2Space_arrows [T2Space C] (hc : IsClosed (ineffectiveArrows C)) :
    T2Space (Quiver.Total (EffectiveQuotient C)) :=
  (t2Space_arrows_iff hs).mpr ⟨‹_›, hc⟩

section PurelyIneffective

/-- When every arrow of an étale topological groupoid is ineffective, its effective quotient is a
thin category: between any two objects there is at most one effective arrow. -/
theorem isThin_of_ineffectiveArrows_eq_univ (h : ineffectiveArrows C = univ) :
    Quiver.IsThin (EffectiveQuotient C) := fun u v ↦ ⟨fun f g ↦ by
  obtain ⟨x⟩ := u
  obtain ⟨y⟩ := v
  obtain ⟨f₀, rfl⟩ := (toEffectiveQuotient C).map_surjective f
  obtain ⟨g₀, rfl⟩ := (toEffectiveQuotient C).map_surjective g
  have hf : (⟨x, y, f₀⟩ : Quiver.Total C) ∈ ineffectiveArrows C := h ▸ mem_univ _
  obtain rfl : x = y := left_eq_right_of_mem_ineffectiveArrows hf
  have hg : (⟨x, x, g₀⟩ : Quiver.Total C) ∈ ineffectiveArrows C := h ▸ mem_univ _
  rw [(toEffectiveQuotient_map_eq_id_iff hs).mpr hf,
    (toEffectiveQuotient_map_eq_id_iff hs).mpr hg]⟩

/-- When every arrow of an étale topological groupoid is ineffective, its effective quotient is
categorically equivalent to the discrete category `Discrete C`. -/
def equivalenceDiscreteOfIneffectiveArrowsEqUniv (h : ineffectiveArrows C = univ) :
    EffectiveQuotient C ≌ Discrete C :=
  haveI := isThin_of_ineffectiveArrows_eq_univ hs h
  let F₀ : C ⥤ Discrete C :=
    { obj x := Discrete.mk x
      map {x y} f := Discrete.eqToHom
        (left_eq_right_of_mem_ineffectiveArrows (a := ⟨x, y, f⟩) (h ▸ mem_univ _)) }
  { functor := CategoryTheory.Quotient.lift (germRel C) F₀ fun _ _ _ _ _ ↦ Subsingleton.elim _ _
    inverse := Discrete.functor (toEffectiveQuotient C).obj
    unitIso := NatIso.ofComponents (fun u ↦ by obtain ⟨x⟩ := u; exact Iso.refl _)
    counitIso := NatIso.ofComponents (fun x ↦ by obtain ⟨x⟩ := x; exact Iso.refl _) }

@[simp]
theorem equivalenceDiscreteOfIneffectiveArrowsEqUniv_functor_obj_toEffectiveQuotient
    (h : ineffectiveArrows C = univ) (x : C) :
    (equivalenceDiscreteOfIneffectiveArrowsEqUniv hs h).functor.obj
      ((toEffectiveQuotient C).obj x) = Discrete.mk x :=
  (rfl)

@[simp]
theorem equivalenceDiscreteOfIneffectiveArrowsEqUniv_inverse_obj
    (h : ineffectiveArrows C = univ) (x : C) :
    (equivalenceDiscreteOfIneffectiveArrowsEqUniv hs h).inverse.obj (Discrete.mk x) =
      (toEffectiveQuotient C).obj x :=
  (rfl)

/-- When every arrow of an étale topological groupoid is ineffective, the source map is a
homeomorphism from the total arrows of the effective quotient to its object space, with inverse the
unit map. -/
def arrowHomeomorphObjectsOfIneffectiveArrowsEqUniv (h : ineffectiveArrows C = univ) :
    Quiver.Total (EffectiveQuotient C) ≃ₜ EffectiveQuotient C where
  toFun := Quiver.Total.left
  invFun y := ⟨y, y, 𝟙 y⟩
  left_inv a := by
    obtain ⟨⟨x, y, f⟩, rfl⟩ := mapTotal_surjective a
    have hf : (⟨x, y, f⟩ : Quiver.Total C) ∈ ineffectiveArrows C := h ▸ mem_univ _
    obtain rfl : x = y := left_eq_right_of_mem_ineffectiveArrows hf
    simp [Prefunctor.mapTotal, (toEffectiveQuotient_map_eq_id_iff hs).mpr hf]
  right_inv _ := rfl
  continuous_toFun := continuous_source
  continuous_invFun := (isTopologicalGroupoid hs).continuous_unit

@[simp]
theorem arrowHomeomorphObjectsOfIneffectiveArrowsEqUniv_apply
    (h : ineffectiveArrows C = univ) (a : Quiver.Total (EffectiveQuotient C)) :
    arrowHomeomorphObjectsOfIneffectiveArrowsEqUniv hs h a = a.left :=
  (rfl)

@[simp]
theorem arrowHomeomorphObjectsOfIneffectiveArrowsEqUniv_symm_apply
    (h : ineffectiveArrows C = univ) (y : EffectiveQuotient C) :
    (arrowHomeomorphObjectsOfIneffectiveArrowsEqUniv hs h).symm y = ⟨y, y, 𝟙 y⟩ :=
  (rfl)

end PurelyIneffective

end EffectiveQuotient

end TauCeti

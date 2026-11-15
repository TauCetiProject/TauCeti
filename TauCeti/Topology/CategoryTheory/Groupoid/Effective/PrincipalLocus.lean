/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.Groupoid.Effective.Topology

import TauCeti.Topology.CategoryTheory.ActionGroupoid.Effective
import TauCeti.Topology.CategoryTheory.IsomorphismClasses

/-!
# The principal locus of a proper étale groupoid

At an object `x` of an étale topological groupoid `C`, the isotropy group of the effective quotient
is `Aut x ⧸ ineffectiveKernel hs x` (`TauCeti.quotientIneffectiveKernelMulEquivAut`). An object lies
in the *principal locus* when this effective isotropy is trivial, equivalently when
`ineffectiveKernel hs x = ⊤`: every automorphism of `x` induces the identity germ near `x`. When
every ineffective kernel is trivial, this simply means `Subsingleton (Aut x)`.

Because `TauCeti.map_autMulEquivOfIso_ineffectiveKernel` transports ineffective kernels along
isomorphisms, the principal locus is saturated for isomorphism and descends to the coarse space
`Quotient (isIsomorphicSetoid C)`.

When the arrow space of `C` is Hausdorff and the source-target map is proper, every object admits a
local action chart `Aut x ⋉ U ⥤ C` (`TauCeti.exists_isotropy_action_of_proper_source_target`) in
which `ineffectiveKernel hs y = ⊤` corresponds to `stabilizer (Aut x) y = germKernel (Aut x) y`
(`TauCeti.ineffectiveKernel_eq_top_iff_stabilizer_eq_germKernel`). Since `Aut x` is finite,
`TauCeti.MulAction.isOpen_setOf_stabilizer_eq_germKernel` and
`TauCeti.MulAction.dense_setOf_stabilizer_eq_germKernel` show that the principal locus is open and
dense in `C`, in `EffectiveQuotient C`, and in the coarse space, without any smoothness or
finite-dimensionality hypothesis.

## Main results

* `TauCeti.subsingleton_aut_toEffectiveQuotient_iff`: `Aut ((toEffectiveQuotient C).obj x)` is a
  subsingleton if and only if `ineffectiveKernel hs x = ⊤`.
* `TauCeti.isOpen_setOf_ineffectiveKernel_eq_top` and
  `TauCeti.dense_setOf_ineffectiveKernel_eq_top`: in a proper étale topological groupoid with
  Hausdorff arrow space, `{x : C | ineffectiveKernel hs x = ⊤}` is open and dense.
* `TauCeti.isOpen_image_setOf_ineffectiveKernel_eq_top` and
  `TauCeti.dense_image_setOf_ineffectiveKernel_eq_top`: its image in the coarse space is open and
  dense.
* `TauCeti.EffectiveQuotient.isOpen_setOf_subsingleton_aut` and
  `TauCeti.EffectiveQuotient.dense_setOf_subsingleton_aut`: the objects of `EffectiveQuotient C`
  with trivial isotropy form a dense open set; so do those of `C` itself when every ineffective
  kernel is trivial (`TauCeti.isOpen_setOf_subsingleton_aut_of_ineffectiveKernel_eq_bot`,
  `TauCeti.dense_setOf_subsingleton_aut_of_ineffectiveKernel_eq_bot`).

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public section

open CategoryTheory Set Topology

namespace TauCeti

variable {C : Type*} [Groupoid C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  [IsTopologicalGroupoid C]

section Etale

variable (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))

/-- Whether the ineffective kernel exhausts the isotropy group depends only on the isomorphism
class of the object. -/
theorem ineffectiveKernel_eq_top_iff_of_iso {x y : C} (e : x ≅ y) :
    ineffectiveKernel hs x = ⊤ ↔ ineffectiveKernel hs y = ⊤ := by
  rw [Subgroup.eq_top_iff', Subgroup.eq_top_iff',
    (Aut.autMulEquivOfIso e).surjective.forall]
  exact forall_congr' fun _ ↦ (autMulEquivOfIso_mem_ineffectiveKernel_iff hs e).symm

/-- An object has trivial isotropy in the effective quotient precisely when its ineffective kernel
is the whole isotropy group `Aut x`. -/
theorem subsingleton_aut_toEffectiveQuotient_iff (x : C) :
    Subsingleton (Aut ((toEffectiveQuotient C).obj x)) ↔ ineffectiveKernel hs x = ⊤ := by
  rw [← (quotientIneffectiveKernelMulEquivAut hs x).toEquiv.subsingleton_congr,
    QuotientGroup.subsingleton_iff]

/-- Under the projection to the effective quotient, the objects with trivial effective isotropy pull
back to the objects whose ineffective kernel is all of `Aut x`. -/
theorem EffectiveQuotient.preimage_setOf_subsingleton_aut :
    (toEffectiveQuotient C).obj ⁻¹' {y : EffectiveQuotient C | Subsingleton (Aut y)} =
      {x : C | ineffectiveKernel hs x = ⊤} :=
  ext fun x ↦ subsingleton_aut_toEffectiveQuotient_iff hs x

/-- At an object with trivial ineffective kernel, `Aut x` is a subsingleton precisely when the
ineffective kernel is `⊤`. -/
theorem subsingleton_aut_iff_ineffectiveKernel_eq_top_of_eq_bot {x : C}
    (hx : ineffectiveKernel hs x = ⊥) :
    Subsingleton (Aut x) ↔ ineffectiveKernel hs x = ⊤ := by
  rw [hx, Subgroup.eq_top_iff']
  refine ⟨fun _ g ↦ Subgroup.mem_bot.mpr (Subsingleton.elim g 1), fun h ↦ ⟨fun a b ↦ ?_⟩⟩
  exact (Subgroup.mem_bot.mp (h a)).trans (Subgroup.mem_bot.mp (h b)).symm

/-- The locus `{x : C | ineffectiveKernel hs x = ⊤}` is saturated with respect to isomorphism. -/
theorem preimage_isomorphismClassesMk_image_setOf_ineffectiveKernel_eq_top :
    _root_.Quotient.mk (isIsomorphicSetoid C) ⁻¹'
      (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x : C | ineffectiveKernel hs x = ⊤}) =
      {x : C | ineffectiveKernel hs x = ⊤} := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨x, hx, rfl⟩⟩
  rintro ⟨y, hy, hxy⟩
  obtain ⟨f⟩ := isomorphismClassesMk_eq_iff.mp hxy
  exact (ineffectiveKernel_eq_top_iff_of_iso hs (asIso f)).mp hy

end Etale

section ProperEtale

variable [T2Space (Quiver.Total C)]
  (hp : IsProperMap (fun a : Quiver.Total C ↦ (a.left, a.right)))
  (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))

include hp

/-- Around any object `x` of a Hausdorff proper étale topological groupoid, there is an open
neighbourhood `U` on which `{z : C | ineffectiveKernel hs z = ⊤}` is open and dense. -/
private theorem exists_open_nhds_principalLocus (x : C) :
    ∃ U : Set C, IsOpen U ∧ x ∈ U ∧
      IsOpen (U ∩ {z : C | ineffectiveKernel hs z = ⊤}) ∧
      ∀ V : Set C, IsOpen V → x ∈ V → (V ∩ {z : C | ineffectiveKernel hs z = ⊤}).Nonempty := by
  have ht : IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C) :=
    (IsTopologicalGroupoid.isLocalHomeomorph_source_iff_target C).mp hs
  have : T2Space C := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
  have := finite_aut_of_proper_source_target hp hs x
  obtain ⟨U, hxU, act, F, hUo, hcont, hobj, hFull, hFaithful, hσ, -⟩ :=
    exists_isotropy_action_of_proper_source_target hp hs ht
      IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp x
  let : MulAction (Aut x) U := act
  have : ContinuousConstSMul (Aut x) U := ⟨hcont⟩
  have hpre : (Subtype.val : U → C) ⁻¹' {z : C | ineffectiveKernel hs z = ⊤} =
      {y : U | MulAction.stabilizer (Aut x) y = TauCeti.MulAction.germKernel (Aut x) y} :=
    ext fun y ↦
      ineffectiveKernel_eq_top_iff_stabilizer_eq_germKernel hs Subtype.val_injective hobj hσ y
  refine ⟨U, hUo, hxU, ?_, fun V hVo hxV ↦ ?_⟩
  · have himg : (Subtype.val : U → C) ''
        {y : U | MulAction.stabilizer (Aut x) y = TauCeti.MulAction.germKernel (Aut x) y} =
        U ∩ {z : C | ineffectiveKernel hs z = ⊤} := by
      rw [← hpre, Subtype.image_preimage_coe]
    rw [← himg]
    exact hUo.isOpenEmbedding_subtypeVal.isOpenMap _
      (TauCeti.MulAction.isOpen_setOf_stabilizer_eq_germKernel (G := Aut x) (X := U))
  · obtain ⟨y, hyV, hyS⟩ := dense_iff_inter_open.mp
      (TauCeti.MulAction.dense_setOf_stabilizer_eq_germKernel (G := Aut x) (X := U))
      ((Subtype.val : U → C) ⁻¹' V) (hVo.preimage continuous_subtype_val) ⟨⟨x, hxU⟩, hxV⟩
    exact ⟨y, hyV, by rwa [← mem_preimage, hpre]⟩

/-- **Openness of the principal locus.** In a proper étale topological groupoid with Hausdorff
arrow space, the objects whose ineffective kernel exhausts `Aut x` form an open set. -/
theorem isOpen_setOf_ineffectiveKernel_eq_top :
    IsOpen {x : C | ineffectiveKernel hs x = ⊤} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, -, hxU, hUo, -⟩ := exists_open_nhds_principalLocus hp hs x
  exact ⟨U ∩ {z : C | ineffectiveKernel hs z = ⊤}, inter_subset_right, hUo, hxU, hx⟩

/-- **Density of the principal locus.** In a proper étale topological groupoid with Hausdorff arrow
space, the objects whose ineffective kernel exhausts `Aut x` form a dense set. -/
theorem dense_setOf_ineffectiveKernel_eq_top :
    Dense {x : C | ineffectiveKernel hs x = ⊤} := by
  rw [dense_iff_inter_open]
  rintro V hVo ⟨x, hxV⟩
  obtain ⟨_, -, -, -, hdense⟩ := exists_open_nhds_principalLocus hp hs x
  exact hdense V hVo hxV

/-- In a proper étale topological groupoid with Hausdorff arrow space, the image of the principal
locus in the coarse space is open. -/
theorem isOpen_image_setOf_ineffectiveKernel_eq_top :
    IsOpen (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x : C | ineffectiveKernel hs x = ⊤}) :=
  (isOpenQuotientMap_isomorphismClassesMk hs.continuous
    ((IsTopologicalGroupoid.isLocalHomeomorph_source_iff_target C).mp hs).isOpenMap).isOpenMap _
      (isOpen_setOf_ineffectiveKernel_eq_top hp hs)

/-- In a proper étale topological groupoid with Hausdorff arrow space, the image of the principal
locus in the coarse space is dense. -/
theorem dense_image_setOf_ineffectiveKernel_eq_top :
    Dense (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x : C | ineffectiveKernel hs x = ⊤}) :=
  (Quotient.mk''_surjective (s₁ := isIsomorphicSetoid C)).denseRange.dense_image
    continuous_quotient_mk' (dense_setOf_ineffectiveKernel_eq_top hp hs)

include hs in
/-- In the effective quotient of a proper étale topological groupoid with Hausdorff arrow space,
the objects with trivial isotropy form an open set. -/
theorem EffectiveQuotient.isOpen_setOf_subsingleton_aut :
    IsOpen {y : EffectiveQuotient C | Subsingleton (Aut y)} := by
  rw [← (isHomeomorph_toEffectiveQuotient_obj (C := C)).isQuotientMap.isOpen_preimage,
    EffectiveQuotient.preimage_setOf_subsingleton_aut hs]
  exact isOpen_setOf_ineffectiveKernel_eq_top hp hs

include hs in
/-- In the effective quotient of a proper étale topological groupoid with Hausdorff arrow space,
the objects with trivial isotropy form a dense set. -/
theorem EffectiveQuotient.dense_setOf_subsingleton_aut :
    Dense {y : EffectiveQuotient C | Subsingleton (Aut y)} := by
  have himg : (toEffectiveQuotient C).obj '' {x : C | ineffectiveKernel hs x = ⊤} =
      {y : EffectiveQuotient C | Subsingleton (Aut y)} := by
    rw [← EffectiveQuotient.preimage_setOf_subsingleton_aut hs,
      (isHomeomorph_toEffectiveQuotient_obj (C := C)).surjective.image_preimage]
  rw [← himg]
  exact (isHomeomorph_toEffectiveQuotient_obj (C := C)).surjective.denseRange.dense_image
    (isHomeomorph_toEffectiveQuotient_obj (C := C)).continuous
    (dense_setOf_ineffectiveKernel_eq_top hp hs)

/-- In an effective proper étale topological groupoid with Hausdorff arrow space, the objects with
trivial isotropy form an open set. -/
theorem isOpen_setOf_subsingleton_aut_of_ineffectiveKernel_eq_bot
    (heff : ∀ x : C, ineffectiveKernel hs x = ⊥) :
    IsOpen {x : C | Subsingleton (Aut x)} := by
  have heq : {x : C | Subsingleton (Aut x)} = {x : C | ineffectiveKernel hs x = ⊤} :=
    ext fun x ↦ subsingleton_aut_iff_ineffectiveKernel_eq_top_of_eq_bot hs (heff x)
  rw [heq]
  exact isOpen_setOf_ineffectiveKernel_eq_top hp hs

/-- In an effective proper étale topological groupoid with Hausdorff arrow space, the objects with
trivial isotropy form a dense set. -/
theorem dense_setOf_subsingleton_aut_of_ineffectiveKernel_eq_bot
    (heff : ∀ x : C, ineffectiveKernel hs x = ⊥) :
    Dense {x : C | Subsingleton (Aut x)} := by
  have heq : {x : C | Subsingleton (Aut x)} = {x : C | ineffectiveKernel hs x = ⊤} :=
    ext fun x ↦ subsingleton_aut_iff_ineffectiveKernel_eq_top_of_eq_bot hs (heff x)
  rw [heq]
  exact dense_setOf_ineffectiveKernel_eq_top hp hs

end ProperEtale

end TauCeti

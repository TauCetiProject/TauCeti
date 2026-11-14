/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.ActionGroupoid.Effective
public import TauCeti.Topology.CategoryTheory.Groupoid.Effective.Topology
public import TauCeti.Topology.CategoryTheory.IsomorphismClasses

/-!
# The principal stratum of a proper étale groupoid

An object `x` of an étale topological groupoid `C` lies in the *principal stratum* when its
effective isotropy is trivial, that is, when every automorphism of `x` induces the identity germ
(`ineffectiveKernel hs x = ⊤`). Equivalently, its image in the effective quotient has trivial
automorphism group (`TauCeti.ineffectiveKernel_eq_top_iff_subsingleton_aut`). When `C` is already
effective (`ineffectiveKernel hs x = ⊥` for all `x`), this simply means `Subsingleton (Aut x)`.

For a Hausdorff proper étale topological groupoid, the principal stratum is open and dense in the
object space (`TauCeti.isOpen_setOf_ineffectiveKernel_eq_top`,
`TauCeti.dense_setOf_ineffectiveKernel_eq_top`), and its image in the coarse space is open and
dense (`TauCeti.isOpen_image_setOf_ineffectiveKernel_eq_top`,
`TauCeti.dense_image_setOf_ineffectiveKernel_eq_top`). Passing to `TauCeti.EffectiveQuotient C`
turns this locus into the open dense set of objects with trivial automorphism group
(`TauCeti.EffectiveQuotient.isOpen_setOf_subsingleton_aut`,
`TauCeti.EffectiveQuotient.dense_setOf_subsingleton_aut`).

No manifold structure is needed: openness and density hold purely topologically for any Hausdorff
proper étale topological groupoid, without assuming smooth charts or closedness of ineffective
arrows.

## Main results

* `TauCeti.ineffectiveKernel_eq_top_iff_subsingleton_aut`: `ineffectiveKernel hs x = ⊤` if and only
  if `Aut ((toEffectiveQuotient C).obj x)` is a subsingleton.
* `TauCeti.isOpen_setOf_ineffectiveKernel_eq_top` and
  `TauCeti.dense_setOf_ineffectiveKernel_eq_top`: the principal objects form a dense open subset in
  any Hausdorff proper étale topological groupoid.
* `TauCeti.isOpen_image_setOf_ineffectiveKernel_eq_top` and
  `TauCeti.dense_image_setOf_ineffectiveKernel_eq_top`: the principal coarse stratum is open and
  dense in the coarse space.
* `TauCeti.isOpen_setOf_subsingleton_aut` and `TauCeti.dense_setOf_subsingleton_aut`: when every
  ineffective kernel is trivial, the objects with trivial automorphism group form a dense open set.
* `TauCeti.EffectiveQuotient.isOpen_setOf_subsingleton_aut` and
  `TauCeti.EffectiveQuotient.dense_setOf_subsingleton_aut`: in the effective quotient of a
  Hausdorff proper étale topological groupoid, the objects with trivial automorphism group form a
  dense open set, and so does their image in the coarse space.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Chapter 1.
-/

public section

open CategoryTheory Set Topology

namespace TauCeti

variable {C : Type*} [Groupoid C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  [IsTopologicalGroupoid C] (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))

/-- Being a principal object is invariant under isomorphism. -/
theorem ineffectiveKernel_eq_top_iff_of_iso {x y : C} (e : x ≅ y) :
    ineffectiveKernel hs x = ⊤ ↔ ineffectiveKernel hs y = ⊤ := by
  simp only [Subgroup.eq_top_iff', ← autMulEquivOfIso_mem_ineffectiveKernel_iff hs e]
  exact (Aut.autMulEquivOfIso e).surjective.forall.symm

/-- An object has every automorphism ineffective if and only if its image in the effective quotient
has trivial automorphism group. -/
theorem ineffectiveKernel_eq_top_iff_subsingleton_aut {x : C} :
    ineffectiveKernel hs x = ⊤ ↔ Subsingleton (Aut ((toEffectiveQuotient C).obj x)) :=
  QuotientGroup.subsingleton_iff.symm.trans
    (quotientIneffectiveKernelMulEquivAut hs x).toEquiv.subsingleton_congr

/-- Under the object bijection with the effective quotient, the objects with trivial automorphism
group pull back to the objects whose ineffective kernel is the whole isotropy group. -/
theorem preimage_setOf_subsingleton_aut :
    (toEffectiveQuotient C).obj ⁻¹' {y : EffectiveQuotient C | Subsingleton (Aut y)} =
      {x : C | ineffectiveKernel hs x = ⊤} := by
  ext x
  exact (ineffectiveKernel_eq_top_iff_subsingleton_aut hs).symm

/-- Under `EffectiveQuotient.objHomeomorph`, the principal objects map onto the objects of the
effective quotient with trivial automorphism group. -/
theorem image_objHomeomorph_setOf_ineffectiveKernel_eq_top :
    EffectiveQuotient.objHomeomorph C '' {x : C | ineffectiveKernel hs x = ⊤} =
      {y : EffectiveQuotient C | Subsingleton (Aut y)} := by
  rw [Homeomorph.image_eq_preimage_symm]
  ext y
  simpa using (ineffectiveKernel_eq_top_iff_subsingleton_aut hs
    (x := (EffectiveQuotient.objHomeomorph C).symm y))

/-- The set of principal objects is saturated for isomorphism. -/
theorem isomorphismClasses_preimage_image_setOf_ineffectiveKernel_eq_top :
    _root_.Quotient.mk (isIsomorphicSetoid C) ⁻¹'
      (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x : C | ineffectiveKernel hs x = ⊤}) =
    {x : C | ineffectiveKernel hs x = ⊤} := by
  ext y
  simp only [mem_preimage, mem_image, mem_ofPred_eq]
  refine ⟨fun ⟨x, hx, hxy⟩ ↦ ?_, fun hy ↦ ⟨y, hy, rfl⟩⟩
  obtain ⟨e⟩ := _root_.Quotient.exact hxy
  exact (ineffectiveKernel_eq_top_iff_of_iso hs e).mp hx

/-- When every ineffective kernel is trivial, the objects with trivial automorphism group are
precisely those whose ineffective kernel is the whole isotropy group. -/
theorem setOf_subsingleton_aut_eq_of_ineffectiveKernel_eq_bot
    (hbot : ∀ x : C, ineffectiveKernel hs x = ⊥) :
    {x : C | Subsingleton (Aut x)} = {x : C | ineffectiveKernel hs x = ⊤} := by
  ext x
  simp only [mem_ofPred_eq, hbot x, Subgroup.eq_top_iff', Subgroup.mem_bot,
    subsingleton_iff_forall_eq (1 : Aut x)]

section Proper

variable [T2Space (Quiver.Total C)]
  (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
include hs hp

private theorem exists_isotropy_chart_principal (x : C) :
    ∃ (U : Set C) (_ : x ∈ U), IsOpen U ∧
      IsOpen ((Subtype.val : U → C) ⁻¹' {z : C | ineffectiveKernel hs z = ⊤}) ∧
      Dense ((Subtype.val : U → C) ⁻¹' {z : C | ineffectiveKernel hs z = ⊤}) := by
  have ht : IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C) :=
    (IsTopologicalGroupoid.isLocalHomeomorph_source_iff_target C).mp hs
  obtain ⟨U, hxU, act, F, hUo, hcont, hobj, hfull, hfaith, hopen, -⟩ :=
    exists_isotropy_action_of_proper_source_target hp hs ht
      IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp x
  let : MulAction (Aut x) U := act
  have : ContinuousConstSMul (Aut x) U := ⟨hcont⟩
  have : Finite (Aut x) := finite_aut_of_proper_source_target hp hs x
  have : T2Space C := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
  let := hfull
  let := hfaith
  have hpre : (Subtype.val : U → C) ⁻¹' {z : C | ineffectiveKernel hs z = ⊤} =
      {y : U | MulAction.stabilizer (Aut x) y = MulAction.germKernel (Aut x) y} := by
    ext y
    exact ineffectiveKernel_eq_top_iff_stabilizer_eq_germKernel hs
      Subtype.val_injective hobj hopen y
  refine ⟨U, hxU, hUo, ?_⟩
  rw [hpre]
  exact ⟨MulAction.isOpen_setOf_stabilizer_eq_germKernel,
    MulAction.dense_setOf_stabilizer_eq_germKernel⟩

/-- **Openness of the principal stratum.** In a Hausdorff proper étale topological groupoid, the
objects whose ineffective kernel is the whole isotropy group form an open set. -/
theorem isOpen_setOf_ineffectiveKernel_eq_top :
    IsOpen {x : C | ineffectiveKernel hs x = ⊤} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨U, hxU, hUo, hopen, -⟩ := exists_isotropy_chart_principal hs hp x
  exact ⟨Subtype.val '' ((Subtype.val : U → C) ⁻¹' {z : C | ineffectiveKernel hs z = ⊤}),
    image_preimage_subset _ _, hUo.isOpenMap_subtype_val _ hopen, ⟨x, hxU⟩, hx, rfl⟩

/-- **Density of the principal stratum.** In a Hausdorff proper étale topological groupoid, the
objects whose ineffective kernel is the whole isotropy group form a dense set. -/
theorem dense_setOf_ineffectiveKernel_eq_top :
    Dense {x : C | ineffectiveKernel hs x = ⊤} := by
  refine dense_iff_inter_open.mpr fun V hV ⟨x, hxV⟩ ↦ ?_
  obtain ⟨U, hxU, -, -, hdense⟩ := exists_isotropy_chart_principal hs hp x
  obtain ⟨y, hyV, hyP⟩ := hdense.inter_open_nonempty ((Subtype.val : U → C) ⁻¹' V)
    (hV.preimage continuous_subtype_val) ⟨⟨x, hxU⟩, hxV⟩
  exact ⟨y.1, hyV, hyP⟩

/-- In a Hausdorff proper étale topological groupoid, the coarse image of the principal objects is
open in the space of isomorphism classes. -/
theorem isOpen_image_setOf_ineffectiveKernel_eq_top :
    IsOpen (_root_.Quotient.mk (isIsomorphicSetoid C) ''
      {x : C | ineffectiveKernel hs x = ⊤}) :=
  (isOpenQuotientMap_isomorphismClassesMk hs.continuous
    ((IsTopologicalGroupoid.isOpenMap_source_iff_target C).mp hs.isOpenMap)).isOpenMap _
      (isOpen_setOf_ineffectiveKernel_eq_top hs hp)

/-- In a Hausdorff proper étale topological groupoid, the coarse image of the principal objects is
dense in the space of isomorphism classes. -/
theorem dense_image_setOf_ineffectiveKernel_eq_top :
    Dense (_root_.Quotient.mk (isIsomorphicSetoid C) ''
      {x : C | ineffectiveKernel hs x = ⊤}) :=
  _root_.Quotient.mk_surjective.denseRange.dense_image continuous_quotient_mk'
    (dense_setOf_ineffectiveKernel_eq_top hs hp)

/-- In an effective Hausdorff proper étale topological groupoid, the objects with trivial
automorphism group form an open set. -/
theorem isOpen_setOf_subsingleton_aut (hbot : ∀ x : C, ineffectiveKernel hs x = ⊥) :
    IsOpen {x : C | Subsingleton (Aut x)} := by
  rw [setOf_subsingleton_aut_eq_of_ineffectiveKernel_eq_bot hs hbot]
  exact isOpen_setOf_ineffectiveKernel_eq_top hs hp

/-- In an effective Hausdorff proper étale topological groupoid, the objects with trivial
automorphism group form a dense set. -/
theorem dense_setOf_subsingleton_aut (hbot : ∀ x : C, ineffectiveKernel hs x = ⊥) :
    Dense {x : C | Subsingleton (Aut x)} := by
  rw [setOf_subsingleton_aut_eq_of_ineffectiveKernel_eq_bot hs hbot]
  exact dense_setOf_ineffectiveKernel_eq_top hs hp

/-- In the effective quotient of a Hausdorff proper étale topological groupoid, the objects with
trivial automorphism group form an open set. -/
theorem EffectiveQuotient.isOpen_setOf_subsingleton_aut :
    IsOpen {y : EffectiveQuotient C | Subsingleton (Aut y)} := by
  rw [← image_objHomeomorph_setOf_ineffectiveKernel_eq_top hs]
  exact (EffectiveQuotient.objHomeomorph C).isOpenMap _
    (isOpen_setOf_ineffectiveKernel_eq_top hs hp)

/-- In the effective quotient of a Hausdorff proper étale topological groupoid, the objects with
trivial automorphism group form a dense set. -/
theorem EffectiveQuotient.dense_setOf_subsingleton_aut :
    Dense {y : EffectiveQuotient C | Subsingleton (Aut y)} := by
  rw [← image_objHomeomorph_setOf_ineffectiveKernel_eq_top hs]
  exact (EffectiveQuotient.objHomeomorph C).surjective.denseRange.dense_image
    (EffectiveQuotient.objHomeomorph C).continuous (dense_setOf_ineffectiveKernel_eq_top hs hp)

/-- In the effective quotient of a Hausdorff proper étale topological groupoid, the coarse image of
the objects with trivial automorphism group is open. -/
theorem EffectiveQuotient.isOpen_image_setOf_subsingleton_aut :
    IsOpen (_root_.Quotient.mk (isIsomorphicSetoid (EffectiveQuotient C)) ''
      {y : EffectiveQuotient C | Subsingleton (Aut y)}) := by
  let := EffectiveQuotient.isTopologicalGroupoid hs
  exact (isOpenQuotientMap_isomorphismClassesMk
    (EffectiveQuotient.isLocalHomeomorph_source hs).continuous
    (EffectiveQuotient.isLocalHomeomorph_target hs).isOpenMap).isOpenMap _
      (EffectiveQuotient.isOpen_setOf_subsingleton_aut hs hp)

/-- In the effective quotient of a Hausdorff proper étale topological groupoid, the coarse image of
the objects with trivial automorphism group is dense. -/
theorem EffectiveQuotient.dense_image_setOf_subsingleton_aut :
    Dense (_root_.Quotient.mk (isIsomorphicSetoid (EffectiveQuotient C)) ''
      {y : EffectiveQuotient C | Subsingleton (Aut y)}) :=
  _root_.Quotient.mk_surjective.denseRange.dense_image continuous_quotient_mk'
    (EffectiveQuotient.dense_setOf_subsingleton_aut hs hp)

end Proper

end TauCeti

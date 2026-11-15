/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.Groupoid.Effective.Topology
public import TauCeti.Topology.CategoryTheory.IsomorphismClasses

import TauCeti.Topology.CategoryTheory.ActionGroupoid.Effective
import TauCeti.Topology.CategoryTheory.Etale

/-!
# The principal stratum of a proper étale groupoid

An object `x` of an étale topological groupoid `C` is *principal* when every automorphism of `x`
is ineffective (`TauCeti.ineffectiveKernel hs x = ⊤`), equivalently when its image in the
effective quotient `TauCeti.EffectiveQuotient C` has trivial isotropy
(`Subsingleton (Aut ((TauCeti.toEffectiveQuotient C).obj x))`). Unlike requiring `Aut x` itself to
be trivial, this condition allows global or local ineffective isotropy that acts as the identity on
open neighbourhoods.

For a proper étale topological groupoid:
* When `C` is Hausdorff, `{x : C | ineffectiveKernel hs x = ⊤}` is open: the loops that are *not*
  ineffective form the closed set `{a | a.left = a.right} \ ineffectiveArrows C`, and properness of
  `(source, target)` pushes this closed set forward to a closed set whose pullback along the
  diagonal is the non-principal locus.
* When the total arrow space `Quiver.Total C` is Hausdorff, `{x : C | ineffectiveKernel hs x = ⊤}`
  is dense: near every object `x`, `TauCeti.exists_isotropy_action_of_proper_source_target` exhibits
  an open neighbourhood `U` as a local isotropy chart `Aut x ⋉ U ⥤ C`, on which principal objects
  correspond via `TauCeti.ineffectiveKernel_eq_top_iff_stabilizer_eq_germKernel` to points whose
  stabilizer equals their germ kernel, a dense set by
  `TauCeti.MulAction.dense_setOf_stabilizer_eq_germKernel`.

Since `ineffectiveKernel hs x = ⊤` is invariant under isomorphism, the principal locus descends to
an open dense subset of the coarse space `Quotient (isIsomorphicSetoid C)`, and corresponds under
`TauCeti.EffectiveQuotient.objHomeomorph` to the open dense locus of objects in
`EffectiveQuotient C` with trivial isotropy.

## Main results

* `TauCeti.ineffectiveKernel_eq_top_iff_of_iso`: being principal is invariant under isomorphism.
* `TauCeti.subsingleton_aut_toEffectiveQuotient_obj_iff`: an object of `C` has trivial isotropy in
  `EffectiveQuotient C` if and only if its ineffective kernel is all of `Aut x`.
* `TauCeti.isOpen_setOf_ineffectiveKernel_eq_top`,
  `TauCeti.dense_setOf_ineffectiveKernel_eq_top`: the principal objects form an open dense subset
  of `C`.
* `TauCeti.isOpen_image_isomorphismClassesMk_setOf_ineffectiveKernel_eq_top`,
  `TauCeti.dense_image_isomorphismClassesMk_setOf_ineffectiveKernel_eq_top`: their isomorphism
  classes form an open dense subset of the coarse space.
* `TauCeti.EffectiveQuotient.isOpen_setOf_subsingleton_aut`,
  `TauCeti.EffectiveQuotient.dense_setOf_subsingleton_aut`: the objects of `EffectiveQuotient C`
  with trivial isotropy form an open dense subset, with open dense image in the coarse space.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public section

open CategoryTheory Set Topology

namespace TauCeti

variable {C : Type*} [Groupoid C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  [IsTopologicalGroupoid C]
  (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))

include hs

/-- Whether every automorphism of an object is ineffective depends only on its isomorphism class. -/
theorem ineffectiveKernel_eq_top_iff_of_iso {x y : C} (e : x ≅ y) :
    ineffectiveKernel hs x = ⊤ ↔ ineffectiveKernel hs y = ⊤ := by
  rw [Subgroup.eq_top_iff', Subgroup.eq_top_iff', (Aut.autMulEquivOfIso e).surjective.forall]
  exact forall_congr' fun _ ↦ (autMulEquivOfIso_mem_ineffectiveKernel_iff hs e).symm

/-- An object has trivial isotropy in the effective quotient if and only if every automorphism of
that object in `C` is ineffective. -/
theorem subsingleton_aut_toEffectiveQuotient_obj_iff (x : C) :
    Subsingleton (Aut ((toEffectiveQuotient C).obj x)) ↔ ineffectiveKernel hs x = ⊤ :=
  (quotientIneffectiveKernelMulEquivAut hs x).toEquiv.subsingleton_congr.symm.trans
    QuotientGroup.subsingleton_iff

/-- **Openness of the principal locus.** In an étale topological groupoid with Hausdorff object
space and proper source-target map, the objects whose automorphisms are all ineffective form an
open set. -/
theorem isOpen_setOf_ineffectiveKernel_eq_top [T2Space C]
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right)) :
    IsOpen {x : C | ineffectiveKernel hs x = ⊤} := by
  let S : Set (Quiver.Total C) := {a | a.left = a.right} \ ineffectiveArrows C
  have hS : IsClosed S :=
    (isClosed_eq IsTopologicalGroupoid.continuous_source
      IsTopologicalGroupoid.continuous_target).sdiff isOpen_ineffectiveArrows
  have hcompl : {x : C | ineffectiveKernel hs x = ⊤}ᶜ =
      (fun x : C ↦ (x, x)) ⁻¹' ((fun a : Quiver.Total C ↦ (a.left, a.right)) '' S) := by
    ext x
    simp only [mem_compl_iff, mem_ofPred_eq, Subgroup.eq_top_iff', not_forall, mem_preimage,
      mem_image, S, mem_sdiff, mem_ineffectiveKernel]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨⟨x, x, g.asIso.hom⟩, ⟨rfl, hg⟩, rfl⟩
    · rintro ⟨⟨a₁, a₂, f⟩, ⟨_, hf⟩, hpair⟩
      have ha₁ : a₁ = x := congrArg Prod.fst hpair
      have ha₂ : a₂ = x := congrArg Prod.snd hpair
      subst a₁ a₂
      exact ⟨Aut.of (asIso f), hf⟩
  rw [← isClosed_compl_iff, hcompl]
  exact (hp.isClosedMap S hS).preimage (continuous_id.prodMk continuous_id)

/-- **Density of the principal locus.** In an étale topological groupoid with Hausdorff total arrow
space and proper source-target map, the objects whose automorphisms are all ineffective form a
dense set. -/
theorem dense_setOf_ineffectiveKernel_eq_top [T2Space (Quiver.Total C)]
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right)) :
    Dense {x : C | ineffectiveKernel hs x = ⊤} := by
  let _ : T2Space C := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
  have ht : IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C) :=
    (IsTopologicalGroupoid.isLocalHomeomorph_source_iff_target C).mp hs
  refine dense_iff_inter_open.mpr fun V hVo ⟨x, hxV⟩ ↦ ?_
  obtain ⟨U, hxU, hact, F, _, hcont, hobj, hFull, hFaith, hσ, _⟩ :=
    exists_isotropy_action_of_proper_source_target hp hs ht
      IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp x
  let _ : MulAction (Aut x) U := hact
  let _ : ContinuousConstSMul (Aut x) U := ⟨hcont⟩
  let _ : Finite (Aut x) := finite_aut_of_proper_source_target hp hs x
  have hd :
      Dense {y : U | MulAction.stabilizer (Aut x) y = TauCeti.MulAction.germKernel (Aut x) y} :=
    TauCeti.MulAction.dense_setOf_stabilizer_eq_germKernel
  obtain ⟨y, hyV, hy⟩ := hd.inter_open_nonempty ((Subtype.val : U → C) ⁻¹' V)
    (hVo.preimage continuous_subtype_val) ⟨⟨x, hxU⟩, hxV⟩
  exact ⟨y.1, hyV, (ineffectiveKernel_eq_top_iff_stabilizer_eq_germKernel hs
    Subtype.val_injective hobj hσ y).mpr hy⟩

/-- The principal locus is saturated with respect to isomorphism classes. -/
theorem preimage_image_isomorphismClassesMk_setOf_ineffectiveKernel_eq_top :
    _root_.Quotient.mk (isIsomorphicSetoid C) ⁻¹'
      (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x : C | ineffectiveKernel hs x = ⊤}) =
      {x : C | ineffectiveKernel hs x = ⊤} := by
  ext y
  simp only [mem_preimage, mem_image, mem_ofPred_eq]
  refine ⟨fun ⟨x, hx, hxy⟩ ↦ ?_, fun hy ↦ ⟨y, hy, rfl⟩⟩
  obtain ⟨f⟩ := isomorphismClassesMk_eq_iff.mp hxy
  exact (ineffectiveKernel_eq_top_iff_of_iso hs (asIso f)).mp hx

/-- In an étale topological groupoid with Hausdorff object space and proper source-target map, the
image of the principal locus in the coarse space is open. -/
theorem isOpen_image_isomorphismClassesMk_setOf_ineffectiveKernel_eq_top [T2Space C]
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right)) :
    IsOpen (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x : C | ineffectiveKernel hs x = ⊤}) :=
  (isOpenQuotientMap_isomorphismClassesMk IsTopologicalGroupoid.continuous_source
    ((IsTopologicalGroupoid.isLocalHomeomorph_source_iff_target C).mp hs).isOpenMap).isOpenMap _
    (isOpen_setOf_ineffectiveKernel_eq_top hs hp)

/-- In an étale topological groupoid with Hausdorff total arrow space and proper source-target map,
the image of the principal locus in the coarse space is dense. -/
theorem dense_image_isomorphismClassesMk_setOf_ineffectiveKernel_eq_top [T2Space (Quiver.Total C)]
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right)) :
    Dense (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x : C | ineffectiveKernel hs x = ⊤}) :=
  isQuotientMap_quotient_mk'.surjective.denseRange.dense_image continuous_quotient_mk'
    (dense_setOf_ineffectiveKernel_eq_top hs hp)

namespace EffectiveQuotient

/-- An object of `EffectiveQuotient C` has trivial isotropy if and only if its preimage in `C` has
all automorphisms ineffective. -/
theorem subsingleton_aut_iff (y : EffectiveQuotient C) :
    Subsingleton (Aut y) ↔ ineffectiveKernel hs ((objEquiv C).symm y) = ⊤ := by
  conv_lhs => rw [← toEffectiveQuotient_obj_objEquiv_symm y]
  exact subsingleton_aut_toEffectiveQuotient_obj_iff hs ((objEquiv C).symm y)

/-- Under `EffectiveQuotient.objHomeomorph`, the principal objects of `C` correspond to the objects
of `EffectiveQuotient C` with trivial isotropy. -/
theorem preimage_objHomeomorph_setOf_subsingleton_aut :
    objHomeomorph C ⁻¹' {y : EffectiveQuotient C | Subsingleton (Aut y)} =
      {x : C | ineffectiveKernel hs x = ⊤} := by
  ext x
  simpa only [mem_preimage, mem_ofPred_eq, objHomeomorph_apply] using
    subsingleton_aut_toEffectiveQuotient_obj_iff hs x

/-- In the effective quotient of an étale topological groupoid with Hausdorff object space and
proper source-target map, the objects with trivial isotropy form an open set. -/
theorem isOpen_setOf_subsingleton_aut [T2Space C]
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right)) :
    IsOpen {y : EffectiveQuotient C | Subsingleton (Aut y)} := by
  rw [← (objHomeomorph C).isQuotientMap.isOpen_preimage,
    preimage_objHomeomorph_setOf_subsingleton_aut hs]
  exact isOpen_setOf_ineffectiveKernel_eq_top hs hp

/-- In the effective quotient of an étale topological groupoid with Hausdorff total arrow space and
proper source-target map, the objects with trivial isotropy form a dense set. -/
theorem dense_setOf_subsingleton_aut [T2Space (Quiver.Total C)]
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right)) :
    Dense {y : EffectiveQuotient C | Subsingleton (Aut y)} := by
  have himg : objHomeomorph C '' {x : C | ineffectiveKernel hs x = ⊤} =
      {y : EffectiveQuotient C | Subsingleton (Aut y)} := by
    rw [← preimage_objHomeomorph_setOf_subsingleton_aut hs,
      (objHomeomorph C).surjective.image_preimage]
  rw [← himg]
  exact (objHomeomorph C).surjective.denseRange.dense_image (objHomeomorph C).continuous
    (dense_setOf_ineffectiveKernel_eq_top hs hp)

/-- In the effective quotient of an étale topological groupoid with Hausdorff object space and
proper source-target map, the isomorphism classes of objects with trivial isotropy form an open
subset of the coarse space. -/
theorem isOpen_image_isomorphismClassesMk_setOf_subsingleton_aut [T2Space C]
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right)) :
    IsOpen (_root_.Quotient.mk (isIsomorphicSetoid (EffectiveQuotient C)) ''
      {y : EffectiveQuotient C | Subsingleton (Aut y)}) :=
  (isOpenQuotientMap_isomorphismClassesMk continuous_source
    (isLocalHomeomorph_target hs).isOpenMap).isOpenMap _
    (isOpen_setOf_subsingleton_aut hs hp)

/-- In the effective quotient of an étale topological groupoid with Hausdorff total arrow space and
proper source-target map, the isomorphism classes of objects with trivial isotropy form a dense
subset of the coarse space. -/
theorem dense_image_isomorphismClassesMk_setOf_subsingleton_aut [T2Space (Quiver.Total C)]
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right)) :
    Dense (_root_.Quotient.mk (isIsomorphicSetoid (EffectiveQuotient C)) ''
      {y : EffectiveQuotient C | Subsingleton (Aut y)}) :=
  isQuotientMap_quotient_mk'.surjective.denseRange.dense_image continuous_quotient_mk'
    (dense_setOf_subsingleton_aut hs hp)

end EffectiveQuotient

end TauCeti

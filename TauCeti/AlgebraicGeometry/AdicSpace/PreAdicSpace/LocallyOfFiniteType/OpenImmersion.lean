/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyOfFiniteType.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Complete

/-!
# Open immersions are locally of finite type

An open immersion with adic source is locally of finite type. An affinoid neighbourhood
of a source point is identified with its open image in the target. Present both by the
same complete Hausdorff Huber pair: the local ring map is then the identity, which has
a finite-type presentation with no variables. In particular, the identity of every
adic space is locally of finite type.

This gives the open-subspace morphisms used in refining local finite-type charts.
The target need not itself be adic: the affinoid charts of the source supply the
required charts on its open image.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definitions 8.42 and 8.48.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti.PreAdicSpace

open Huber ValuationSpectrum

universe u

variable {X Y : PreAdicSpace.{u}}

/-- An open immersion with adic source is locally of finite type. Its local presentations
use the identity of a complete Hausdorff affinoid chart, so the target may be any pre-adic
space. -/
theorem locallyOfFiniteType_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f]
    (hX : isAdic X) : LocallyOfFiniteType f := by
  rw [locallyOfFiniteType_iff]
  intro x
  obtain ⟨U, hU, hx⟩ := hX.isLocallyAffinoid x
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨e⟩⟩ :=
    (isAffinoid_iff_exists_complete _).mp hU
  let V : Opens Y := f.isOpenEmbedding.isOpenMap.functor.obj U
  have hr : Set.range (X.ofRestrict U.isOpenEmbedding ≫ f).base =
      Set.range (Y.ofRestrict V.isOpenEmbedding).base := by
    ext y
    constructor
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact ⟨⟨f.base z, z, hz, rfl⟩, rfl⟩
    · rintro ⟨⟨_, z, hz, rfl⟩, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  let e' := IsOpenImmersion.isoOfRangeEq
    (X.ofRestrict U.isOpenEmbedding ≫ f) (Y.ofRestrict V.isOpenEmbedding) hr
  have hs : isSheafy (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
    ObjectProperty.prop_of_iso isSheafy e (isSheafy_restrict U.isOpenEmbedding hX.isSheafy)
  have hs' := (isSheafy_presentationLimitPreAdicSpace_iff P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hP).mp hs
  refine ⟨U, hx, V, fun z hz ↦ ⟨z, hz, rfl⟩, A, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, A, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, Pair.Hom.id S,
    Pair.Hom.isTopologicallyFiniteType_id S, hs', e, e'.symm ≪≫ e, ?_⟩
  simp only [Pair.Hom.toRingHom_id, presentationLimitPreAdicSpaceComap_id]
  simp only [Iso.trans_inv, Iso.symm_inv, Category.id_comp, Category.assoc, Iso.hom_inv_id_assoc]
  exact (IsOpenImmersion.isoOfRangeEq_hom_comp _ _ hr).symm

/-- The identity of every adic space is locally of finite type. -/
theorem locallyOfFiniteType_id (hX : isAdic X) : LocallyOfFiniteType (𝟙 X) :=
  locallyOfFiniteType_of_isOpenImmersion (𝟙 X) hX

end TauCeti.PreAdicSpace

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TwistedE6.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.Assembly

/-!
# The character map of the represented ²E₆ Steinberg endomorphism

On the full-weight torus of the doubled minuscule E₆ carrier, the independently defined graph
and Frobenius maps induce precisely the native root-datum character maps. Their composite
therefore has character pullback `ValidLieTypeIndex.datumSteinberg.weightMap`. The torus
coordinates use the index's own Bourbaki-numbered fundamental weights.

This compares endomorphisms and character lattices on the represented carrier; it does not
identify that carrier with a canonical Chevalley–Demazure group.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* The indexed comparison follows
  `TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.CharacterMap`.
-/

public section

namespace TauCeti.TypeTwistedE6LieIndex

noncomputable section

variable (d : TypeTwistedE6LieIndex)

/-- Frobenius raises each fundamental-weight torus coordinate to the recorded field order. -/
@[simp]
theorem frobenius_weightTorus (s : Fin d.1.rank → d.1.Closureˣ) :
    d.frobenius (d.weightTorus s) = d.weightTorus (s ^ d.1.fieldOrder) := by
  rw [frobenius_def, weightTorus_apply, E6DoubledMinuscule.frobenius_weightTorusPoints,
    weightTorus_apply, d.1.fieldOrder_eq_characteristic_pow]
  -- Reindexing by `finCongr` commutes definitionally with pointwise powers.
  rfl

/-- The graph automorphism relabels torus coordinates by the inverse diagram permutation. -/
@[simp]
theorem graphAut_weightTorus (s : Fin d.1.rank → d.1.Closureˣ) :
    d.graphAut (d.weightTorus s) =
      d.weightTorus (fun i => s (d.toGraphTwistedIndex.diagramPerm.symm i)) := by
  obtain ⟨q, rfl⟩ := d.exists_eq_of
  rw [graphAut_def]
  -- The constructor's semireducible rank requires `erw` to apply the explicit torus equation.
  erw [weightTorus_of,
    E6DoubledMinuscule.graphAutomorphismPoints_weightTorusPoints,
    weightTorus_of, GraphTwistedIndex.diagramPerm_twistedE6, graphPermE6_symm]
  rfl

/-- Frobenius pulls characters back by multiplication by the recorded field order. -/
theorem isCharacterMap_frobenius :
    IsCharacterMap d.weightTorus d.frobenius ((d.1.fieldOrder : ℕ) • 1) := by
  refine isCharacterMap_iff.mpr fun s => ?_
  rw [frobenius_weightTorus, torusPointMap_nsmul, torusPointMap_one,
    MonoidHom.pow_apply, MonoidHom.id_apply]

/-- The graph factor has the inverse native datum graph action as character pullback. -/
theorem isCharacterMap_graphAut :
    IsCharacterMap d.weightTorus d.graphAut.toMonoidHom
      d.toGraphTwistedIndex.datumGraphAut⁻¹.toHom.weightMap := by
  refine isCharacterMap_iff.mpr fun s => ?_
  rw [MulEquiv.coe_toMonoidHom, graphAut_weightTorus,
    GraphTwistedIndex.datumGraphAut_def, DynkinType.diagramAut_inv_weightMap,
    torusPointMap_funCongrLeft]

/-- The represented Steinberg map pulls characters back by the uniform native datum map. -/
theorem isCharacterMap_steinberg :
    IsCharacterMap d.weightTorus d.steinberg d.1.datumSteinberg.weightMap := by
  have h := d.isCharacterMap_graphAut.comp d.isCharacterMap_frobenius
  rw [smul_mul_assoc, one_mul] at h
  rw [steinberg_def, d.1.datumSteinberg_of_not_usesHalfFrobenius d.toGraphTwistedIndex.2,
    GraphTwistedIndex.datumSteinberg_weightMap, LinearMap.comp_smul, LinearMap.comp_id]
  exact h

/-- The Steinberg action on torus coordinates: inverse diagram permutation and field power. -/
@[simp]
theorem steinberg_weightTorus (s : Fin d.1.rank → d.1.Closureˣ) :
    d.steinberg (d.weightTorus s) =
      d.weightTorus (fun i => s (d.toGraphTwistedIndex.diagramPerm.symm i) ^ d.1.fieldOrder) := by
  rw [steinberg_def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    frobenius_weightTorus, graphAut_weightTorus]
  -- Applying a pointwise power at a permuted coordinate is definitionally the displayed power.
  rfl

end

end TauCeti.TypeTwistedE6LieIndex

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.Assembly
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TrialityD4.Basic

/-!
# The character pullback of the triality Steinberg map

For a validated `³D₄(q)` index, the Steinberg map on the tripled carrier has character pullback
`ValidLieTypeIndex.datumSteinberg.weightMap`. The torus is parametrized in the index's own
Bourbaki-numbered fundamental-weight coordinates, not in a second set of coordinates on a spin
carrier. Its graph factor pulls characters back by the inverse native diagram action, while
its Frobenius factor multiplies them by the recorded field order `q`.

This supplies the represented torus computation for comparison with independently constructed
canonical point maps. It asserts neither such a carrier comparison nor finiteness or simplicity
of the fixed-point candidate.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, §11.
* The point maps are those of `TauCeti.TypeTrialityD4LieIndex`; the character maps are those of
  `TauCeti.GraphTwistedIndex.datumGraphAut` and `TauCeti.ValidLieTypeIndex.datumSteinberg`.
-/

public section

namespace TauCeti.TypeTrialityD4LieIndex

noncomputable section

variable (d : TypeTrialityD4LieIndex)

/-- The fundamental-weight torus of the tripled carrier, in the index's Bourbaki coordinates. -/
def weightTorus : (Fin d.1.rank → d.1.Closureˣ) →* d.AmbientGroup :=
  (D4Tripled.weightTorusPoints d.1.Closure).comp
    (MulEquiv.arrowCongr (finCongr d.rank_eq_four) (MulEquiv.refl d.1.Closureˣ)).toMonoidHom

/-- The indexed torus is the native tripled-carrier torus after the rank-four coordinate cast. -/
theorem weightTorus_apply (s : Fin d.1.rank → d.1.Closureˣ) :
    d.weightTorus s = D4Tripled.weightTorusPoints d.1.Closure
      (fun i => s (finCongr d.rank_eq_four.symm i)) :=
  (rfl)

/-- Triality relabels the torus parameters by the inverse native diagram permutation. -/
@[simp]
theorem graphAut_weightTorus (s : Fin d.1.rank → d.1.Closureˣ) :
    d.graphAut (d.weightTorus s) = d.weightTorus
      (fun i => s (d.toTypeDDiagramLieIndex.toGraphTwistedIndex.diagramPerm.symm i)) := by
  obtain ⟨q, rfl⟩ := d.exists_eq_of
  have hperm : (of q).toTypeDDiagramLieIndex.toGraphTwistedIndex.diagramPerm =
      trialityPermD4 :=
    GraphTwistedIndex.diagramPerm_trialityD4 (LieTypeIndex.valid_trialityD4 q)
  rw [graphAut_def, weightTorus_apply, D4Tripled.trialityPoints_weightTorusPoints,
    weightTorus_apply, hperm]
  -- On the constructor the rank is literally four, so both coordinate casts are identities.
  rfl

/-- Frobenius raises each fundamental-weight torus parameter to the recorded field order. -/
@[simp]
theorem frobenius_weightTorus (s : Fin d.1.rank → d.1.Closureˣ) :
    d.frobenius (d.weightTorus s) = d.weightTorus (s ^ d.1.fieldOrder) := by
  rw [frobenius_def, weightTorus_apply, D4Tripled.frobenius_weightTorusPoints,
    weightTorus_apply, d.1.fieldOrder_eq_characteristic_pow]
  -- Coordinate reindexing commutes with pointwise powers.
  rfl

/-- The character pullback of the graph factor is the inverse root-datum diagram action. -/
theorem isCharacterMap_graphAut :
    IsCharacterMap d.weightTorus d.graphAut.toMonoidHom
      d.toTypeDDiagramLieIndex.toGraphTwistedIndex.datumGraphAut⁻¹.toHom.weightMap := by
  apply isCharacterMap_iff.mpr
  intro s
  rw [GraphTwistedIndex.datumGraphAut_def, DynkinType.diagramAut_inv_weightMap,
    torusPointMap_funCongrLeft]
  exact d.graphAut_weightTorus s

/-- The root-datum Frobenius is the character pullback of the represented Frobenius. -/
theorem isCharacterMap_frobenius :
    IsCharacterMap d.weightTorus d.frobenius d.1.datumFrobenius.weightMap := by
  apply isCharacterMap_iff.mpr
  intro s
  rw [ValidLieTypeIndex.datumFrobenius_weightMap, ← Module.End.one_eq_id,
    torusPointMap_nsmul, torusPointMap_one, MonoidHom.pow_apply, MonoidHom.id_apply]
  exact d.frobenius_weightTorus s

/-- The independently defined Steinberg map of the tripled carrier has exactly the character
pullback of the native uniform root-datum Steinberg map, with the contravariant orientation. -/
theorem isCharacterMap_steinberg :
    IsCharacterMap d.weightTorus d.steinberg d.1.datumSteinberg.weightMap := by
  rw [ValidLieTypeIndex.datumSteinberg_of_not_usesHalfFrobenius
    d.1 d.toTypeDDiagramLieIndex.toGraphTwistedIndex.2,
    GraphTwistedIndex.datumSteinberg_weightMap, LinearMap.comp_smul, LinearMap.comp_id,
    steinberg_def]
  simpa only [ValidLieTypeIndex.datumFrobenius_weightMap, ← Module.End.one_eq_id,
    smul_mul_assoc, one_mul] using
    d.isCharacterMap_graphAut.comp d.isCharacterMap_frobenius

end

end TauCeti.TypeTrialityD4LieIndex

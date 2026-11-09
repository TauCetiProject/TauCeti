/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.Assembly

/-!
# The type-A Steinberg maps and their root-datum character pullbacks

For both validated type-A families, the represented Steinberg map acts on the full-weight
standard carrier's torus through the weight map of the native root-datum Steinberg isogeny.
The untwisted family has pullback `q • id`; the unitary family has `q` times the inverse diagram
action. Here the chosen diagram permutation is an involution, but the statement retains the
inverse required by contravariance.

`TypeALieIndex.weightTorus` uses the carrier's fundamental-weight coordinates, without changing
its torus parametrization. The graph and Frobenius character equations are proved separately,
and `TypeALieIndex.isCharacterMap_steinberg` combines them by contravariant composition. These
are computations on the represented carrier, not an identification with canonical points.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti.TypeALieIndex

/-- The split weight torus of the represented type-A ambient group, in fundamental-weight
coordinates. -/
noncomputable def weightTorus (d : TypeALieIndex) :
    (Fin d.1.rank → d.1.Closureˣ) →* d.AmbientGroup :=
  SlStd.weightTorusPoints d.1.rank d.1.Closure

/-- The indexed torus is the standard carrier's weight torus, with unchanged coordinates. -/
theorem weightTorus_def (d : TypeALieIndex) :
    d.weightTorus = SlStd.weightTorusPoints d.1.rank d.1.Closure := (rfl)

/-- The character pullback of the indexed Frobenius agrees with the native datum Frobenius. -/
theorem isCharacterMap_frobenius (d : TypeALieIndex) :
    IsCharacterMap d.weightTorus d.frobenius d.1.datumFrobenius.weightMap := by
  rw [weightTorus_def, frobenius_def, ValidLieTypeIndex.datumFrobenius_weightMap,
    d.1.fieldOrder_eq_characteristic_pow, ← Module.End.one_eq_id]
  exact SlStd.isCharacterMap_frobenius _ _ _ _

/-- The character pullback of the indexed graph automorphism is the inverse native datum
symmetry, with the orientation appropriate to pullback. -/
theorem isCharacterMap_graphAut (d : TypeALieIndex) :
    IsCharacterMap d.weightTorus d.graphAut.toMonoidHom
      d.toGraphTwistedIndex.datumGraphAut⁻¹.toHom.weightMap := by
  rw [GraphTwistedIndex.datumGraphAut_def, DynkinType.diagramAut_inv_weightMap,
    weightTorus_def]
  rcases d.exists_eq_ofA_or_exists_eq_ofTwistedA with
    ⟨rank, q, hvalid, rfl⟩ | ⟨rank, q, hvalid, rfl⟩
  · rw [graphAut_ofA, GraphTwistedIndex.diagramPerm_A, Equiv.Perm.one_def,
      LinearEquiv.funCongrLeft_id, LinearEquiv.refl_toLinearMap, isCharacterMap_iff]
    intro s
    rw [torusPointMap_id]
    rfl
  · rw [graphAut_ofTwistedA, GraphTwistedIndex.diagramPerm_twistedA]
    -- The constructor's rank is definitionally `rank`; reducing the dependent node type
    -- makes the carrier's nondependent reversal formula applicable.
    change IsCharacterMap
      (SlStd.weightTorusPoints rank (ofTwistedA rank q hvalid).1.Closure)
      (SlStd.graphAutomorphismPoints rank (ofTwistedA rank q hvalid).1.Closure).toMonoidHom
      (LinearEquiv.funCongrLeft ℤ ℤ (graphPermA rank)).toLinearMap
    have hperm : graphPermA rank = Fin.revPerm := Equiv.ext (graphPermA_apply rank)
    rw [hperm]
    exact SlStd.isCharacterMap_graphAutomorphismPoints _ _

/-- The represented type-A Steinberg endomorphism has exactly the native root-datum Steinberg
weight map as a character pullback, on both the linear and unitary families. -/
theorem isCharacterMap_steinberg (d : TypeALieIndex) :
    IsCharacterMap d.weightTorus d.steinberg d.1.datumSteinberg.weightMap := by
  rw [ValidLieTypeIndex.datumSteinberg_of_not_usesHalfFrobenius _
      (LieTypeIndex.not_usesHalfFrobenius_of_isTypeA d.2),
    steinberg_eq_graphAut_comp_frobenius, GraphTwistedIndex.datumSteinberg_weightMap]
  have h := d.isCharacterMap_graphAut.comp d.isCharacterMap_frobenius
  rw [ValidLieTypeIndex.datumFrobenius_weightMap, Module.End.mul_eq_comp] at h
  simpa only [LinearMap.smul_comp, LinearMap.id_comp, LinearMap.comp_smul,
    LinearMap.comp_id] using h

end TauCeti.TypeALieIndex

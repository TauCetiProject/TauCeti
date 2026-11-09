/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.Assembly

/-!
# The type-B Steinberg map on characters

For every valid untwisted type-B index, the represented spin-carrier Steinberg map has character
pullback equal to the weight map of `ValidLieTypeIndex.datumSteinberg`. Both are multiplication
by the recorded field order. The torus is the actual spin weight torus, reindexed by the native
rank equality, not an adjoint torus or an independently chosen parametrization.

This supplies character compatibility of the represented model. It does not construct or
identify a canonical simply connected group scheme, or an equivalence with its points.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* The Geck-carrier comparison in `TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.CharacterMap`.
-/

public section

namespace TauCeti.TypeBLieIndex

noncomputable section

variable (d : TypeBLieIndex)

/-- The full-weight spin torus in the index's fundamental-weight coordinates. The carrier
numbers its nodes by `Fin (carrierRank + 1)`; the index numbers the same nodes by `Fin rank`. -/
def weightTorus : (Fin d.1.rank → d.1.Closureˣ) →* d.AmbientGroup :=
  (TypeBSpinCarrier.weightTorusPoints d.carrierRank d.1.Closure).comp
    (MonoidHom.pi fun j =>
      Pi.evalMonoidHom (fun _ : Fin d.1.rank => d.1.Closureˣ)
        (Fin.cast d.carrierRank_add_one j))

/-- The indexed torus agrees with the carrier torus under the rank identification. -/
-- Not a simp lemma: keep the indexed torus intact for character-map and round-trip equations.
theorem weightTorus_apply (s : Fin d.1.rank → d.1.Closureˣ) :
    d.weightTorus s = TypeBSpinCarrier.weightTorusPoints d.carrierRank d.1.Closure
      (fun j => s (Fin.cast d.carrierRank_add_one j)) :=
  (rfl)

/-- The represented type-B Frobenius has the native root-datum Frobenius as character pullback. -/
theorem isCharacterMap_frobenius :
    IsCharacterMap d.weightTorus d.frobenius d.1.datumFrobenius.weightMap := by
  rw [ValidLieTypeIndex.datumFrobenius_weightMap]
  apply isCharacterMap_iff.mpr
  intro s
  rw [torusPointMap_nsmul, torusPointMap_id, MonoidHom.pow_apply, MonoidHom.id_apply,
    weightTorus_apply, weightTorus_apply, frobenius_def]
  have hpow :
      (fun j => s (Fin.cast d.carrierRank_add_one j)) ^
          (d.1.characteristic ^ d.1.fieldExponent) =
        (fun j => s (Fin.cast d.carrierRank_add_one j) ^
          (d.1.characteristic ^ d.1.fieldExponent)) := by
    ext j
    simp
  simpa only [torusPointMap_nsmul, torusPointMap_one, MonoidHom.pow_apply,
    MonoidHom.id_apply, d.1.fieldOrder_eq_characteristic_pow, hpow, Pi.pow_apply] using
    (TypeBSpinCarrier.isCharacterMap_frobenius d.carrierRank d.1.characteristic
      d.1.fieldExponent d.1.Closure).map_apply
      (fun j => s (Fin.cast d.carrierRank_add_one j))

/-- The represented type-B Steinberg map pulls characters back by the weight map of the uniform
native datum Steinberg map. The family is untwisted, so both maps are the recorded Frobenius. -/
theorem isCharacterMap_steinberg :
    IsCharacterMap d.weightTorus d.steinberg d.1.datumSteinberg.weightMap := by
  rw [steinberg_def,
    (d.1.datumSteinberg_eq_datumFrobenius_iff_of_not_usesHalfFrobenius
      (LieTypeIndex.not_usesHalfFrobenius_of_isTypeB d.2)).mpr d.diagramPerm_eq_one]
  exact d.isCharacterMap_frobenius

end

end TauCeti.TypeBLieIndex

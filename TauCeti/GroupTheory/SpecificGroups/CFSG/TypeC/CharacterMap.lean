/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.Assembly

/-!
# Character pullback of the type-C Steinberg map

The represented type-C ambient group is the full-weight standard symplectic carrier. Its
Steinberg map is entrywise field Frobenius. This file identifies its pullback on characters,
in the fundamental-weight coordinates of the valid index, with the independently defined
`TauCeti.ValidLieTypeIndex.datumSteinberg.weightMap`.

The torus is `TauCeti.TypeCLieIndex.weightTorus`, with the same Bourbaki numbering as the native
root datum. Transport from the carrier's rank parameter changes only the type of the node index,
not the coordinates. The diagram factor is trivial, so the character map is multiplication by
the recorded field order. No comparison with a canonical Chevalley–Demazure carrier, or
finiteness or simplicity of fixed points, is asserted here.

The calculation uses `TauCeti.SpStd.isCharacterMap_frobenius` on the represented carrier,
following the native Geck comparison in
`TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.CharacterMap`.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
-/

public section

namespace TauCeti.TypeCLieIndex

variable (d : TypeCLieIndex)

/-- The native root-datum Frobenius is the character pullback of the represented symplectic
Frobenius, on the full-weight torus in the index's fundamental-weight coordinates. -/
theorem isCharacterMap_frobenius :
    IsCharacterMap d.weightTorus d.frobenius d.1.datumFrobenius.weightMap := by
  rw [ValidLieTypeIndex.datumFrobenius_weightMap, d.1.fieldOrder_eq_characteristic_pow,
    ← Module.End.one_eq_id, isCharacterMap_iff]
  intro s
  rw [weightTorus_apply, frobenius_def,
    (SpStd.isCharacterMap_frobenius d.carrierRank d.1.characteristic
      d.1.fieldExponent d.1.Closure).map_apply]
  simp only [weightTorus_apply, torusPointMap_nsmul, torusPointMap_one,
    MonoidHom.pow_apply, MonoidHom.id_apply, Pi.pow_apply]
  rfl

/-- The character pullback of the represented type-C Steinberg map is the weight map of the
uniform native root-datum Steinberg map. The diagram factor is the identity on this family. -/
theorem isCharacterMap_steinberg :
    IsCharacterMap d.weightTorus d.steinberg d.1.datumSteinberg.weightMap := by
  have h := (d.1.datumSteinberg_eq_datumFrobenius_iff_of_not_usesHalfFrobenius
    (LieTypeIndex.not_usesHalfFrobenius_of_isTypeC d.2)).mpr d.diagramPerm_eq_one
  rw [h, steinberg_def]
  exact d.isCharacterMap_frobenius

end TauCeti.TypeCLieIndex

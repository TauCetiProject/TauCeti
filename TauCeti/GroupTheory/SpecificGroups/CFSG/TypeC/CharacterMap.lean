/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.Assembly
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap

/-!
# Character pullback of the type-C Steinberg map

The standard symplectic carrier uses fundamental-weight coordinates for its torus. On these
coordinates the represented Frobenius raises each parameter to the field order `q`, so its
character pullback is multiplication by `q`. This file identifies that pullback with the
uniform datum Steinberg map for every validated type-C index. This family is untwisted: its
native diagram permutation is the identity, so the datum Steinberg map equals the datum Frobenius.

The torus is `TauCeti.TypeCLieIndex.weightTorus`, using the index's own numbered rank rather than
the predecessor rank parameter of the symplectic carrier. No identification with a canonical
Chevalley–Demazure carrier is asserted here.

## Main results

* `TauCeti.TypeCLieIndex.isCharacterMap_frobenius`: the represented Frobenius has the
  uniform native datum Frobenius map as character map.
* `TauCeti.TypeCLieIndex.isCharacterMap_steinberg`: the represented Steinberg map has the
  uniform native datum Steinberg map as character map.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.

The character-map comparison follows the existing Geck-carrier comparison in
`TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.CharacterMap`, using the standard symplectic
torus and Frobenius equations instead of the adjoint representation.
-/

public section

namespace TauCeti.TypeCLieIndex

variable (d : TypeCLieIndex)

/-- The native root-datum Frobenius is the character pullback of the represented symplectic
Frobenius, on the full-weight torus in the index's fundamental-weight coordinates. -/
theorem isCharacterMap_frobenius :
    IsCharacterMap d.weightTorus d.frobenius d.1.datumFrobenius.weightMap := by
  rw [ValidLieTypeIndex.datumFrobenius_weightMap, isCharacterMap_iff]
  intro s
  simpa only [torusPointMap_nsmul, torusPointMap_id, MonoidHom.pow_apply,
    MonoidHom.id_apply] using d.frobenius_weightTorus s

/-- The uniform native datum Steinberg map is the character pullback of the represented
Steinberg map on the type-C fundamental-weight torus. The diagram factor is trivial on this
untwisted family. -/
theorem isCharacterMap_steinberg :
    IsCharacterMap d.weightTorus d.steinberg d.1.datumSteinberg.weightMap := by
  have hdatum : d.1.datumSteinberg = d.1.datumFrobenius :=
    (d.1.datumSteinberg_eq_datumFrobenius_iff_of_not_usesHalfFrobenius
      d.toGraphTwistedIndex.2).mpr d.diagramPerm_eq_one
  rw [hdatum, ValidLieTypeIndex.datumFrobenius_weightMap, isCharacterMap_iff]
  intro s
  simpa only [torusPointMap_nsmul, torusPointMap_id, MonoidHom.pow_apply,
    MonoidHom.id_apply] using d.steinberg_weightTorus s

end TauCeti.TypeCLieIndex

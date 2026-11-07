/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE7.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.Assembly
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap

/-!
# Character pullback of the E₇ Steinberg map

The 56-dimensional minuscule carrier has the full E₇ weight lattice, rather than only the
root lattice of the adjoint representation. Its Frobenius raises every weight-torus parameter
to the field order `q`, and its character pullback is therefore multiplication by `q`.
This file identifies that pullback with the uniform native datum Steinberg map.

The torus uses the validated index's own numbered fundamental-weight coordinates. No
identification of the represented carrier with an independently constructed canonical group
is asserted. The comparison follows `TauCeti.TypeCLieIndex.isCharacterMap_steinberg`, using
`TauCeti.TypeE7LieIndex.steinberg_weightTorusPoints` on the minuscule carrier.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti.TypeE7LieIndex

noncomputable section

variable (d : TypeE7LieIndex)

/-- The full-weight torus of the minuscule E₇ carrier in the validated index's
Bourbaki-numbered fundamental-weight coordinates. -/
def weightTorus : (Fin d.1.rank → d.1.Closureˣ) →* d.AmbientGroup :=
  (E7Minuscule.weightTorusPoints d.1.Closure).comp
    (MonoidHom.pi fun i : Fin 7 =>
      Pi.evalMonoidHom (fun _ : Fin d.1.rank => d.1.Closureˣ)
        ((finCongr d.rank_eq_seven).symm i))

/-- The indexed torus is the represented torus with unchanged coordinate values. -/
theorem weightTorus_apply (s : Fin d.1.rank → d.1.Closureˣ) :
    d.weightTorus s = E7Minuscule.weightTorusPoints d.1.Closure
      (fun i => s ((finCongr d.rank_eq_seven).symm i)) :=
  (rfl)

/-- The Steinberg map raises every fundamental-weight torus parameter to the field order. -/
@[simp]
theorem steinberg_weightTorus (s : Fin d.1.rank → d.1.Closureˣ) :
    d.steinberg (d.weightTorus s) = d.weightTorus (s ^ d.1.fieldOrder) := by
  rw [weightTorus_apply, steinberg_weightTorusPoints, weightTorus_apply]
  rfl

/-- The uniform datum Steinberg map is the character pullback of the represented
E₇ Steinberg map on its full-weight torus. -/
theorem isCharacterMap_steinberg :
    IsCharacterMap d.weightTorus d.steinberg d.1.datumSteinberg.weightMap := by
  have hdatum : d.1.datumSteinberg = d.1.datumFrobenius :=
    (d.1.datumSteinberg_eq_datumFrobenius_iff_of_not_usesHalfFrobenius
      d.toGraphTwistedIndex.2).mpr d.diagramPerm_toGraphTwistedIndex
  rw [hdatum, ValidLieTypeIndex.datumFrobenius_weightMap, isCharacterMap_iff]
  intro s
  simpa only [torusPointMap_nsmul, torusPointMap_id, MonoidHom.pow_apply,
    MonoidHom.id_apply] using d.steinberg_weightTorus s

end

end TauCeti.TypeE7LieIndex

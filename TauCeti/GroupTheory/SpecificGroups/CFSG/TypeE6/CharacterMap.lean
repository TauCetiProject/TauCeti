/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE6.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.Assembly
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap

/-!
# Character pullback of the untwisted E₆ Steinberg map

The 27-dimensional minuscule carrier has the full E₆ weight lattice. Its Frobenius acts on
its weight torus by raising every parameter to the field order `q`. Consequently the pullback
on characters is multiplication by `q`, agreeing with the native datum Steinberg map.

The torus below uses the validated index's own fundamental-weight coordinates. The rank
identification changes no node. This computes the character action of the represented model;
it does not identify that model with an independently constructed canonical group.

The comparison follows `TauCeti.TypeCLieIndex.isCharacterMap_steinberg`, using
`TauCeti.E6Minuscule.frobenius_weightTorusPoints` on the minuscule carrier.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti.TypeE6LieIndex

noncomputable section

variable (d : TypeE6LieIndex)

/-- The full-weight torus of the minuscule E₆ carrier in the validated index's
Bourbaki-numbered fundamental-weight coordinates. -/
def weightTorus : (Fin d.1.rank → d.1.Closureˣ) →* d.AmbientGroup :=
  (E6Minuscule.weightTorusPoints d.1.Closure).comp
    (MulEquiv.arrowCongr (finCongr d.rank_eq_six) (MulEquiv.refl _)).toMonoidHom

/-- The indexed torus is the represented torus with unchanged coordinate values. -/
theorem weightTorus_apply (s : Fin d.1.rank → d.1.Closureˣ) :
    d.weightTorus s = E6Minuscule.weightTorusPoints d.1.Closure
      (fun i => s ((finCongr d.rank_eq_six).symm i)) :=
  (rfl)

/-- The untwisted Steinberg map raises every fundamental-weight torus parameter to `q`. -/
@[simp]
theorem steinberg_weightTorus (s : Fin d.1.rank → d.1.Closureˣ) :
    d.steinberg (d.weightTorus s) = d.weightTorus (s ^ d.1.fieldOrder) := by
  rw [weightTorus_apply, steinberg_def, E6Minuscule.frobenius_weightTorusPoints,
    weightTorus_apply, d.1.fieldOrder_eq_characteristic_pow]
  simp only [Pi.pow_def]

/-- The uniform datum Steinberg map is the character pullback of the represented
untwisted E₆ Steinberg map on its full-weight torus. -/
theorem isCharacterMap_steinberg :
    IsCharacterMap d.weightTorus d.steinberg d.1.datumSteinberg.weightMap := by
  rw [d.1.datumSteinberg_weightMap_of_diagramPerm_eq_one
    d.toGraphTwistedIndex.2 d.diagramPerm_toGraphTwistedIndex]
  exact IsCharacterMap.of_map_eq_pow d.steinberg_weightTorus

end

end TauCeti.TypeE6LieIndex

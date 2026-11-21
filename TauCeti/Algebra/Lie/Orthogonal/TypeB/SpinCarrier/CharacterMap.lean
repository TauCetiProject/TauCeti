/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Frobenius
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap

/-!
# Frobenius character pullback on the type-B spin carrier

The split spin weight torus uses fundamental-weight coordinates. The entrywise `p ^ k`-power
Frobenius therefore pulls back characters by multiplication by `p ^ k`. This identifies the
character action on the represented carrier without identifying it with a canonical group scheme.
The value ring may be any commutative ring of exponential characteristic `p`.

The computation uses `TypeBSpinCarrier.frobenius_weightTorusPoints` and the split-torus duality
API, following the Geck-carrier calculation in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.CharacterMap`.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti.TypeBSpinCarrier

universe v

/-- Frobenius on the spin carrier pulls back fundamental-weight characters by multiplication
by `p ^ k`, including the identity map when `k = 0`. -/
theorem isCharacterMap_frobenius (n p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p] :
    IsCharacterMap (weightTorusPoints n A) (frobenius n p k A) ((p ^ k : ℕ) • 1) := by
  apply isCharacterMap_iff.mpr
  intro s
  rw [frobenius_weightTorusPoints, torusPointMap_nsmul, torusPointMap_one,
    MonoidHom.pow_apply, MonoidHom.id_apply]

end TauCeti.TypeBSpinCarrier

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Frobenius
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.GraphAutomorphism
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap

/-!
# Character pullbacks on the full-weight type-D spin carrier

The independently constructed fork-exchange automorphism acts on the spin weight torus by
exchanging its final two fundamental-weight coordinates. Its character pullback is therefore
precomposition by the fork exchange. Frobenius pulls characters back by multiplication by its
power `p ^ k`. These computations use the actual spin carrier and its weight torus,
not an identification with another group.

The proofs consume `graphAutPoints_weightTorusPoints` and `frobenius_weightTorusPoints`.
They follow the character-pullback computation for the Geck carrier in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.CharacterMap`, using
contravariance of torus-character evaluation. Both results hold over arbitrary commutative
value rings; only Frobenius requires exponential characteristic.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
-/

public section

namespace TauCeti.TypeDSpinCarrier

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n)

/-- Frobenius on the full-weight spin carrier pulls characters back by `p ^ k`. -/
theorem isCharacterMap_frobenius (p k : ℕ) (A : Type*) [CommRing A] [ExpChar A p] :
    IsCharacterMap (weightTorusPoints n hn A) (frobenius n hn p k A)
      ((p ^ k : ℕ) • (1 : Module.End ℤ (Fin n → ℤ))) := by
  apply isCharacterMap_iff.mpr
  intro s
  rw [frobenius_weightTorusPoints, torusPointMap_nsmul, torusPointMap_one,
    MonoidHom.pow_apply, MonoidHom.id_apply]

/-- The spin carrier's pinned fork exchange pulls characters back by precomposition with
`graphPermD`. This is the inverse diagram action, since the fork exchange is an involution. -/
theorem isCharacterMap_graphAutPoints (A : Type*) [CommRing A] :
    IsCharacterMap (weightTorusPoints n hn A) (graphAutPoints n hn A).toMonoidHom
      (LinearEquiv.funCongrLeft ℤ ℤ (graphPermD n (by omega))).toLinearMap := by
  apply isCharacterMap_iff.mpr
  intro s
  rw [MulEquiv.coe_toMonoidHom, graphAutPoints_weightTorusPoints]
  congr 1
  funext i
  rw [torusPointMap_apply, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply]
  have h := torusCharacter_mulEquivArrowCongr (graphPermD n (by omega)) s (Pi.single i 1)
  simp only [MulEquiv.arrowCongr_apply, MulEquiv.refl_apply, torusCharacter_single,
    zpow_one] at h
  rw [graphPermD_symm] at h
  -- Read the linear precomposition map as composition of the underlying functions.
  convert h using 1
  congr 1

end

end TauCeti.TypeDSpinCarrier

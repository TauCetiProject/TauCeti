/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.QuotientSpecialIsogeny
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Special

/-!
# Character pullback of the short-root F₄ special isogeny

The exceptional endomorphism of the prime-field short-root carrier acts on its weight torus
through the weight map of `DynkinType.f4SpecialIsogeny`. The torus parameters are fundamental-
weight coordinates: their image is `(s₃², s₂², s₁, s₀)`, rather than the map associated to the
transposed character matrix. This identifies the independently constructed represented
endomorphism with its root-datum character action, and retains that identification for every
iterate, including the odd powers used for Ree groups and the first power used for the Tits
candidate.

The carrier calculation is `specialIsogeny_weightTorusPoints`; the lattice calculation is
`DynkinType.torusCharacter_f4SpecialIsogenyTorusMap`. Neither a comparison with a canonical
simply connected group scheme nor a finiteness or simplicity result is asserted here.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 14.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

noncomputable section

-- The universal represented-quotient torus calculation is supplied in universe zero.
variable (A : Type) [CommRing A] [Algebra (ZMod 2) A]

/-- The special root-datum isogeny's weight map is the character pullback of the represented
exceptional endomorphism, over every commutative algebra over the prime field. -/
theorem isCharacterMap_specialIsogeny :
    IsCharacterMap (weightTorusPoints A) (specialIsogeny A) f4SpecialIsogeny.weightMap := by
  rw [isCharacterMap_iff]
  intro s
  rw [specialIsogeny_weightTorusPoints]
  congr 1
  funext i
  rw [torusPointMap_apply, f4SpecialIsogeny_weightMap]
  simpa only [zpow_one, Matrix.mulVecLin_apply] using
    (torusCharacter_single _ i 1).symm.trans
      (torusCharacter_f4SpecialIsogenyTorusMap s (Pi.single i 1))

/-- Every iterate of the represented exceptional endomorphism has the character map of the
same iterate of the root-datum isogeny. The zeroth iterate gives the identity on both sides. -/
theorem isCharacterMap_specialIsogeny_pow (n : ℕ) :
    IsCharacterMap (weightTorusPoints A)
      -- The endomorphism type selects composition powers, not pointwise powers.
      ((show Monoid.End (points A) from specialIsogeny A) ^ n)
      (f4SpecialIsogeny ^ n).weightMap := by
  rw [RootPairingIsogeny.weightMap_pow]
  induction n with
  | zero =>
    exact isCharacterMap_id (weightTorusPoints A)
  | succ n ih =>
    -- Endomorphism multiplication is composition; character pullback reverses its order.
    rw [pow_succ', pow_succ]
    exact (isCharacterMap_specialIsogeny A).comp ih

end

end TauCeti.F4ShortRoot.PrimeField

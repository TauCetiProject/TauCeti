/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.SpecialIsogeny
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap

/-!
# Character pullback of the short-root G₂ special isogeny

The signed-minor special isogeny on the characteristic-three short-root carrier pulls
characters back by `TauCeti.DynkinType.g2SpecialIsogeny.weightMap`. Its torus action
`(s₀, s₁) ↦ (s₁, s₀³)` uses the same fundamental-weight coordinates as the simply connected
root datum, with the short node first. The character matrix is therefore
`!![0, 3; 1, 0]`, not its transpose.

`isCharacterMap_specialIsogeny_pow` records the pullback for every iterate, including the
odd powers defining the Ree Steinberg maps. These are comparisons on the existing represented
carrier; no identification with a canonical Chevalley–Demazure group is asserted.

The construction uses the torus equation of
`TauCeti.G2ShortRoot.PrimeField.specialIsogeny_weightTorusPoints` and the contravariant
composition and power laws `TauCeti.IsCharacterMap.comp` and `TauCeti.IsCharacterMap.pow`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3 and 13.4.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

noncomputable section

variable (A : Type*) [CommRing A] [Algebra (ZMod 3) A]

/-- The character pullback of the represented special isogeny is the weight map of the
pinned G₂ special root-datum isogeny. This holds over every commutative 𝔽₃-algebra. -/
theorem isCharacterMap_specialIsogeny :
    IsCharacterMap (weightTorusPoints A) (specialIsogeny A)
      DynkinType.g2SpecialIsogeny.weightMap := by
  apply isCharacterMap_iff.mpr
  intro s
  rw [specialIsogeny_weightTorusPoints]
  congr 1
  ext i
  fin_cases i <;>
    simp [torusPointMap_apply, DynkinType.g2SpecialIsogeny_weightMap,
      DynkinType.g2SpecialIsogenyMatrix_def, torusCharacter_def, Fin.prod_univ_two]

/-- Iterating the represented special isogeny pulls characters back by the corresponding
power of the root-datum weight map. In particular, odd powers have the Ree character action. -/
theorem isCharacterMap_specialIsogeny_pow (n : ℕ) :
    IsCharacterMap (weightTorusPoints A)
      (HPow.hPow (α := Monoid.End (points A)) (specialIsogeny A) n)
      (DynkinType.g2SpecialIsogeny.weightMap ^ n) :=
  (isCharacterMap_specialIsogeny A).pow n

end

end TauCeti.G2ShortRoot.PrimeField

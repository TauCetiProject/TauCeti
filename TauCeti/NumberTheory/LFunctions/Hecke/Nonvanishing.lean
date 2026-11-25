/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.UnitaryCancelling
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Cancellation

/-!
# Boundary nonvanishing for ray class character L-functions

Over an arbitrary number field `K` and modulus `𝔪 : Modulus K`, the unitary ideal weights
`χ ↦ χ.toUnitaryIdealWeight` of ray class characters satisfy
`TauCeti.LFunctions.IsUnitaryCharacterFamily`: the trivial character's weight is the indicator of
ideals prime to `𝔪` (hence trivial on its good ideals), multiplication of characters corresponds to
pointwise multiplication of weights, and every imaginary norm twist of every nontrivial character
has partial-sum cancellation (`RayClassCharacter.hasCancellation_normTwist_toUnitaryIdealWeight`).

Consequently every nontrivial ray class character satisfies `TauCeti.LFunctions.UnitaryCancelling`,
and its continued L-function `continuedLFunctionOfWeight χ.toUnitaryIdealWeight` is nonzero on
`Re s ≥ 1` away from `s = 1` in the quadratic case `χ ^ 2 = 1`.

## Main results

* `RayClassCharacter.isUnitaryCharacterFamily_toUnitaryIdealWeight`:
  `toUnitaryIdealWeight` on `RayClassCharacter 𝔪` forms a unitary character family.
* `RayClassCharacter.unitaryCancelling_toUnitaryIdealWeight_iff`:
  `UnitaryCancelling χ.toUnitaryIdealWeight ↔ χ ≠ 1`.
* `RayClassCharacter.continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero`:
  for `χ ≠ 1` and `1 ≤ s.re`, `continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0` whenever
  `χ ^ 2 ≠ 1` or `s ≠ 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
-/

public section

namespace TauCeti.GlobalNumberFields.RayClassCharacter

open TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- Any imaginary norm twist of `χ.toUnitaryIdealWeight` has cancellation if and only if `χ ≠ 1`. -/
@[simp]
theorem hasCancellation_imaginaryNormTwist_toUnitaryIdealWeight_iff {χ : RayClassCharacter 𝔪}
    (t : ℝ) :
    HasCancellation (imaginaryNormTwist χ.toUnitaryIdealWeight t) ↔ χ ≠ 1 := by
  simp [imaginaryNormTwist_def]

/-- **Ray class characters of any modulus `𝔪` form a unitary character family.** -/
theorem isUnitaryCharacterFamily_toUnitaryIdealWeight (𝔪 : Modulus K) :
    IsUnitaryCharacterFamily (toUnitaryIdealWeight (𝔪 := 𝔪)) :=
  IsUnitaryCharacterFamily.of_mul
    (by
      rw [val_toUnitaryIdealWeight, toMultiplicativeIdealWeight_one]
      exact MultiplicativeIdealWeight.isTrivialOnGood_ofBadPrimes 𝔪.support.finite_toSet)
    toUnitaryIdealWeight_mul
    (fun hχ t ↦ (hasCancellation_imaginaryNormTwist_toUnitaryIdealWeight_iff t).mpr hχ)

/-- Every nontrivial ray class character's unitary weight satisfies `UnitaryCancelling`. -/
theorem unitaryCancelling_toUnitaryIdealWeight {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1) :
    UnitaryCancelling χ.toUnitaryIdealWeight :=
  (isUnitaryCharacterFamily_toUnitaryIdealWeight 𝔪).unitaryCancelling hχ

/-- The unitary weight of the trivial ray class character never satisfies `UnitaryCancelling`. -/
theorem not_unitaryCancelling_toUnitaryIdealWeight_one :
    ¬ UnitaryCancelling (1 : RayClassCharacter 𝔪).toUnitaryIdealWeight :=
  (isUnitaryCharacterFamily_toUnitaryIdealWeight 𝔪).not_unitaryCancelling_one

/-- A ray class character's unitary weight satisfies `UnitaryCancelling` if and only if `χ ≠ 1`. -/
@[simp]
theorem unitaryCancelling_toUnitaryIdealWeight_iff {χ : RayClassCharacter 𝔪} :
    UnitaryCancelling χ.toUnitaryIdealWeight ↔ χ ≠ 1 :=
  (isUnitaryCharacterFamily_toUnitaryIdealWeight 𝔪).unitaryCancelling_iff

/-- **Boundary nonvanishing for the continued L-function of a nontrivial ray class character** on
`Re s ≥ 1`, away from `s = 1` in the quadratic case `χ ^ 2 = 1`. -/
theorem continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero {χ : RayClassCharacter 𝔪}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) (hquad : χ ^ 2 ≠ 1 ∨ s ≠ 1) :
    continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0 :=
  (isUnitaryCharacterFamily_toUnitaryIdealWeight 𝔪).continuedLFunctionOfWeight_ne_zero hχ hs hquad

end TauCeti.GlobalNumberFields.RayClassCharacter

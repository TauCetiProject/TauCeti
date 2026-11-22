/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation.Nonvanishing
import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Cancellation

/-!
# Nonvanishing on `Re s ≥ 1` for cancellation-continued ray class L-functions

For a nontrivial ray class character `χ` of a modulus `𝔪` of a number field `K`, the unitary
ideal weight `χ.toUnitaryIdealWeight` has cancellation
(`TauCeti.GlobalNumberFields.RayClassCharacter.hasCancellation_toUnitaryIdealWeight`), so its
continued L-function `TauCeti.continuedLFunctionOfWeight χ.toUnitaryIdealWeight` is holomorphic
on `Re s > 1 - 1 / [K : ℚ]`.

When `[K : ℚ] = 1`, that half-plane is `Re s > 0`, and combining `3-4-1` with Landau's theorem
(`TauCeti.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one` when
`χ ^ 2 = 1`, and `TauCeti.continuedLFunctionOfWeight_ne_zero_of_hasCancellation_sq` when
`χ ^ 2 ≠ 1`) yields unconditional nonvanishing on `Re s ≥ 1`.

## Main results

* `continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re_of_finrank_eq_one`
  (in `TauCeti.GlobalNumberFields.RayClassCharacter`): nonvanishing on `Re s ≥ 1` when `[K : ℚ] = 1`
  and `χ ≠ 1`.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
-/

public section

open NumberField TauCeti
open scoped NumberField

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **Unconditional nonvanishing on `Re s ≥ 1` of the cancellation-continued ray class L-function
when `[K : ℚ] = 1`.** For any nontrivial ray class character `χ ≠ 1` of any modulus `𝔪`,
`continuedLFunctionOfWeight χ.toUnitaryIdealWeight` does not vanish on `Re s ≥ 1`: when
`χ ^ 2 = 1` this follows from Landau's theorem (`[K : ℚ] = 1`), and when `χ ^ 2 ≠ 1` it follows
from `3-4-1` and cancellation for `χ ^ 2`. -/
theorem continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re_of_finrank_eq_one
    (hK : Module.finrank ℚ K = 1) {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) :
    continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0 := by
  by_cases hsq : χ ^ 2 = 1
  · refine continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one hK
      (hasCancellation_toUnitaryIdealWeight hχ) ?_ hs
    rw [UnitaryIdealWeight.val_pow, val_toUnitaryIdealWeight]
    exact χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hsq
  · have hpow : χ.toUnitaryIdealWeight ^ 2 = (χ ^ 2).toUnitaryIdealWeight := by
      rw [sq, sq, toUnitaryIdealWeight_mul]
    exact continuedLFunctionOfWeight_ne_zero_of_hasCancellation_sq
      (hasCancellation_toUnitaryIdealWeight hχ)
      (hpow ▸ hasCancellation_toUnitaryIdealWeight hsq) hs

end TauCeti.GlobalNumberFields.RayClassCharacter

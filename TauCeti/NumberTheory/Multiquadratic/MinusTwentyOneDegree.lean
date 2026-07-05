/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.MinusTwentyOneData
public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantIndependence

/-!
# The degree of the `-21` prime-discriminant radicand field

This file exposes the degree worked example for `ℚ(√-1, √-3, √-7)`.

## Main result

* `TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven`: the
  worked-example degree `[ℚ(i, √-3, √-7) : ℚ] = 8`.
-/

namespace TauCeti.Multiquadratic

public section

/-- **Worked example: `[ℚ(i, √-3, √-7) : ℚ] = 8`.** This is the degree of the
multiquadratic field `ℚ(√-1, √-3, √-7)` attached to the prime discriminants `-4`, `-3`,
and `-7` in the genus-field example for `ℚ(√-21)`. -/
theorem finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven :
    Module.finrank ℚ
      (IntermediateField.adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) :
        IntermediateField ℚ ℂ)
      = 8 := by
  have h := finrank_adjoin_roots_primeDiscriminantRadicands
    negFourNegThreeNegSevenPrimeDiscriminants
    negFourNegThreeNegSevenPrimeDiscriminants_isPrimeDiscriminant
    negFourNegThreeNegSevenPrimeDiscriminants_injective
    negFourNegThreeNegSevenPrimeDiscriminants_not_all_even
    negFourNegThreeNegSevenPrimeDiscriminantRoots
    negFourNegThreeNegSevenPrimeDiscriminantRoots_sq
  rw [← range_negFourNegThreeNegSevenPrimeDiscriminantRoots]
  exact h.trans (by norm_num [Nat.card_fin])

end

end TauCeti.Multiquadratic

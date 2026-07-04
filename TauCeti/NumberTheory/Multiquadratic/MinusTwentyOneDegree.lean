/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantIndependence
public import TauCeti.NumberTheory.Multiquadratic.MinusTwentyOneData

/-!
# The degree of the `-21` prime-discriminant radicand field

The worked examples in the multiquadratic roadmap identify the genus field for `ℚ(√-21)` as
`ℚ(√-1, √-3, √-7)`, attached to the prime discriminants `-4`, `-3`, and `-7`. This file records
the immediate Layer-0 degree consequence needed before the actual genus-field comparison: those
three prime-discriminant radicands are square-class independent, so their multiquadratic
compositum over `ℚ` has degree `8`.

The prime-discriminant convention follows the standard genus-theory convention in Cox's
*Primes of the Form x² + ny²* and Lemmermeyer's *Reciprocity Laws*.

## Main result

* `TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven`: the
  worked-example degree `[ℚ(i, √-3, √-7) : ℚ] = 8`.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

/-- **Worked example: `[ℚ(i, √-3, √-7) : ℚ] = 8`.** This is the degree of the
multiquadratic field `ℚ(√-1, √-3, √-7)` attached to the prime discriminants `-4`, `-3`,
and `-7` in the genus-field example for `ℚ(√-21)`. -/
theorem finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven :
    Module.finrank ℚ
      (adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) :
        IntermediateField ℚ ℂ)
      = 8 := by
  have h := finrank_adjoin_roots_primeDiscriminantRadicands
    negFourNegThreeNegSevenPrimeDiscriminants
    MinusTwentyOne.primeDiscriminants_isPrimeDiscriminant
    MinusTwentyOne.primeDiscriminants_injective
    MinusTwentyOne.primeDiscriminants_not_all_even
    MinusTwentyOne.primeDiscriminantRoot
    MinusTwentyOne.primeDiscriminantRoot_sq
  rw [← MinusTwentyOne.range_primeDiscriminantRoot]
  exact h.trans (by norm_num [Nat.card_fin])

end TauCeti.Multiquadratic

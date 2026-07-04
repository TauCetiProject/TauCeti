/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.MinusTwentyOneData
public import TauCeti.NumberTheory.Multiquadratic.MinusTwentyOneExamples
public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantGaloisGroup

/-!
# The Galois group of the `-21` prime-discriminant radicand field

This file exposes the Galois-cardinality worked example for `ℚ(√-1, √-3, √-7)`.

## Main result

* `TauCeti.Multiquadratic.card_aut_adjoin_I_sqrt_neg_three_sqrt_neg_seven`: the
  worked-example cardinality `|Gal(ℚ(i, √-3, √-7)/ℚ)| = 8`.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

/-- **Worked example: `|Gal(ℚ(i, √-3, √-7)/ℚ)| = 8`.** This is the Galois group of the
multiquadratic field `ℚ(√-1, √-3, √-7)` attached to the prime discriminants `-4`, `-3`,
and `-7` in the genus-field example for `ℚ(√-21)`. -/
theorem card_aut_adjoin_I_sqrt_neg_three_sqrt_neg_seven :
    Nat.card
      ((adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) :
          IntermediateField ℚ ℂ)
          ≃ₐ[ℚ]
        (adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) :
          IntermediateField ℚ ℂ))
      = 8 := by
  let P := MinusTwentyOne.primeDiscriminantPackage
  have h := card_aut_adjoin_roots_primeDiscriminantRadicands
    negFourNegThreeNegSevenPrimeDiscriminants
    P.isPrimeDiscriminant
    P.injective
    P.not_all_even
    P.root
    P.root_sq
  rw [← P.range_root]
  exact h.trans (by norm_num [Nat.card_fin])

end TauCeti.Multiquadratic

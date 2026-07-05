/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantExampleLists
public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantGaloisGroup

/-!
# The Galois group of the `-21` prime-discriminant radicand field

The worked examples in the multiquadratic roadmap identify the genus field for `ℚ(√-21)` as
`ℚ(√-1, √-3, √-7)`, attached to the prime discriminants `-4`, `-3`, and `-7`. This file
records the immediate Layer-0 consequence needed before the
actual genus-field comparison: those three prime-discriminant radicands are square-class
independent, so the Galois group of their multiquadratic compositum over `ℚ` has cardinality
`8`.

The prime-discriminant convention follows the standard genus-theory convention in Cox's
*Primes of the Form x² + ny²* and Lemmermeyer's *Reciprocity Laws*.

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
      ((adjoin ℚ ({Complex.I, sqrtNegNat 3, sqrtNegNat 7} : Set ℂ) :
          IntermediateField ℚ ℂ)
          ≃ₐ[ℚ]
        (adjoin ℚ ({Complex.I, sqrtNegNat 3, sqrtNegNat 7} : Set ℂ) :
          IntermediateField ℚ ℂ))
      = 8 := by
  have h := card_aut_adjoin_roots_primeDiscriminantRadicands
    negFourNegThreeNegSevenPrimeDiscriminants
    isPrimeDiscriminant_negFourNegThreeNegSevenPrimeDiscriminants
    injective_negFourNegThreeNegSevenPrimeDiscriminants
    not_all_even_negFourNegThreeNegSevenPrimeDiscriminants
    (fun i : Fin 3 => ![Complex.I, sqrtNegNat 3, sqrtNegNat 7] i)
    root_neg_four_neg_three_neg_seven_sq
  rw [← range_roots_neg_four_neg_three_neg_seven]
  exact h.trans (by norm_num [Nat.card_fin])

end TauCeti.Multiquadratic

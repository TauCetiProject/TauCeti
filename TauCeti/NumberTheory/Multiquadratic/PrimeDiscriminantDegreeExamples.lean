/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.LegendrePrimeDiscriminantExamples
public import TauCeti.NumberTheory.Multiquadratic.CMField
public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantIndependence

/-!
# Degrees of the first prime-discriminant generator fields

The multiquadratic roadmap's genus-field worked examples use the prime-discriminant generator
lists `[-4, 5]` for `ℚ(√-5)` and `[-4, -3, -7]` for `ℚ(√-21)`. The corresponding radicands are
`[-1, 5]` and `[-1, -3, -7]`, so the proposed genus fields are `ℚ(i, √5)` and
`ℚ(i, √-3, √-7)`.

This file records the immediate Layer-0 degree consequences for those two composita. The actual
class-field-theoretic statements identifying them as genus fields are later roadmap work; here we
only package the already-proved prime-discriminant independence theorem in the two concrete forms
that the worked examples will consume.

The prime-discriminant convention follows Cox's *Primes of the Form x² + ny²* and Lemmermeyer's
*Reciprocity Laws*, as in the prime-discriminant API reused below.

## Main results

* `TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_five`: `[ℚ(i, √5) : ℚ] = 4`.
* `TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven`:
  `[ℚ(i, √-3, √-7) : ℚ] = 8`.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

/-- **Worked example: `[ℚ(i, √5) : ℚ] = 4`.** This is the full-degree Layer-0 input for the
prime-discriminant generator field attached to the `ℚ(√-5)` genus-field example. -/
theorem finrank_adjoin_I_sqrt_five :
    Module.finrank ℚ
      (adjoin ℚ ({Complex.I, ((Real.sqrt 5 : ℝ) : ℂ)} : Set ℂ) : IntermediateField ℚ ℂ) = 4 := by
  have h := finrank_adjoin_I_sqrt_primes ![5] (by decide) (by decide)
  have hset : insert Complex.I
      (Set.range fun i : Fin 1 => ((Real.sqrt ((![5] : Fin 1 → ℕ) i) : ℝ) : ℂ))
      = ({Complex.I, ((Real.sqrt 5 : ℝ) : ℂ)} : Set ℂ) := by
    rw [Set.range_unique]
    simp [Matrix.cons_val_fin_one]
  rw [hset] at h
  rw [h, Nat.card_fin]
  norm_num

/-- **Worked example: `[ℚ(i, √-3, √-7) : ℚ] = 8`.** This is the full-degree Layer-0 input for
the prime-discriminant generator field attached to the `ℚ(√-21)` genus-field example. -/
theorem finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven :
    Module.finrank ℚ
      (adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) : IntermediateField ℚ ℂ) =
        8 := by
  have h := finrank_adjoin_roots_primeDiscriminantRadicands
    negFourNegThreeNegSevenPrimeDiscriminants
    isPrimeDiscriminant_negFourNegThreeNegSevenPrimeDiscriminants
    injective_negFourNegThreeNegSevenPrimeDiscriminants
    not_all_even_negFourNegThreeNegSevenPrimeDiscriminants
    (fun i : Fin 3 => ![Complex.I, sqrtNegThree, sqrtNegSeven] i)
    root_neg_four_neg_three_neg_seven_sq
  rw [range_roots_neg_four_neg_three_neg_seven] at h
  exact h.trans (by norm_num [Nat.card_fin])

end TauCeti.Multiquadratic

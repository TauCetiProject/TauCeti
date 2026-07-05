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

private theorem isPrimeDiscriminant_negFourNegThreeNegSevenPrimeDiscriminants :
    ∀ i : Fin 3, IsPrimeDiscriminant (negFourNegThreeNegSevenPrimeDiscriminants i) := by
  intro i
  fin_cases i
  · simp [negFourNegThreeNegSevenPrimeDiscriminants]
  · have h3 : IsPrimeDiscriminant (oddPrimeDiscriminant 3) :=
      isPrimeDiscriminant_oddPrimeDiscriminant (p := 3) (by decide) (by decide)
    simpa [negFourNegThreeNegSevenPrimeDiscriminants,
      oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h3
  · have h7 : IsPrimeDiscriminant (oddPrimeDiscriminant 7) :=
      isPrimeDiscriminant_oddPrimeDiscriminant (p := 7) (by decide) (by decide)
    simpa [negFourNegThreeNegSevenPrimeDiscriminants,
      oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h7

private theorem injective_negFourNegThreeNegSevenPrimeDiscriminants :
    Function.Injective negFourNegThreeNegSevenPrimeDiscriminants := by
  decide

private theorem not_all_even_negFourNegThreeNegSevenPrimeDiscriminants :
    ¬ ((∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -4) ∧
      (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = 8) ∧
        (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -8)) := by
  decide

private theorem root_neg_four_neg_three_neg_seven_sq (i : Fin 3) :
    (fun i : Fin 3 => ![Complex.I, sqrtNegNat 3, sqrtNegNat 7] i) i ^ 2 =
      algebraMap ℚ ℂ
        (((primeDiscriminantRadicand
          (negFourNegThreeNegSevenPrimeDiscriminants i) : ℤ) : ℚ)) := by
  fin_cases i
  · simp [negFourNegThreeNegSevenPrimeDiscriminants, Complex.I_sq]
  · have hrad : primeDiscriminantRadicand (-3) = -3 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 3) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h
    simp [negFourNegThreeNegSevenPrimeDiscriminants, hrad]
  · have hrad : primeDiscriminantRadicand (-7) = -7 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 7) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h
    simp [negFourNegThreeNegSevenPrimeDiscriminants, hrad]

private theorem range_roots_neg_four_neg_three_neg_seven :
    (Set.range fun i : Fin 3 => ![Complex.I, sqrtNegNat 3, sqrtNegNat 7] i)
      = {Complex.I, sqrtNegNat 3, sqrtNegNat 7} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    rcases hx with hx | hx | hx
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨1, by simp [hx]⟩
    · exact ⟨2, by simp [hx]⟩

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

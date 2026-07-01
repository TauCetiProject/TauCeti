/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantGaloisGroup

/-!
# The Galois group of the `-21` prime-discriminant generator field

The worked examples in the multiquadratic roadmap identify the genus-field generators for
`ℚ(√-21)` as the prime discriminants `-4`, `-3`, and `-7`, giving the field
`ℚ(√-1, √-3, √-7)`. This file records the immediate Layer-0 consequence needed before the
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

/-- The chosen complex square root of `-3`, namely `i√3`. -/
noncomputable abbrev sqrtNegThree : ℂ :=
  Complex.I * ((Real.sqrt 3 : ℝ) : ℂ)

/-- The chosen complex square root of `-7`, namely `i√7`. -/
noncomputable abbrev sqrtNegSeven : ℂ :=
  Complex.I * ((Real.sqrt 7 : ℝ) : ℂ)

/-- The three prime discriminants used for the `ℚ(√-21)` genus-field example. -/
private def minusTwentyOnePrimeDiscriminants : Fin 3 → ℤ :=
  ![(-4 : ℤ), -3, -7]

/-- The complex square root data for the prime discriminants `-4`, `-3`, and `-7`: the
associated radicands are `-1`, `-3`, and `-7`, with roots `i`, `i√3`, and `i√7`. -/
private theorem root_neg_four_neg_three_neg_seven_sq (i : Fin 3) :
    (fun i : Fin 3 => ![Complex.I, sqrtNegThree, sqrtNegSeven] i) i ^ 2 =
      algebraMap ℚ ℂ
        (((primeDiscriminantRadicand (minusTwentyOnePrimeDiscriminants i) : ℤ) : ℚ)) := by
  fin_cases i
  · simp [minusTwentyOnePrimeDiscriminants, Complex.I_sq]
  · have hsqrt : (((Real.sqrt 3 : ℝ) : ℂ) ^ 2) = (3 : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    have hrad : primeDiscriminantRadicand (-3) = -3 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 3) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h
    calc
      sqrtNegThree ^ 2 = Complex.I ^ 2 * (((Real.sqrt 3 : ℝ) : ℂ) ^ 2) := by
        ring
      _ = algebraMap ℚ ℂ
          (((primeDiscriminantRadicand (minusTwentyOnePrimeDiscriminants 1) : ℤ) : ℚ)) := by
        simp [minusTwentyOnePrimeDiscriminants, Complex.I_sq, hsqrt, hrad]
  · have hsqrt : (((Real.sqrt 7 : ℝ) : ℂ) ^ 2) = (7 : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)]
      norm_num
    have hrad : primeDiscriminantRadicand (-7) = -7 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 7) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h
    calc
      sqrtNegSeven ^ 2 = Complex.I ^ 2 * (((Real.sqrt 7 : ℝ) : ℂ) ^ 2) := by
        ring
      _ = algebraMap ℚ ℂ
          (((primeDiscriminantRadicand (minusTwentyOnePrimeDiscriminants 2) : ℤ) : ℚ)) := by
        simp [minusTwentyOnePrimeDiscriminants, Complex.I_sq, hsqrt, hrad]

private theorem isPrimeDiscriminant_minusTwentyOnePrimeDiscriminants :
    ∀ i : Fin 3, IsPrimeDiscriminant (minusTwentyOnePrimeDiscriminants i) := by
  intro i
  fin_cases i
  · simp [minusTwentyOnePrimeDiscriminants]
  · have h3 : IsPrimeDiscriminant (oddPrimeDiscriminant 3) :=
      isPrimeDiscriminant_oddPrimeDiscriminant (p := 3) (by decide) (by decide)
    simpa [minusTwentyOnePrimeDiscriminants,
      oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h3
  · have h7 : IsPrimeDiscriminant (oddPrimeDiscriminant 7) :=
      isPrimeDiscriminant_oddPrimeDiscriminant (p := 7) (by decide) (by decide)
    simpa [minusTwentyOnePrimeDiscriminants,
      oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h7

private theorem injective_minusTwentyOnePrimeDiscriminants :
    Function.Injective minusTwentyOnePrimeDiscriminants := by
  decide

private theorem not_all_even_minusTwentyOnePrimeDiscriminants :
    ¬ ((∃ i : Fin 3, minusTwentyOnePrimeDiscriminants i = -4) ∧
      (∃ i : Fin 3, minusTwentyOnePrimeDiscriminants i = 8) ∧
        (∃ i : Fin 3, minusTwentyOnePrimeDiscriminants i = -8)) := by
  decide

private theorem range_roots_neg_four_neg_three_neg_seven :
    (Set.range fun i : Fin 3 => ![Complex.I, sqrtNegThree, sqrtNegSeven] i)
      = {Complex.I, sqrtNegThree, sqrtNegSeven} := by
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
multiquadratic field generated by the radicands attached to the prime discriminants `-4`,
`-3`, and `-7`, the genus-field generators for `ℚ(√-21)`. -/
theorem card_aut_adjoin_I_sqrt_neg_three_sqrt_neg_seven :
    Nat.card
      ((adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) :
          IntermediateField ℚ ℂ)
          ≃ₐ[ℚ]
        (adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) :
          IntermediateField ℚ ℂ))
      = 8 := by
  have h := card_aut_adjoin_roots_primeDiscriminantRadicands
    minusTwentyOnePrimeDiscriminants isPrimeDiscriminant_minusTwentyOnePrimeDiscriminants
    injective_minusTwentyOnePrimeDiscriminants not_all_even_minusTwentyOnePrimeDiscriminants
    (fun i : Fin 3 => ![Complex.I, sqrtNegThree, sqrtNegSeven] i)
    root_neg_four_neg_three_neg_seven_sq
  rw [← range_roots_neg_four_neg_three_neg_seven]
  exact h.trans (by norm_num [Nat.card_fin])

end TauCeti.Multiquadratic

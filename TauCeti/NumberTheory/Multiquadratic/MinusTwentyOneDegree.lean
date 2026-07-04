/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.LegendrePrimeDiscriminantExamples
public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantIndependence
public import Mathlib.Data.Complex.Basic

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

/-- The complex number `i√n` squares to `-n`. -/
private theorem I_mul_real_sqrt_nat_sq (n : ℕ) :
    (Complex.I * ((Real.sqrt n : ℝ) : ℂ)) ^ 2 = -(n : ℂ) := by
  have hsqrt : (((Real.sqrt n : ℝ) : ℂ) ^ 2) = (n : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_num
  calc
    (Complex.I * ((Real.sqrt n : ℝ) : ℂ)) ^ 2 =
        Complex.I ^ 2 * (((Real.sqrt n : ℝ) : ℂ) ^ 2) := by
      ring
    _ = -(n : ℂ) := by
      simp [Complex.I_sq, hsqrt]

/-- The chosen complex square root of `-3`, namely `i√3`. -/
noncomputable abbrev sqrtNegThree : ℂ :=
  Complex.I * ((Real.sqrt 3 : ℝ) : ℂ)

/-- The chosen root `sqrtNegThree` squares to `-3`. -/
@[simp]
theorem sqrtNegThree_sq : sqrtNegThree ^ 2 = (-3 : ℂ) := by
  simpa [sqrtNegThree] using I_mul_real_sqrt_nat_sq 3

/-- The chosen complex square root of `-7`, namely `i√7`. -/
noncomputable abbrev sqrtNegSeven : ℂ :=
  Complex.I * ((Real.sqrt 7 : ℝ) : ℂ)

/-- The chosen root `sqrtNegSeven` squares to `-7`. -/
@[simp]
theorem sqrtNegSeven_sq : sqrtNegSeven ^ 2 = (-7 : ℂ) := by
  simpa [sqrtNegSeven] using I_mul_real_sqrt_nat_sq 7

namespace MinusTwentyOne

/-- The three prime discriminants used for the `ℚ(√-21)` genus-field example. -/
def primeDiscriminants : Fin 3 → ℤ :=
  negFourNegThreeNegSevenPrimeDiscriminants

/-- The complex square root data for the prime discriminants `-4`, `-3`, and `-7`: the
associated radicands are `-1`, `-3`, and `-7`, with roots `i`, `i√3`, and `i√7`. -/
theorem root_sq (i : Fin 3) :
    (fun i : Fin 3 => ![Complex.I, sqrtNegThree, sqrtNegSeven] i) i ^ 2 =
      algebraMap ℚ ℂ
        (((primeDiscriminantRadicand (primeDiscriminants i) : ℤ) : ℚ)) := by
  fin_cases i
  · simp [primeDiscriminants, Complex.I_sq]
  · have hrad : primeDiscriminantRadicand (-3) = -3 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 3) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h
    simp [primeDiscriminants, hrad]
  · have hrad : primeDiscriminantRadicand (-7) = -7 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 7) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h
    simp [primeDiscriminants, hrad]

/-- Each entry of `MinusTwentyOne.primeDiscriminants` is a prime discriminant. -/
theorem isPrimeDiscriminant :
    ∀ i : Fin 3, IsPrimeDiscriminant (primeDiscriminants i) := by
  intro i
  fin_cases i
  · simp [primeDiscriminants, negFourNegThreeNegSevenPrimeDiscriminants]
  · have h3 : IsPrimeDiscriminant (oddPrimeDiscriminant 3) :=
      isPrimeDiscriminant_oddPrimeDiscriminant (p := 3) (by decide) (by decide)
    simpa [primeDiscriminants, negFourNegThreeNegSevenPrimeDiscriminants,
      oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h3
  · have h7 : IsPrimeDiscriminant (oddPrimeDiscriminant 7) :=
      isPrimeDiscriminant_oddPrimeDiscriminant (p := 7) (by decide) (by decide)
    simpa [primeDiscriminants, negFourNegThreeNegSevenPrimeDiscriminants,
      oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h7

/-- The three prime discriminants for the `-21` example are pairwise distinct. -/
theorem injective :
    Function.Injective primeDiscriminants := by
  decide

/-- The `-21` example does not contain all three even prime discriminants. -/
theorem not_all_even :
    ¬ ((∃ i : Fin 3, primeDiscriminants i = -4) ∧
      (∃ i : Fin 3, primeDiscriminants i = 8) ∧
        (∃ i : Fin 3, primeDiscriminants i = -8)) := by
  decide

/-- The range of the chosen root family is exactly `{i, √-3, √-7}`. -/
theorem range_roots :
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

end MinusTwentyOne

/-- **Worked example: `[ℚ(i, √-3, √-7) : ℚ] = 8`.** This is the degree of the
multiquadratic field `ℚ(√-1, √-3, √-7)` attached to the prime discriminants `-4`, `-3`,
and `-7` in the genus-field example for `ℚ(√-21)`. -/
theorem finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven :
    Module.finrank ℚ
      (adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) :
        IntermediateField ℚ ℂ)
      = 8 := by
  have h := finrank_adjoin_roots_primeDiscriminantRadicands
    MinusTwentyOne.primeDiscriminants MinusTwentyOne.isPrimeDiscriminant
    MinusTwentyOne.injective MinusTwentyOne.not_all_even
    (fun i : Fin 3 => ![Complex.I, sqrtNegThree, sqrtNegSeven] i)
    MinusTwentyOne.root_sq
  rw [← MinusTwentyOne.range_roots]
  exact h.trans (by norm_num [Nat.card_fin])

end TauCeti.Multiquadratic

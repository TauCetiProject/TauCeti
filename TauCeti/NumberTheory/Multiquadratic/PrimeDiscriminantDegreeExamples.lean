/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CMField
public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantIndependence

/-!
# Degree examples for prime-discriminant multiquadratic fields

The worked example in the multiquadratic roadmap names the genus-field generators for
`ℚ(√-21)` as `ℚ(i, √-3, √-7)`. Before the later class-field-theoretic comparison with genus
fields, the Layer-0 multiquadratic theory should record the basic degree fact for this
generator list.

This file packages the `ℚ(i, √-3, √-7)` reading of
`TauCeti.Multiquadratic.finrank_adjoin_roots_primeDiscriminantRadicands`. It uses the
prime-discriminant convention from Cox's *Primes of the Form x² + ny²* and Lemmermeyer's
*Reciprocity Laws*, together with the square-class independence already proved in
`TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantIndependence`.

## Main results

* `TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven`:
  `[ℚ(i, √-3, √-7) : ℚ] = 8`.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

/-- The prime-discriminant list `[-4, -3, -7]` for the `ℚ(√-21)` genus-field generators. -/
abbrev minusTwentyOnePrimeDiscriminants : Fin 3 → ℤ :=
  ![(-4 : ℤ), -3, -7]

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

/-- The complex square root data for the prime discriminants `-4`, `-3`, and `-7`: the
associated radicands are `-1`, `-3`, and `-7`, with roots `i`, `i√3`, and `i√7`. -/
theorem root_neg_four_neg_three_neg_seven_sq (i : Fin 3) :
    (fun i : Fin 3 => ![Complex.I, sqrtNegThree, sqrtNegSeven] i) i ^ 2 =
      algebraMap ℚ ℂ
        (((primeDiscriminantRadicand (minusTwentyOnePrimeDiscriminants i) : ℤ) : ℚ)) := by
  fin_cases i
  · simp [minusTwentyOnePrimeDiscriminants, Complex.I_sq]
  · have hrad : primeDiscriminantRadicand (-3) = -3 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 3) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h
    simp [minusTwentyOnePrimeDiscriminants, hrad]
  · have hrad : primeDiscriminantRadicand (-7) = -7 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 7) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h
    simp [minusTwentyOnePrimeDiscriminants, hrad]

/-- Each member of `minusTwentyOnePrimeDiscriminants` is a prime discriminant. -/
theorem isPrimeDiscriminant_minusTwentyOnePrimeDiscriminants :
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

/-- The list `[-4, -3, -7]` has no repeated prime discriminants. -/
theorem injective_minusTwentyOnePrimeDiscriminants :
    Function.Injective minusTwentyOnePrimeDiscriminants := by
  decide

/-- The list `[-4, -3, -7]` does not contain all three even prime discriminants. -/
theorem not_all_even_minusTwentyOnePrimeDiscriminants :
    ¬ ((∃ i : Fin 3, minusTwentyOnePrimeDiscriminants i = -4) ∧
      (∃ i : Fin 3, minusTwentyOnePrimeDiscriminants i = 8) ∧
        (∃ i : Fin 3, minusTwentyOnePrimeDiscriminants i = -8)) := by
  decide

/-- The range of the chosen `√-21` root family is `{i, √-3, √-7}`. -/
theorem range_roots_neg_four_neg_three_neg_seven :
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

/-- **Worked example: `[ℚ(i, √-3, √-7) : ℚ] = 8`.** This is the Layer-0 degree statement for
the multiquadratic field generated by the prime-discriminant radicands `-1`, `-3`, and `-7`,
the genus-field generator list for `ℚ(√-21)`. -/
theorem finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven :
    Module.finrank ℚ
      (adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) : IntermediateField ℚ ℂ)
      = 8 := by
  have h := finrank_adjoin_roots_primeDiscriminantRadicands minusTwentyOnePrimeDiscriminants
    isPrimeDiscriminant_minusTwentyOnePrimeDiscriminants
    injective_minusTwentyOnePrimeDiscriminants
    not_all_even_minusTwentyOnePrimeDiscriminants
    (fun i : Fin 3 => ![Complex.I, sqrtNegThree, sqrtNegSeven] i)
    root_neg_four_neg_three_neg_seven_sq
  rw [range_roots_neg_four_neg_three_neg_seven] at h
  exact h.trans (by norm_num [Nat.card_fin])

end TauCeti.Multiquadratic

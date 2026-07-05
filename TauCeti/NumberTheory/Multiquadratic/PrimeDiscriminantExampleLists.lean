/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminants
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Complex.Basic

/-!
# Prime-discriminant lists for the first genus-field examples

The multiquadratic roadmap's genus-field worked examples use the prime-discriminant lists
`[-4, 5]` for `ℚ(√-5)` and `[-4, -3, -7]` for `ℚ(√-21)`. This file gives those shared lists
a neutral home for the Legendre-character, degree, and Galois worked examples, together with
the shared witness bundle (prime-discriminant, injectivity, parity, and root-square facts) for
the `[-4, -3, -7]` list reused by the `ℚ(√-21)` degree and Galois examples.
-/

public section

namespace TauCeti.Multiquadratic

/-- The prime-discriminant list `[-4, 5]` for the genus-field generators of `ℚ(√-5)`. -/
abbrev negFourFivePrimeDiscriminants : Fin 2 → ℤ :=
  ![(-4 : ℤ), 5]

/-- The prime-discriminant list `[-4, -3, -7]` for the genus-field generators of
`ℚ(√-21)`. -/
abbrev negFourNegThreeNegSevenPrimeDiscriminants : Fin 3 → ℤ :=
  ![(-4 : ℤ), -3, -7]

/-- The chosen complex square root of `-n`, namely `i√n`. -/
noncomputable abbrev sqrtNegNat (n : ℕ) : ℂ :=
  Complex.I * ((Real.sqrt n : ℝ) : ℂ)

/-- The chosen root `sqrtNegNat n` squares to `-n`. -/
@[simp]
theorem sqrtNegNat_sq (n : ℕ) : sqrtNegNat n ^ 2 = -(n : ℂ) := by
  have hsqrt : (((Real.sqrt n : ℝ) : ℂ) ^ 2) = (n : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_num
  calc
    (Complex.I * ((Real.sqrt n : ℝ) : ℂ)) ^ 2 =
        Complex.I ^ 2 * (((Real.sqrt n : ℝ) : ℂ) ^ 2) := by
      ring
    _ = -(n : ℂ) := by
      simp [Complex.I_sq, hsqrt]

/-- Each entry of the `[-4, -3, -7]` list is a prime discriminant. -/
theorem isPrimeDiscriminant_negFourNegThreeNegSevenPrimeDiscriminants :
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

/-- The `[-4, -3, -7]` list has no repeated entries. -/
theorem injective_negFourNegThreeNegSevenPrimeDiscriminants :
    Function.Injective negFourNegThreeNegSevenPrimeDiscriminants := by
  decide

/-- The `[-4, -3, -7]` list does not contain all three even prime discriminants. -/
theorem not_all_three_evenPrimeDiscriminants_negFourNegThreeNegSevenPrimeDiscriminants :
    ¬ ((∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -4) ∧
      (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = 8) ∧
        (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -8)) := by
  decide

/-- The complex square root data for the prime discriminants `-4`, `-3`, and `-7`: the
associated radicands are `-1`, `-3`, and `-7`, with roots `i`, `i√3`, and `i√7`. -/
theorem root_neg_four_neg_three_neg_seven_sq (i : Fin 3) :
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

/-- The range of the chosen `√-21` root family is `{i, √-3, √-7}`. -/
theorem range_roots_neg_four_neg_three_neg_seven :
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

end TauCeti.Multiquadratic

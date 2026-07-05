/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantExampleLists
public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantIndependence
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Complex.Basic

/-!
# Shared data for the `-21` prime-discriminant radicand examples

The worked examples for `ℚ(√-21)` use the prime-discriminant list `[-4, -3, -7]` and
the corresponding roots `i`, `i√3`, and `i√7` of the radicands `-1`, `-3`, and `-7`.
This file keeps those concrete roots and elementary list facts separate from the degree and
Galois-cardinality consequences, so those examples can share data without depending on each
other.

## Main definitions

* `TauCeti.Multiquadratic.negFourNegThreeNegSevenPrimeDiscriminantRoots`: the concrete root
  vector `[i, √-3, √-7]`.
* `TauCeti.Multiquadratic.negFourNegThreeNegSevenPrimeDiscriminantRoots_sq`: the square of each
  root is the radicand attached to the corresponding prime discriminant.
* `TauCeti.Multiquadratic.not_isSquare_prod_negFourNegThreeNegSevenPrimeDiscriminantRadicands`:
  the packaged square-class-independence fact for the concrete radicands.
-/

public section

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

/-- Each entry of the concrete list `[-4, -3, -7]` is a prime discriminant. -/
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

/-- The concrete list `[-4, -3, -7]` is injective. -/
private theorem negFourNegThreeNegSevenPrimeDiscriminants_injective :
    Function.Injective negFourNegThreeNegSevenPrimeDiscriminants := by
  decide

/-- The concrete list `[-4, -3, -7]` does not contain all three even prime discriminants. -/
private theorem negFourNegThreeNegSevenPrimeDiscriminants_not_all_three_evenPrimeDiscriminants :
    ¬ ((∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -4) ∧
      (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = 8) ∧
        (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -8)) := by
  decide

/-- The concrete roots `[i, √-3, √-7]` for the prime-discriminant list `[-4, -3, -7]`. -/
noncomputable abbrev negFourNegThreeNegSevenPrimeDiscriminantRoots : Fin 3 → ℂ :=
  ![Complex.I, sqrtNegThree, sqrtNegSeven]

/-- Each concrete root squares to the radicand attached to the corresponding prime
discriminant in `[-4, -3, -7]`. -/
theorem negFourNegThreeNegSevenPrimeDiscriminantRoots_sq (i : Fin 3) :
    negFourNegThreeNegSevenPrimeDiscriminantRoots i ^ 2 =
      algebraMap ℚ ℂ
        (((primeDiscriminantRadicand
          (negFourNegThreeNegSevenPrimeDiscriminants i) : ℤ) : ℚ)) := by
  fin_cases i
  · simp [negFourNegThreeNegSevenPrimeDiscriminantRoots,
      negFourNegThreeNegSevenPrimeDiscriminants, Complex.I_sq]
  · have hrad : primeDiscriminantRadicand (-3) = -3 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 3) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h
    simp [negFourNegThreeNegSevenPrimeDiscriminantRoots,
      negFourNegThreeNegSevenPrimeDiscriminants, hrad]
  · have hrad : primeDiscriminantRadicand (-7) = -7 := by
      have h := primeDiscriminantRadicand_oddPrimeDiscriminant (p := 7) (by decide)
      simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h
    simp [negFourNegThreeNegSevenPrimeDiscriminantRoots,
      negFourNegThreeNegSevenPrimeDiscriminants, hrad]

/-- The concrete root vector `[i, √-3, √-7]` has range `{i, √-3, √-7}`. -/
private theorem range_negFourNegThreeNegSevenPrimeDiscriminantRoots :
    Set.range negFourNegThreeNegSevenPrimeDiscriminantRoots =
      {Complex.I, sqrtNegThree, sqrtNegSeven} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i <;> simp [negFourNegThreeNegSevenPrimeDiscriminantRoots]
  · intro hx
    rcases hx with hx | hx | hx
    · exact ⟨0, by simp [negFourNegThreeNegSevenPrimeDiscriminantRoots, hx]⟩
    · exact ⟨1, by simp [negFourNegThreeNegSevenPrimeDiscriminantRoots, hx]⟩
    · exact ⟨2, by simp [negFourNegThreeNegSevenPrimeDiscriminantRoots, hx]⟩

/-- Packaged square-class independence for the radicands `-1`, `-3`, and `-7` attached to
the prime-discriminant list `[-4, -3, -7]`. -/
theorem not_isSquare_prod_negFourNegThreeNegSevenPrimeDiscriminantRadicands :
    ∀ S : Finset (Fin 3), S.Nonempty →
      ¬ IsSquare
        (∏ i ∈ S,
          (((primeDiscriminantRadicand
            (negFourNegThreeNegSevenPrimeDiscriminants i) : ℤ) : ℚ))) := by
  exact not_isSquare_prod_primeDiscriminantRadicands
    negFourNegThreeNegSevenPrimeDiscriminants
    isPrimeDiscriminant_negFourNegThreeNegSevenPrimeDiscriminants
    negFourNegThreeNegSevenPrimeDiscriminants_injective
    negFourNegThreeNegSevenPrimeDiscriminants_not_all_three_evenPrimeDiscriminants

end TauCeti.Multiquadratic

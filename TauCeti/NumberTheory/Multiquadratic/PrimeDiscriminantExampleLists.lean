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
a neutral home for the Legendre-character, degree, and Galois worked examples.
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

/-- Compatibility name for the chosen complex square root of `-3`. -/
noncomputable abbrev sqrtNegThree : ℂ :=
  sqrtNegNat 3

/-- Compatibility name for the chosen complex square root of `-7`. -/
noncomputable abbrev sqrtNegSeven : ℂ :=
  sqrtNegNat 7

/-- The chosen root `sqrtNegThree` squares to `-3`. -/
@[simp]
theorem sqrtNegThree_sq : sqrtNegThree ^ 2 = -(3 : ℂ) :=
  sqrtNegNat_sq 3

/-- The chosen root `sqrtNegSeven` squares to `-7`. -/
@[simp]
theorem sqrtNegSeven_sq : sqrtNegSeven ^ 2 = -(7 : ℂ) :=
  sqrtNegNat_sq 7

end TauCeti.Multiquadratic

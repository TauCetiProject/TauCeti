/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminantExampleLists
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Complex.Basic

/-!
# Shared data for the `-21` prime-discriminant radicand examples

The worked examples for `ℚ(√-21)` use the prime-discriminant list `[-4, -3, -7]` and
the corresponding roots `i`, `i√3`, and `i√7` of the radicands `-1`, `-3`, and `-7`.
This file keeps those concrete roots and elementary list facts separate from the degree and
Galois-cardinality consequences, so those examples can share data without depending on each
other.
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

end TauCeti.Multiquadratic

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Complex conjugation of `2πi`

Complex conjugation negates `2πi`, so it acts on `(2πi)^k` by the sign `(-1)^k`. These are the
signs by which conjugation acts on the Tate twists `(2πi)^k ℝ` inside `ℂ`.
-/

public section

open ComplexConjugate

namespace Complex

/-- Complex conjugation negates `2πi`. -/
theorem conj_two_pi_I : conj (2 * Real.pi * I : ℂ) = -(2 * Real.pi * I) := by
  simp [conj_ofReal, map_ofNat]

/-- Complex conjugation acts on `(2πi)^k` by the sign `(-1)^k`. -/
theorem conj_two_pi_I_pow (k : ℕ) :
    conj ((2 * Real.pi * I : ℂ) ^ k) = (-1) ^ k * (2 * Real.pi * I) ^ k := by
  rw [map_pow, conj_two_pi_I, neg_eq_neg_one_mul, mul_pow]

end Complex

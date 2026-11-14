/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.ConjExponents

/-!
# Hölder exponents and the threshold two

A natural number `n` that has a Hölder conjugate exponent satisfies `2 ≤ n`, since Hölder
conjugate exponents are greater than one (`Real.HolderConjugate.two_le_of_natCast`,
`NNReal.HolderConjugate.two_le_of_natCast`). This is how the dimension bound `2 ≤ n` is read off
the Sobolev exponent `n / (n - 1)` of the Gagliardo–Nirenberg–Sobolev inequality.

The conjugate of an exponent `p > 2` in `ℝ≥0∞` is less than two (`ENNReal.conjExponent_lt_two`):
supercritical exponents in the plane have subcritical conjugates.
-/

public section

open scoped ENNReal NNReal

/-- A natural number with a real Hölder conjugate exponent is at least two. -/
theorem Real.HolderConjugate.two_le_of_natCast {n : ℕ} {q : ℝ}
    (h : (n : ℝ).HolderConjugate q) : 2 ≤ n := by
  exact_mod_cast h.lt

/-- A natural number with a nonnegative real Hölder conjugate exponent is at least two. -/
theorem NNReal.HolderConjugate.two_le_of_natCast {n : ℕ} {q : ℝ≥0}
    (h : (n : ℝ≥0).HolderConjugate q) : 2 ≤ n := by
  exact_mod_cast h.lt

/-- The conjugate exponent of `p > 2` is less than two. -/
theorem ENNReal.conjExponent_lt_two {p : ℝ≥0∞} (hp : 2 < p) : p.conjExponent < 2 := by
  have : p.HolderConjugate p.conjExponent :=
    .conjExponent ((by norm_num : (1 : ℝ≥0∞) ≤ 2).trans hp.le)
  have h := ENNReal.HolderConjugate.inv_add_inv_eq_one p p.conjExponent
  by_contra h2
  have h1 : p⁻¹ < 2⁻¹ := ENNReal.inv_lt_inv.2 hp
  have h3 : p.conjExponent⁻¹ ≤ 2⁻¹ := ENNReal.inv_le_inv.2 (not_lt.1 h2)
  have := ENNReal.add_lt_add_of_lt_of_le (h3.trans_lt (by norm_num)).ne h1 h3
  rw [h, ENNReal.inv_two_add_inv_two] at this
  exact lt_irrefl _ this

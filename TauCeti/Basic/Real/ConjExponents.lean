/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.ConjExponents

/-!
# Lower bounds on Hölder conjugate exponents

Every pair `(p, q)` of Hölder conjugate exponents has `2 ≤ max p q`, since `p, q < 2` would give
`1 = p⁻¹ + q⁻¹ > 2⁻¹ + 2⁻¹ = 1` (`Real.HolderConjugate.two_le_max`,
`NNReal.HolderConjugate.two_le_max`). Equivalently, `2 ≤ max p (p / (p - 1))` for `1 < p < ∞`
(`Real.two_le_max_div_sub_one`, `ENNReal.two_le_max_toReal_div_toReal_sub_one`).

In addition, a natural number `n` that has a Hölder conjugate exponent satisfies `2 ≤ n`, since
Hölder conjugate exponents are greater than one (`Real.HolderConjugate.two_le_of_natCast`,
`NNReal.HolderConjugate.two_le_of_natCast`). This is how the dimension bound `2 ≤ n` is read off
the Sobolev exponent `n / (n - 1)` of the Gagliardo–Nirenberg–Sobolev inequality.
-/

public section

open scoped ENNReal NNReal

/-- At least one of two real Hölder conjugate exponents is at least `2`. -/
theorem Real.HolderConjugate.two_le_max {p q : ℝ} (h : p.HolderConjugate q) : 2 ≤ max p q := by
  by_contra! hpq
  rw [max_lt_iff] at hpq
  have hlt : (2 : ℝ)⁻¹ + 2⁻¹ < p⁻¹ + q⁻¹ :=
    add_lt_add (inv_strictAnti₀ h.pos hpq.1) (inv_strictAnti₀ h.symm.pos hpq.2)
  rw [← one_div, add_halves, h.inv_add_inv_eq_one] at hlt
  exact lt_irrefl 1 hlt

/-- At least one of two nonnegative real Hölder conjugate exponents is at least `2`. -/
theorem NNReal.HolderConjugate.two_le_max {p q : ℝ≥0} (h : p.HolderConjugate q) : 2 ≤ max p q := by
  exact_mod_cast h.coe.two_le_max

/-- For `1 < p`, at least one of `p` and its conjugate exponent `p / (p - 1)` is at least `2`. -/
theorem Real.two_le_max_div_sub_one {p : ℝ} (hp : 1 < p) : 2 ≤ max p (p / (p - 1)) :=
  (Real.HolderConjugate.conjExponent hp).two_le_max

/-- For `1 < p < ∞` in `ℝ≥0∞`, at least one of `p.toReal` and `p.toReal / (p.toReal - 1)` is at
least `2`. -/
theorem ENNReal.two_le_max_toReal_div_toReal_sub_one {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) :
    2 ≤ max p.toReal (p.toReal / (p.toReal - 1)) :=
  Real.two_le_max_div_sub_one (by simpa using ENNReal.toReal_strict_mono hp hp1)

/-- A natural number with a real Hölder conjugate exponent is at least two. -/
theorem Real.HolderConjugate.two_le_of_natCast {n : ℕ} {q : ℝ}
    (h : (n : ℝ).HolderConjugate q) : 2 ≤ n := by
  exact_mod_cast h.lt

/-- A natural number with a nonnegative real Hölder conjugate exponent is at least two. -/
theorem NNReal.HolderConjugate.two_le_of_natCast {n : ℕ} {q : ℝ≥0}
    (h : (n : ℝ≥0).HolderConjugate q) : 2 ≤ n := by
  exact_mod_cast h.lt

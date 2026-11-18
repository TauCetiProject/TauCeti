/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.ConjExponents

/-!
# Hölder conjugate exponents

A natural number `n` that has a Hölder conjugate exponent satisfies `2 ≤ n`, since Hölder
conjugate exponents are greater than one (`Real.HolderConjugate.two_le_of_natCast`,
`NNReal.HolderConjugate.two_le_of_natCast`). This is how the dimension bound `2 ≤ n` is read off
the Sobolev exponent `n / (n - 1)` of the Gagliardo–Nirenberg–Sobolev inequality.

Dually, a supercritical extended exponent `p > 2` has a Hölder conjugate `q < 2`
(`ENNReal.exists_holderConjugate_lt_two`), the exponent condition under which the reciprocal
kernel `1 / z` lies in `L^q` near the origin of the plane.
-/

public section

open scoped NNReal ENNReal

/-- A natural number with a real Hölder conjugate exponent is at least two. -/
theorem Real.HolderConjugate.two_le_of_natCast {n : ℕ} {q : ℝ}
    (h : (n : ℝ).HolderConjugate q) : 2 ≤ n := by
  exact_mod_cast h.lt

/-- A natural number with a nonnegative real Hölder conjugate exponent is at least two. -/
theorem NNReal.HolderConjugate.two_le_of_natCast {n : ℕ} {q : ℝ≥0}
    (h : (n : ℝ≥0).HolderConjugate q) : 2 ≤ n := by
  exact_mod_cast h.lt

/-- A supercritical exponent `p > 2` has a Hölder conjugate `q < 2`, namely `(1 - p⁻¹)⁻¹`. -/
theorem ENNReal.exists_holderConjugate_lt_two {p : ℝ≥0∞} (hp : 2 < p) :
    ∃ q, p.HolderConjugate q ∧ q < 2 := by
  refine ⟨(1 - p⁻¹)⁻¹, HolderConjugate.inv_one_sub_inv' (one_le_two.trans hp.le), ?_⟩
  rw [ENNReal.inv_lt_iff_inv_lt,
    (ENNReal.cancel_of_ne (ENNReal.inv_ne_top.2 (zero_lt_two.trans hp).ne')).lt_tsub_iff_right]
  calc (2 : ℝ≥0∞)⁻¹ + p⁻¹ < 2⁻¹ + 2⁻¹ :=
        ENNReal.add_lt_add_left (by simp) (ENNReal.inv_lt_inv.2 hp)
    _ = 1 := ENNReal.inv_two_add_inv_two

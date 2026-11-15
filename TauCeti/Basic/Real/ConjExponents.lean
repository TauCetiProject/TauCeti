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

Of two Hölder conjugate exponents in `ℝ≥0∞`, one is less than two exactly when the other is
greater than two (`ENNReal.HolderConjugate.lt_two_iff_two_lt`, `ENNReal.conjExponent_lt_two_iff`):
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

/-- For a Hölder conjugate pair of extended exponents, one exponent is less than two exactly when
the other is greater than two. -/
theorem ENNReal.HolderConjugate.lt_two_iff_two_lt (p q : ℝ≥0∞) [p.HolderConjugate q] :
    p < 2 ↔ 2 < q := by
  have h := ENNReal.HolderConjugate.inv_add_inv_eq_one p q
  have hp : p⁻¹ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (h ▸ le_self_add)
  rw [← ENNReal.inv_two_add_inv_two] at h
  rw [← ENNReal.inv_lt_inv, ← ENNReal.inv_lt_inv (a := q)]
  constructor
  · intro hlt
    by_contra hle
    exact (ENNReal.add_lt_add_of_lt_of_le (by simp) hlt (not_lt.1 hle : 2⁻¹ ≤ q⁻¹)).ne' h
  · intro hlt
    by_contra hle
    exact (ENNReal.add_lt_add_of_le_of_lt hp (not_lt.1 hle : p⁻¹ ≤ 2⁻¹) hlt).ne h

/-- The conjugate exponent of `p` is less than two exactly when `p > 2`. -/
theorem ENNReal.conjExponent_lt_two_iff {p : ℝ≥0∞} : p.conjExponent < 2 ↔ 2 < p := by
  rcases lt_or_ge p 1 with hp | hp
  · -- below one, the conjugate exponent is `∞`
    rw [conjExponent, tsub_eq_zero_of_le hp.le, ENNReal.inv_zero, add_top]
    exact iff_of_false (by simp) (by simpa using (hp.trans one_lt_two).le)
  · have := HolderConjugate.conjExponent hp
    exact HolderConjugate.lt_two_iff_two_lt p.conjExponent p

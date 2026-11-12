/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.OfDigits

/-!
# Comparing base-`b` expansions

Mathlib's `Real.ofDigits a` is the real number `0.a₀a₁a₂…` in base `b`. This file notes that the
all-zero digit sequence has value `0`, bounds `Real.ofDigits a` by its finite partial sums, and
deduces the lexicographic comparison of expansions: if two digit
sequences agree before position `n` and the first has the smaller digit at `n`, then its value
is at most that of the second, and strictly smaller when the two digits at `n` differ by at
least two. The strict form says, for example, that ternary expansions using only the digits `0`
and `2` are ordered lexicographically, which is how the Cantor function is shown to take the
dyadic value `0.s₀s₁…` (in base `2`) at the Cantor point `0.(2s₀)(2s₁)…` (in base `3`).

## Main results

* `Real.ofDigits_const_zero`: the all-zero digit sequence has value `0`.
* `Real.sum_ofDigitsTerm_le_ofDigits`, `Real.ofDigits_le_sum_ofDigitsTerm_add`: the value of a
  digit sequence lies between its `n`-th partial sum and that partial sum plus `b⁻ⁿ`.
* `Real.ofDigits_add_le_ofDigits`: quantitative lexicographic comparison of `Real.ofDigits`.
* `Real.ofDigits_le_ofDigits_of_lt`: lexicographic monotonicity of `Real.ofDigits`.
* `Real.ofDigits_lt_ofDigits_of_add_one_lt`: strict lexicographic monotonicity when the first
  differing digits are at least two apart.
-/

public section

namespace Real

variable {b : ℕ}

/-- The all-zero digit sequence has value `0`. -/
@[simp]
theorem ofDigits_const_zero [NeZero b] : ofDigits (fun _ ↦ (0 : Fin b)) = 0 := by
  simp [ofDigits, ofDigitsTerm]

/-- A partial sum of the digit terms is a lower bound for the value of the digit sequence. -/
theorem sum_ofDigitsTerm_le_ofDigits (a : ℕ → Fin b) (n : ℕ) :
    ∑ i ∈ Finset.range n, ofDigitsTerm a i ≤ ofDigits a :=
  summable_ofDigitsTerm.sum_le_tsum _ fun _ _ ↦ ofDigitsTerm_nonneg

/-- The value of a digit sequence exceeds its `n`-th partial sum by at most `b⁻ⁿ`. -/
theorem ofDigits_le_sum_ofDigitsTerm_add (a : ℕ → Fin b) (n : ℕ) :
    ofDigits a ≤ ∑ i ∈ Finset.range n, ofDigitsTerm a i + ((b : ℝ) ^ n)⁻¹ := by
  rw [ofDigits_eq_sum_add_ofDigits a n]
  exact add_le_add_right (mul_le_of_le_one_right (by positivity) (ofDigits_le_one _)) _

/-- If two digit sequences agree before position `n`, the value of the second exceeds that of
the first by at least `(a' n - a n - 1) b⁻⁽ⁿ⁺¹⁾`. -/
theorem ofDigits_add_le_ofDigits {a a' : ℕ → Fin b} {n : ℕ} (h : ∀ i < n, a i = a' i) :
    ofDigits a + ((a' n : ℝ) - a n - 1) * ((b : ℝ) ^ (n + 1))⁻¹ ≤ ofDigits a' := by
  have hsum : ∑ i ∈ Finset.range n, ofDigitsTerm a i =
      ∑ i ∈ Finset.range n, ofDigitsTerm a' i :=
    Finset.sum_congr rfl fun i hi ↦ by simp [ofDigitsTerm, h i (Finset.mem_range.mp hi)]
  have h₁ := ofDigits_le_sum_ofDigitsTerm_add a (n + 1)
  have h₂ := sum_ofDigitsTerm_le_ofDigits a' (n + 1)
  rw [Finset.sum_range_succ, hsum] at h₁
  rw [Finset.sum_range_succ] at h₂
  simp only [ofDigitsTerm] at h₁ h₂
  linarith

/-- *Lexicographic monotonicity*: if two digit sequences agree before position `n` and the
first has the smaller digit at `n`, then its value is at most that of the second. -/
theorem ofDigits_le_ofDigits_of_lt {a a' : ℕ → Fin b} {n : ℕ} (h : ∀ i < n, a i = a' i)
    (hn : a n < a' n) : ofDigits a ≤ ofDigits a' := by
  have hn' : (a n : ℝ) + 1 ≤ a' n := by exact_mod_cast Fin.lt_def.mp hn
  have := ofDigits_add_le_ofDigits h
  have : 0 ≤ ((a' n : ℝ) - a n - 1) * ((b : ℝ) ^ (n + 1))⁻¹ :=
    mul_nonneg (by linarith) (by positivity)
  linarith

/-- *Strict lexicographic monotonicity*: if two digit sequences agree before position `n` and
their digits at `n` satisfy `a n + 1 < a' n`, then the value of the first is strictly smaller. -/
theorem ofDigits_lt_ofDigits_of_add_one_lt {a a' : ℕ → Fin b} {n : ℕ}
    (h : ∀ i < n, a i = a' i) (hn : (a n : ℕ) + 1 < a' n) : ofDigits a < ofDigits a' := by
  have hb : 0 < b := Fin.pos (a 0)
  have hn' : (a n : ℝ) + 1 < a' n := by exact_mod_cast hn
  have := ofDigits_add_le_ofDigits h
  have : 0 < ((a' n : ℝ) - a n - 1) * ((b : ℝ) ^ (n + 1))⁻¹ :=
    mul_pos (by linarith) (by positivity)
  linarith

end Real

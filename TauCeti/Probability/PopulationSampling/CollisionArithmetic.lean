/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Strict improvement of the finite sampling collision bound

For a population of size `n` and a sample of size `m ≤ n`, write
`p = n.descFactorial m / n ^ m` for the probability of drawing distinct indices with replacement.
If also `2 ≤ n`, then `t = m.descFactorial 2 / n.descFactorial 2` is the probability that a
sample without replacement hits two specified distinct indices. Identifying the values at those
indices gives the one-pair excess formula `1 - p - t * min p (1 - p)`.

This file characterizes exactly when the correction `t * min p (1 - p)` is positive: `2 ≤ m ≤ n`.
This is the arithmetic input for excluding repeated-value populations from attaining the
collision bound in the feasible, nontrivial sample regime. All arithmetic is in `ℝ`, with the usual
zero-denominator convention, so the characterization includes empty populations and samples.
-/

public section

namespace TauCeti.Probability

/-- With `p = n.descFactorial m / n ^ m` and `t = m.descFactorial 2 / n.descFactorial 2` in `ℝ`,
the correction `t * min p (1 - p)` is positive exactly when `2 ≤ m` and `m ≤ n`. Equivalently,
`1 - p - t * min p (1 - p)` is strictly less than `1 - p` exactly in that regime. -/
theorem descFactorial_div_mul_min_pos_iff (m n : ℕ) :
    0 < (m.descFactorial 2 : ℝ) / n.descFactorial 2 *
      min ((n.descFactorial m : ℝ) / (n : ℝ) ^ m)
        (1 - (n.descFactorial m : ℝ) / (n : ℝ) ^ m) ↔ 2 ≤ m ∧ m ≤ n := by
  set p : ℝ := n.descFactorial m / (n : ℝ) ^ m
  set t : ℝ := m.descFactorial 2 / n.descFactorial 2
  constructor
  · intro h
    have hm : 2 ≤ m := by
      by_contra hm
      have hm' : m = 0 ∨ m = 1 := by omega
      rcases hm' with rfl | rfl <;>
        simp [t, Nat.descFactorial_succ] at h
    refine ⟨hm, ?_⟩
    by_contra hmn
    have hp : p = 0 := by
      simp [p, Nat.descFactorial_of_lt (by omega : n < m)]
    rw [hp] at h
    norm_num at h
  · rintro ⟨hm, hmn⟩
    have hn : 0 < n := by omega
    have hnPow : 0 < (n : ℝ) ^ m := pow_pos (Nat.cast_pos.mpr hn) _
    have hp : 0 < p :=
      div_pos (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hmn)) hnPow
    have hp1 : p < 1 := by
      apply (div_lt_one hnPow).mpr
      exact_mod_cast Nat.descFactorial_lt_pow (by omega : n ≠ 0) hm
    have ht : 0 < t :=
      div_pos (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hm))
        (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr (hm.trans hmn)))
    exact mul_pos ht (lt_min hp (sub_pos.mpr hp1))

end TauCeti.Probability

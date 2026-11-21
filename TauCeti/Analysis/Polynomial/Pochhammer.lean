/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Norm bounds for rising Pochhammer polynomials

In any seminormed ring `R` with `‖1‖ = 1`, each linear factor `x + k` of the rising Pochhammer
polynomial `ascPochhammer R m` has norm at most `‖x‖ + k`. Multiplying these bounds gives the
uniform estimate `‖(ascPochhammer R m).eval x‖ ≤ (‖x‖ + m) ^ m` and, when `‖x‖ ≤ N` for a natural
number `N`, the polynomial-times-factorial estimate
`‖(ascPochhammer R m).eval x‖ ≤ (m + N) ^ N * m!`.

## Main results

* `TauCeti.norm_ascPochhammer_eval_le_pow`: `‖(ascPochhammer R j).eval x‖ ≤ (‖x‖ + j) ^ j`.
* `TauCeti.norm_ascPochhammer_eval_le_pow_mul_factorial`: for `‖x‖ ≤ N`,
  `‖(ascPochhammer R m).eval x‖ ≤ (m + N) ^ N * m!`.
-/

public section

open scoped Nat

namespace TauCeti

variable {R : Type*} [SeminormedRing R] [NormOneClass R]

/-- In a seminormed ring with `‖1‖ = 1`, the rising Pochhammer evaluation at `x` has norm at most
`(‖x‖ + j) ^ j`. -/
theorem norm_ascPochhammer_eval_le_pow (j : ℕ) (x : R) :
    ‖(ascPochhammer R j).eval x‖ ≤ (‖x‖ + j) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ascPochhammer_succ_eval, pow_succ]
    push_cast
    have hj : ‖(j : R)‖ ≤ j := by simpa using Nat.norm_cast_le (α := R) j
    refine (norm_mul_le _ _).trans (mul_le_mul
      (ih.trans (pow_le_pow_left₀ (by positivity) (by linarith) j))
      ((norm_add_le x (j : R)).trans (by linarith))
      (norm_nonneg _) (by positivity))

/-- In a seminormed ring with `‖1‖ = 1`, if `‖x‖ ≤ N` for a natural number `N`, then
`‖(ascPochhammer R m).eval x‖ ≤ (m + N) ^ N * m!`. -/
theorem norm_ascPochhammer_eval_le_pow_mul_factorial {x : R} {N : ℕ} (hx : ‖x‖ ≤ N) (m : ℕ) :
    ‖(ascPochhammer R m).eval x‖ ≤ (m + N : ℝ) ^ N * m ! := by
  have hfac : ‖(ascPochhammer R m).eval x‖ ≤ ((m + N)! : ℝ) := by
    induction m with
    | zero =>
      simp only [ascPochhammer_zero, Polynomial.eval_one, norm_one, zero_add]
      exact_mod_cast Nat.factorial_pos N
    | succ m ih =>
      have hsucc : m + 1 + N = (m + N) + 1 := by omega
      rw [ascPochhammer_succ_eval, hsucc, Nat.factorial_succ, Nat.mul_comm, Nat.cast_mul]
      have hm : ‖(m : R)‖ ≤ m := by simpa using Nat.norm_cast_le (α := R) m
      have hxm : ‖x + (m : R)‖ ≤ ((m + N + 1 : ℕ) : ℝ) := by
        calc ‖x + (m : R)‖ ≤ ‖x‖ + ‖(m : R)‖ := norm_add_le _ _
          _ ≤ N + m := add_le_add hx hm
          _ ≤ ((m + N + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact (norm_mul_le _ _).trans (mul_le_mul ih hxm (norm_nonneg _) (by positivity))
  refine hfac.trans ?_
  have hpow : (m + N)! ≤ (m + N) ^ N * m ! := by
    rw [← Nat.factorial_mul_ascFactorial m N, Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (Nat.ascFactorial_le_pow_add m N)
  exact_mod_cast hpow

end TauCeti

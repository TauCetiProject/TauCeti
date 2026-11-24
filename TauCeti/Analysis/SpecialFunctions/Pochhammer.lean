/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Norm bounds for Pochhammer polynomials

This file complements `Mathlib.Analysis.SpecialFunctions.Pochhammer` with norm bounds for the
evaluated ascending Pochhammer polynomial `(ascPochhammer R n).eval x = x (x + 1) ⋯ (x + n - 1)`
in a seminormed ring satisfying `‖(1 : R)‖ = 1`. It also bounds the two endpoint factors on a
complex vertical line by the evaluated ascending Pochhammer polynomial.

## Main results

* `TauCeti.norm_ascPochhammer_eval_le_of_norm_le`: if `‖x‖ ≤ r`, then
  `‖(ascPochhammer R n).eval x‖ ≤ (ascPochhammer ℝ n).eval r`.
* `TauCeti.norm_ascPochhammer_eval_le`:
  `‖(ascPochhammer R n).eval x‖ ≤ (ascPochhammer ℝ n).eval ‖x‖`.
* `TauCeti.norm_ascPochhammer_eval_le_ascFactorial`: if `‖x‖ ≤ M` for `M : ℕ`, then
  `‖(ascPochhammer R n).eval x‖ ≤ M.ascFactorial n`.
* `TauCeti.norm_ascPochhammer_eval_le_pow`: `‖(ascPochhammer R j).eval x‖ ≤ (‖x‖ + j) ^ j`.
* `TauCeti.norm_ascPochhammer_eval_le_factorial_mul_pow`: if `‖x‖ ≤ M` for `M : ℕ`, then
  `‖(ascPochhammer R n).eval x‖ ≤ n! (M + n) ^ M`.
* `TauCeti.norm_endpoints_le_norm_ascPochhammer_eval`: the first and last factor norms are
  bounded by the polynomial norm when every intermediate real factor has absolute value at
  least one.
-/

public section

open scoped Nat

namespace TauCeti

/-- If `‖x‖ ≤ r` in a seminormed ring with `‖1‖ = 1`, then the evaluated ascending Pochhammer
polynomial `(x)ₙ = x (x + 1) ⋯ (x + n - 1)` has norm at most `(r)ₙ`. -/
theorem norm_ascPochhammer_eval_le_of_norm_le {R : Type*} [SeminormedRing R] [NormOneClass R]
    (n : ℕ) {x : R} {r : ℝ} (hx : ‖x‖ ≤ r) :
    ‖(ascPochhammer R n).eval x‖ ≤ (ascPochhammer ℝ n).eval r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    exact (norm_mul_le _ _).trans <|
      mul_le_mul ih
        ((norm_add_le x (n : R)).trans
          (add_le_add hx (by simpa using Nat.norm_cast_le (α := R) n)))
        (norm_nonneg _) ((norm_nonneg _).trans ih)

/-- In a seminormed ring with `‖1‖ = 1`, the norm of the evaluated ascending Pochhammer
polynomial `(x)ₙ = x (x + 1) ⋯ (x + n - 1)` is bounded by `(‖x‖)ₙ`. -/
theorem norm_ascPochhammer_eval_le {R : Type*} [SeminormedRing R] [NormOneClass R]
    (n : ℕ) (x : R) :
    ‖(ascPochhammer R n).eval x‖ ≤ (ascPochhammer ℝ n).eval ‖x‖ :=
  norm_ascPochhammer_eval_le_of_norm_le n le_rfl

/-- If `‖x‖ ≤ M` for a natural number `M` in a seminormed ring with `‖1‖ = 1`, then the evaluated
ascending Pochhammer polynomial `(x)ₙ` has norm at most the rising factorial `M.ascFactorial n`. -/
theorem norm_ascPochhammer_eval_le_ascFactorial {R : Type*} [SeminormedRing R] [NormOneClass R]
    (n : ℕ) {x : R} {M : ℕ} (hx : ‖x‖ ≤ M) :
    ‖(ascPochhammer R n).eval x‖ ≤ M.ascFactorial n :=
  (norm_ascPochhammer_eval_le_of_norm_le n hx).trans_eq
    (ascPochhammer_nat_eq_natCast_ascFactorial ℝ M n)

/-- In a seminormed ring with `‖1‖ = 1`, the rising Pochhammer evaluation at `x` has norm at most
`(‖x‖ + j) ^ j`. -/
theorem norm_ascPochhammer_eval_le_pow {R : Type*} [SeminormedRing R] [NormOneClass R]
    (j : ℕ) (x : R) :
    ‖(ascPochhammer R j).eval x‖ ≤ (‖x‖ + j) ^ j := by
  refine (norm_ascPochhammer_eval_le j x).trans ?_
  rw [ascPochhammer_eval_eq_prod_range]
  calc ∏ i ∈ Finset.range j, (‖x‖ + i)
      ≤ ∏ _i ∈ Finset.range j, (‖x‖ + j) := by
        gcongr with i hi
        exact (Finset.mem_range.mp hi).le
    _ = (‖x‖ + j) ^ j := by simp

/-- If `‖x‖ ≤ M` for a natural number `M` in a seminormed ring with `‖1‖ = 1`, then the evaluated
ascending Pochhammer polynomial `(x)ₙ` has norm at most `n! (M + n) ^ M`: it grows like `n!` up to
a polynomial factor. -/
theorem norm_ascPochhammer_eval_le_factorial_mul_pow {R : Type*} [SeminormedRing R]
    [NormOneClass R] (n : ℕ) {x : R} {M : ℕ} (hx : ‖x‖ ≤ M) :
    ‖(ascPochhammer R n).eval x‖ ≤ n ! * ((M : ℝ) + n) ^ M := by
  have h := norm_ascPochhammer_eval_le_ascFactorial n (M := M + 1)
    (hx.trans (by push_cast; linarith))
  rw [Nat.ascFactorial_eq_factorial_mul_choose] at h
  have hc : (M + n).choose n ≤ (M + n) ^ M := by
    rw [← Nat.choose_symm_add]
    exact Nat.choose_le_pow _ _
  calc ‖(ascPochhammer R n).eval x‖ ≤ ((n ! * (M + n).choose n : ℕ) : ℝ) := h
    _ ≤ ((n ! * (M + n) ^ M : ℕ) : ℝ) := by exact_mod_cast Nat.mul_le_mul_left _ hc
    _ = n ! * ((M : ℝ) + n) ^ M := by push_cast; ring

/-- If the intermediate real factors have absolute value at least one, the norm of the
ascending Pochhammer polynomial bounds the product of its first and last factor norms on a
vertical line. For `j = 1` the intermediate condition is empty; the endpoint factors may vanish. -/
theorem norm_endpoints_le_norm_ascPochhammer_eval (j : ℕ) (hj : 1 ≤ j) (c t : ℝ)
    (hmid : ∀ k : ℕ, 0 < k → k < j → 1 ≤ |c + k|) :
    ‖(c : ℂ) + t * Complex.I‖ * ‖((c + j : ℝ) : ℂ) + t * Complex.I‖ ≤
      ‖(ascPochhammer ℂ (j + 1)).eval ((c : ℂ) + t * Complex.I)‖ := by
  have hprefix : ∀ n : ℕ, 1 ≤ n → n ≤ j →
      ‖(c : ℂ) + t * Complex.I‖ ≤ ‖(ascPochhammer ℂ n).eval ((c : ℂ) + t * Complex.I)‖ := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn hnj
      rcases n.eq_zero_or_pos with rfl | hn0
      · simp
      have hfactor : 1 ≤ ‖(c : ℂ) + t * Complex.I + n‖ := by
        calc
          1 ≤ |c + n| := hmid n hn0 (by omega)
          _ ≤ ‖(c : ℂ) + t * Complex.I + n‖ := by
            simpa using Complex.abs_re_le_norm ((c : ℂ) + t * Complex.I + n)
      rw [ascPochhammer_succ_eval, norm_mul]
      exact (ih hn0 (by omega)).trans
        (le_mul_of_one_le_right (norm_nonneg _) hfactor)
  rw [ascPochhammer_succ_eval, norm_mul]
  have heq : (c : ℂ) + t * Complex.I + j = ((c + j : ℝ) : ℂ) + t * Complex.I := by
    push_cast
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right (hprefix j hj le_rfl) (norm_nonneg _)

end TauCeti

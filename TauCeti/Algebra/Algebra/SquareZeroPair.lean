/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Group.Nat.Even

/-!
# Two square-zero elements with a nilpotent sum

Let `x` and `y` be elements of an `R`-algebra with `x * x = 0` and `y * y = 0`, and write
`s = x + y`. A product of factors from `{x, y}` vanishes as soon as two neighbouring factors are
equal, so the only surviving products are the alternating words `x y x ⋯` and `y x y ⋯`. These are
`x * s ^ t` and `y * s ^ t`, since every other word in the expansion of `s ^ t` has a repeated
neighbour. Hence the `t + 1`-st power of the span of `{x, y}` is spanned by `x * s ^ t` and
`y * s ^ t`, and **if `s ^ m = 0` then every product of `m + 1` factors from `{x, y}` vanishes**.

For the preprojective algebra of a graph, `x` and `y` are the two backtracks from a vertex into
two leaves attached to it, each of which squares to zero by the relation at its leaf. This is
the step which bounds the length of the nonzero paths through the branch vertex of `Dₙ`.

## Main results

* `TauCeti.mul_add_eq_add_mul_of_mul_self_eq_zero` and
  `TauCeti.mul_add_pow_eq_add_pow_mul_of_mul_self_eq_zero`: moving an element of a square-zero
  pair past a power of their sum preserves or exchanges the element according to parity.
* `TauCeti.span_pair_pow_succ_le`: the `t + 1`-st power of the span of `{x, y}` lies in the span
  of `x * (x + y) ^ t` and `y * (x + y) ^ t`.
* `TauCeti.span_pair_pow_succ_eq_bot`: if moreover `(x + y) ^ m = 0`, then the `m + 1`-st power of
  the span of `{x, y}` is zero.
-/

public section

namespace TauCeti

open Submodule

variable {A : Type*} [Semiring A] {x y : A}

/-- Moving an element of a square-zero pair past their sum exchanges the element. -/
theorem mul_add_eq_add_mul_of_mul_self_eq_zero (hx : x * x = 0) (hy : y * y = 0) :
    x * (x + y) = (x + y) * y := by
  simp only [mul_add, add_mul, hx, hy, zero_add, add_zero]

/-- Moving an element of a square-zero pair past a power of their sum preserves it at even
exponents and exchanges it at odd exponents. -/
theorem mul_add_pow_eq_add_pow_mul_of_mul_self_eq_zero (hx : x * x = 0) (hy : y * y = 0)
    (t : ℕ) : x * (x + y) ^ t = (x + y) ^ t * (if Even t then x else y) := by
  induction t with
  | zero => simp
  | succ t ih =>
    calc
      x * (x + y) ^ (t + 1) = (x * (x + y) ^ t) * (x + y) := by
        rw [pow_succ, mul_assoc]
      _ = ((x + y) ^ t * (if Even t then x else y)) * (x + y) := by rw [ih]
      _ = (x + y) ^ (t + 1) * (if Even (t + 1) then x else y) := by
        rw [pow_succ, mul_assoc, mul_assoc]
        congr 1
        by_cases ht : Even t
        · simpa only [Nat.even_add_one, ht, not_true_eq_false, ite_true, ite_false] using
            mul_add_eq_add_mul_of_mul_self_eq_zero hx hy
        · simpa only [Nat.even_add_one, ht, not_false_eq_true, ite_true, ite_false, add_comm] using
            mul_add_eq_add_mul_of_mul_self_eq_zero hy hx

variable {R : Type*} [CommSemiring R] [Algebra R A]

/-- If `x` and `y` square to zero, the products of `t + 1` factors from `{x, y}` span at most the
two alternating words `x * (x + y) ^ t` and `y * (x + y) ^ t`. -/
theorem span_pair_pow_succ_le (hx : x * x = 0) (hy : y * y = 0) (t : ℕ) :
    span R {x, y} ^ (t + 1) ≤ span R {x * (x + y) ^ t, y * (x + y) ^ t} := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ' (span R {x, y})]
    refine (mul_le_mul_right ih _).trans ?_
    rw [span_mul_span, span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    dsimp only
    -- A repeated factor vanishes, and the alternating products extend the alternating words.
    have hxs : x * (y * (x + y) ^ t) = x * (x + y) ^ (t + 1) := by
      rw [pow_succ', ← mul_assoc, ← mul_assoc, mul_add, hx, zero_add]
    have hys : y * (x * (x + y) ^ t) = y * (x + y) ^ (t + 1) := by
      rw [pow_succ', ← mul_assoc, ← mul_assoc, mul_add, hy, add_zero]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rw [← mul_assoc, hx, zero_mul]
      exact zero_mem _
    · rw [hxs]
      exact subset_span (by simp)
    · rw [hys]
      exact subset_span (by simp)
    · rw [← mul_assoc, hy, zero_mul]
      exact zero_mem _

/-- **Two square-zero elements with a nilpotent sum.** If `x * x = 0`, `y * y = 0` and
`(x + y) ^ m = 0`, then every product of `m + 1` factors from `{x, y}` vanishes. -/
theorem span_pair_pow_succ_eq_bot (hx : x * x = 0) (hy : y * y = 0) {m : ℕ}
    (hm : (x + y) ^ m = 0) : span R {x, y} ^ (m + 1) = ⊥ := by
  refine eq_bot_iff.2 ((span_pair_pow_succ_le hx hy m).trans ?_)
  simp [hm]

end TauCeti

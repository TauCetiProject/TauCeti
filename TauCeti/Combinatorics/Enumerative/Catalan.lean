/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Recurrences of the Catalan numbers

Mathlib defines `catalan` by the convolution recurrence and proves
`(n + 1) * catalan n = Nat.centralBinom n`. Combined with the ratio recurrence of the central
binomial coefficients, this gives the first-order recurrence
`(n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n`. This is the form in which Catalan
numbers arise as solutions of linear moment recurrences, such as the even moments of the
semicircle law.

The signed Catalan numbers `(-1)^k C_k` satisfy the Catalan recurrence up to a sign:
`∑_{i ≤ k} (-1)^i C_i (-1)^(k-i) C_(k-i) = (-1)^k C_(k+1)`. This is the recurrence satisfied by
the Möbius function `μ(0̂, 1̂)` of the lattice of noncrossing partitions.

## Main results

* `Nat.catalan_le_four_pow` — the exponential bound `Cₙ ≤ 4ⁿ`.
* `Nat.add_two_mul_catalan_succ` — the first-order recurrence `(n + 2) Cₙ₊₁ = 2 (2n + 1) Cₙ`.
* `Nat.catalan_pos`, `Nat.catalan_lt_catalan_succ`, `Nat.catalan_succ_lt_four_mul`,
  `Nat.monotone_catalan`, `Nat.self_le_catalan` — growth of the Catalan numbers read off from
  the first-order recurrence: `0 < Cₙ`, `Cₙ < Cₙ₊₁ < 4 Cₙ` for `0 < n`, and `n ≤ Cₙ`.
* `Nat.catalan_four` — the value `C₄ = 14`.
* `Nat.mul_add_one_le_centralBinom_iff` — `n (r + 1) ≤ (2r choose r) ↔ n ≤ Cᵣ`.
* `TauCeti.sum_range_neg_one_pow_mul_catalan` — the convolution of the signed Catalan numbers.
-/

public section

namespace Nat

/-- The Catalan numbers have exponential growth bounded by `4 ^ n`. -/
theorem catalan_le_four_pow (n : ℕ) : catalan n ≤ 4 ^ n := by
  calc
    catalan n ≤ n.centralBinom := by
      rw [catalan_eq_centralBinom_div]
      exact Nat.div_le_self _ _
    _ ≤ 4 ^ n := centralBinom_le_four_pow n

/-- The first-order recurrence `(n + 2) Cₙ₊₁ = 2 (2n + 1) Cₙ` of the Catalan numbers. -/
theorem add_two_mul_catalan_succ (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  apply Nat.eq_of_mul_eq_mul_left n.succ_pos
  calc
    (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * (n + 1).centralBinom := by
      rw [← succ_mul_catalan_eq_centralBinom]
    _ = 2 * (2 * n + 1) * n.centralBinom := Nat.succ_mul_centralBinom_succ n
    _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
      rw [← succ_mul_catalan_eq_centralBinom]
      ring

/-- The fourth Catalan number: `C₄ = 14`. -/
theorem catalan_four : catalan 4 = 14 := by
  have h : 5 * catalan 4 = 70 := by simpa [catalan_three] using add_two_mul_catalan_succ 3
  omega

/-- The Catalan numbers are positive. -/
theorem catalan_pos (n : ℕ) : 0 < catalan n :=
  Nat.pos_of_ne_zero fun h => centralBinom_ne_zero n <| by
    rw [← succ_mul_catalan_eq_centralBinom, h, mul_zero]

/-- From index one on, the Catalan numbers increase strictly: `Cₙ < Cₙ₊₁` for `0 < n`. -/
theorem catalan_lt_catalan_succ {n : ℕ} (hn : 0 < n) : catalan n < catalan (n + 1) := by
  have h := add_two_mul_catalan_succ n
  have hc := catalan_pos n
  nlinarith

/-- Consecutive Catalan numbers grow by a factor less than four: `Cₙ₊₁ < 4 Cₙ`. -/
theorem catalan_succ_lt_four_mul (n : ℕ) : catalan (n + 1) < 4 * catalan n := by
  have h := add_two_mul_catalan_succ n
  have hc := catalan_pos n
  nlinarith

/-- The Catalan numbers are monotone; `C₀ = C₁ = 1` is the only repetition. -/
theorem monotone_catalan : Monotone catalan := by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [catalan_zero, catalan_one]
  · exact (catalan_lt_catalan_succ hn).le

/-- The Catalan numbers dominate their index: `n ≤ Cₙ`. -/
theorem self_le_catalan (n : ℕ) : n ≤ catalan n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [catalan_one]
    · exact ih.trans_lt (catalan_lt_catalan_succ hn)

/-- The inequality `n (r + 1) ≤ (2r choose r)` says exactly that `n ≤ Cᵣ`, by
`(r + 1) Cᵣ = (2r choose r)`. -/
theorem mul_add_one_le_centralBinom_iff {n r : ℕ} :
    n * (r + 1) ≤ r.centralBinom ↔ n ≤ catalan r := by
  rw [← succ_mul_catalan_eq_centralBinom, mul_comm (r + 1)]
  exact Nat.mul_le_mul_right_iff r.succ_pos

end Nat

open Finset

namespace TauCeti

/-- The convolution of the signed Catalan numbers:
`∑_{i ≤ k} (-1)^i C_i (-1)^(k-i) C_(k-i) = (-1)^k C_(k+1)`. -/
theorem sum_range_neg_one_pow_mul_catalan {R : Type*} [CommRing R] (k : ℕ) :
    ∑ i ∈ range (k + 1), (-1 : R) ^ i * catalan i * ((-1) ^ (k - i) * catalan (k - i)) =
      (-1) ^ k * catalan (k + 1) := by
  rw [catalan_succ, ← sum_range fun i => catalan i * catalan (k - i), Nat.cast_sum, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [← Nat.add_sub_cancel' (Nat.lt_succ_iff.1 (mem_range.1 hi)), pow_add, Nat.add_sub_cancel_left]
  push_cast
  ring

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify

/-!
# Lah numbers

The (unsigned) Lah numbers `L(n, k)` are the coefficients that express the rising factorial
`(x)ₙ = x (x + 1) ⋯ (x + n - 1)` in the basis of the falling factorials
`[x]ₖ = x (x - 1) ⋯ (x - k + 1)`:
`(x)ₙ = ∑_{k ≤ n} L(n, k) [x]ₖ`. With alternating signs they also express the falling
factorials in the basis of the rising ones: `[x]ₙ = ∑_{k ≤ n} (-1)^(n - k) L(n, k) (x)ₖ`.
For `1 ≤ k ≤ n`, `L(n, k) = C(n - 1, k - 1) n! / k!`, and `L(n, k)` counts the partitions of a
set of `n` elements into `k` nonempty linearly ordered blocks.

As for Mathlib's Stirling numbers `Nat.stirlingFirst` and `Nat.stirlingSecond`, the Lah numbers
are defined as natural numbers by their recurrence `L(n + 1, k + 1) = (n + k + 1) L(n, k + 1) +
L(n, k)`, and the expansions hold in every ring.

## Main declarations

* `Nat.lah`: the Lah numbers, defined by their recurrence.
* `Nat.lah_succ_succ_mul_factorial`: the closed form `L(n + 1, k + 1) (k + 1)! = C(n, k) (n + 1)!`.
* `Nat.cast_lah_eq_choose_mul_factorial_div`: in a division semiring of characteristic zero,
  `L(n, k) = C(n - 1, k - 1) n! / k!` for `n ≠ 0` and `k ≠ 0`.
* `TauCeti.ascPochhammer_eval_eq_sum_lah`: `(x)ₙ = ∑_{k ≤ n} L(n, k) [x]ₖ` in every ring.
* `TauCeti.descPochhammer_eval_eq_sum_lah`: `[x]ₙ = ∑_{k ≤ n} (-1)^(n - k) L(n, k) (x)ₖ` in
  every ring.

## References

* [NIST Digital Library of Mathematical Functions, 5.2.9](https://dlmf.nist.gov/5.2.E9)
-/

public section

open Finset Polynomial

namespace Nat

/-- The Lah number `Nat.lah n k`: the number of partitions of a set of `n` elements into `k`
nonempty linearly ordered blocks. It is defined by the recurrence
`lah (n + 1) (k + 1) = (n + k + 1) * lah n (k + 1) + lah n k`, with `lah 0 0 = 1`. -/
def lah : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (n + k + 1) * lah n (k + 1) + lah n k

/-- `L(0, 0) = 1`. -/
@[simp]
theorem lah_zero : lah 0 0 = 1 :=
  (rfl)

/-- `L(0, k + 1) = 0`. -/
@[simp]
theorem lah_zero_succ (k : ℕ) : lah 0 (k + 1) = 0 :=
  (rfl)

/-- `L(n + 1, 0) = 0`. -/
@[simp]
theorem lah_succ_zero (n : ℕ) : lah (n + 1) 0 = 0 :=
  (rfl)

/-- The recurrence `L(n + 1, k + 1) = (n + k + 1) L(n, k + 1) + L(n, k)` of the Lah numbers. -/
theorem lah_succ_succ (n k : ℕ) :
    lah (n + 1) (k + 1) = (n + k + 1) * lah n (k + 1) + lah n k :=
  (rfl)

/-- The recurrence `L(n + 1, k) = (n + k) L(n, k) + L(n, k - 1)` of the Lah numbers, for
`k ≠ 0`. -/
theorem lah_succ_left (n k : ℕ) (hk : k ≠ 0) :
    lah (n + 1) k = (n + k) * lah n k + lah n (k - 1) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hk)
  rw [lah_succ_succ, Nat.add_sub_cancel, add_assoc]

/-- `L(n, k) = 0` for `n < k`. -/
theorem lah_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → lah n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [lah_succ_succ, lah_eq_zero_of_lt (by omega : n < k + 1),
      lah_eq_zero_of_lt (by omega : n < k), mul_zero]

/-- `L(n, n) = 1`. -/
@[simp]
theorem lah_self (n : ℕ) : lah n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [lah_succ_succ, lah_eq_zero_of_lt n.lt_succ_self, ih, mul_zero, zero_add]

/-- The closed form `L(n + 1, k + 1) (k + 1)! = C(n, k) (n + 1)!` of the Lah numbers. -/
theorem lah_succ_succ_mul_factorial (n k : ℕ) :
    lah (n + 1) (k + 1) * (k + 1)! = n.choose k * (n + 1)! := by
  induction n generalizing k with
  | zero => cases k <;> simp [lah_succ_succ]
  | succ n ih =>
    cases k with
    | zero =>
      have h := ih 0
      simp only [lah_succ_succ, lah_succ_zero, zero_add, factorial_one, mul_one,
        choose_zero_right, one_mul] at h ⊢
      rw [add_zero, h, factorial_succ (n + 1)]
    | succ j =>
      have hA := ih (j + 1)
      have hB := ih j
      have hf : (j + 1 + 1)! = (j + 2) * (j + 1)! := factorial_succ (j + 1)
      rw [lah_succ_succ, choose_succ_succ, factorial_succ (n + 1)]
      rcases le_or_gt j n with hjn | hnj
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjn
        have h := choose_succ_right_eq (j + m) j
        rw [Nat.add_sub_cancel_left] at h
        zify at hA hB hf h ⊢
        linear_combination ((j : ℤ) + m + j + 3) * hA + ((j : ℤ) + 2) * hB +
          (lah (j + m + 1) (j + 1) : ℤ) * hf + ((j + m + 1)! : ℤ) * h
      · rw [choose_eq_zero_of_lt hnj, choose_eq_zero_of_lt (by omega : n < j + 1),
          lah_eq_zero_of_lt (by omega : n + 1 < j + 1 + 1),
          lah_eq_zero_of_lt (by omega : n + 1 < j + 1)]
        simp

/-- The closed form `L(n, k) = C(n - 1, k - 1) n! / k!` of the Lah numbers for `n ≠ 0` and
`k ≠ 0`, in a division semiring of characteristic zero. Together with `Nat.lah_zero`,
`Nat.lah_zero_succ` and `Nat.lah_succ_zero` it determines `Nat.lah`. -/
theorem cast_lah_eq_choose_mul_factorial_div {K : Type*} [DivisionSemiring K] [CharZero K]
    {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    (lah n k : K) = ((n - 1).choose (k - 1) : K) * (n ! : K) / (k ! : K) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hn)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hk)
  rw [eq_div_iff (Nat.cast_ne_zero.2 (factorial_ne_zero _)), Nat.add_sub_cancel,
    Nat.add_sub_cancel]
  exact_mod_cast lah_succ_succ_mul_factorial n k

end Nat

namespace TauCeti

variable {R : Type*} [Ring R]

/-- **The Lah expansion** of the rising factorial in the falling factorials:
`(x)ₙ = ∑_{k ≤ n} L(n, k) [x]ₖ`, where `(x)ₙ = x (x + 1) ⋯ (x + n - 1)` and
`[x]ₖ = x (x - 1) ⋯ (x - k + 1)` (DLMF 5.2.9). -/
theorem ascPochhammer_eval_eq_sum_lah (x : R) (n : ℕ) :
    (ascPochhammer R n).eval x =
      ∑ k ∈ range (n + 1), (n.lah k : R) * (descPochhammer R k).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- `[x]ₖ (x + n) = [x]ₖ₊₁ + (n + k) [x]ₖ`.
    have hstep (k : ℕ) : (descPochhammer R k).eval x * (x + n) =
        (descPochhammer R (k + 1)).eval x + ((n + k : ℕ) : R) * (descPochhammer R k).eval x := by
      rw [descPochhammer_succ_eval, Nat.cast_comm, ← mul_add]
      congr 1
      push_cast
      abel
    -- The boundary terms: `L(n, 0) n = 0` and `L(n, n + 1) = 0`.
    have h0 : n.lah 0 * (n + 0) = 0 := by cases n <;> simp
    have hshift : ∑ k ∈ range (n + 1), ((n.lah k * (n + k) : ℕ) : R) *
          (descPochhammer R k).eval x =
        ∑ k ∈ range (n + 1), (((n + k + 1) * n.lah (k + 1) : ℕ) : R) *
          (descPochhammer R (k + 1)).eval x := by
      rw [sum_range_succ', sum_range_succ, h0, Nat.lah_eq_zero_of_lt n.lt_succ_self, mul_zero,
        Nat.cast_zero, zero_mul, zero_mul, add_zero, add_zero]
      refine sum_congr rfl fun k _ => ?_
      rw [mul_comm (n.lah (k + 1)), add_assoc]
    calc (ascPochhammer R (n + 1)).eval x
        = ∑ k ∈ range (n + 1), (n.lah k : R) * ((descPochhammer R k).eval x * (x + n)) := by
          rw [ascPochhammer_succ_eval, ih, sum_mul]
          simp_rw [mul_assoc]
      _ = ∑ k ∈ range (n + 1), (n.lah k : R) * (descPochhammer R (k + 1)).eval x +
          ∑ k ∈ range (n + 1), ((n.lah k * (n + k) : ℕ) : R) *
            (descPochhammer R k).eval x := by
          rw [← sum_add_distrib]
          refine sum_congr rfl fun k _ => ?_
          rw [hstep, mul_add, Nat.cast_mul, mul_assoc]
      _ = ∑ k ∈ range (n + 1 + 1), ((n + 1).lah k : R) * (descPochhammer R k).eval x := by
          rw [hshift, ← sum_add_distrib, sum_range_succ' _ (n + 1), Nat.lah_succ_zero,
            Nat.cast_zero, zero_mul, add_zero]
          refine sum_congr rfl fun k _ => ?_
          rw [Nat.lah_succ_succ, Nat.cast_add, add_mul (R := R)]
          exact add_comm _ _

/-- **The Lah expansion** of the falling factorial in the rising factorials:
`[x]ₙ = ∑_{k ≤ n} (-1)^(n - k) L(n, k) (x)ₖ`, where `[x]ₙ = x (x - 1) ⋯ (x - n + 1)` and
`(x)ₖ = x (x + 1) ⋯ (x + k - 1)` (DLMF 5.2.9). -/
theorem descPochhammer_eval_eq_sum_lah (x : R) (n : ℕ) :
    (descPochhammer R n).eval x =
      ∑ k ∈ range (n + 1), (-1) ^ (n - k) * (n.lah k : R) * (ascPochhammer R k).eval x := by
  -- `[y]ₖ = (-1)ᵏ (-y)ₖ`, from `(-y)ₖ = (-1)ᵏ [y]ₖ`.
  have hdesc (k : ℕ) (y : R) :
      (descPochhammer R k).eval y = (-1) ^ k * (ascPochhammer R k).eval (-y) := by
    rw [ascPochhammer_eval_neg_eq_descPochhammer, ← mul_assoc, ← pow_add,
      Even.neg_one_pow ⟨k, rfl⟩, one_mul]
  rw [hdesc, ascPochhammer_eval_eq_sum_lah, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hkn
  rw [hdesc, neg_neg, Nat.add_sub_cancel, ← (Nat.cast_commute _ _).left_comm, pow_add,
    mul_assoc, ← mul_assoc ((-1 : R) ^ k), ← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_mul,
    mul_assoc, (Nat.cast_commute _ _).left_comm]

end TauCeti

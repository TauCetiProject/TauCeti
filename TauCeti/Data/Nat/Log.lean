/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Integer logarithms and power-cutoff interval sums

Appending a base-`b` digit `e < b` to a positive natural number `n` raises its integer logarithm
by one: `Nat.log b (b * n + e) = Nat.log b n + 1`. This complements Mathlib's `Nat.log_mul_base`,
which is the case `e = 0` with the factors in the other order.

For any base `p > 1`, restricting a sum over `k ∈ Icc 1 N` to exponents with `p ^ k ≤ N` is
equivalent to summing over `Icc 1 (Nat.log p N)`.

## Main results

* `TauCeti.Nat.log_mul_add`: `Nat.log b (b * n + e) = Nat.log b n + 1` for `n ≠ 0` and `e < b`.
* `Nat.sum_Icc_ite_pow_le_eq_sum_Icc_log`: `∑ k ∈ Icc 1 N, if p ^ k ≤ N then g k else 0` equals
  `∑ k ∈ Icc 1 (p.log N), g k` for `1 < p`.
-/

public section

namespace TauCeti.Nat

/-- Appending a base-`b` digit to a positive number raises its integer logarithm by one. -/
theorem log_mul_add {b n e : ℕ} (hb : 1 < b) (hn : n ≠ 0) (he : e < b) :
    Nat.log b (b * n + e) = Nat.log b n + 1 := by
  have hle : b ≤ b * n + e :=
    (Nat.le_mul_of_pos_right b (Nat.pos_of_ne_zero hn)).trans (Nat.le_add_right _ _)
  rw [Nat.log_of_one_lt_of_le hb hle, Nat.mul_add_div (by omega), Nat.div_eq_of_lt he]
  simp

end TauCeti.Nat

namespace Nat

open Finset

/-- For any base `p > 1`, filtering exponents `k ∈ Icc 1 N` by `p ^ k ≤ N` is equivalent to summing
over `Icc 1 (p.log N)`. -/
theorem sum_Icc_ite_pow_le_eq_sum_Icc_log {M : Type*} [AddCommMonoid M] {p : ℕ} (hp : 1 < p)
    (N : ℕ) (g : ℕ → M) :
    ∑ k ∈ Icc 1 N, (if p ^ k ≤ N then g k else 0) = ∑ k ∈ Icc 1 (p.log N), g k := by
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_Icc]
  refine ⟨fun ⟨⟨hk1, _⟩, hpk⟩ ↦ ⟨hk1, le_log_of_pow_le hp hpk⟩, fun ⟨hk1, hklog⟩ ↦ ?_⟩
  have hN0 : N ≠ 0 := by rintro rfl; simp at hklog; omega
  exact ⟨⟨hk1, hklog.trans (log_le_self p N)⟩, pow_le_of_le_log hN0 hklog⟩

end Nat

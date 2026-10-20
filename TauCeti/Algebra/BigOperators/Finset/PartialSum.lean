/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite partial sums

This file contains basic facts about finite partial sums.

## Main results

* `TauCeti.eq_zero_of_forall_sum_Iic_eq_zero`: a finite sequence whose inclusive partial sums
  all vanish is zero.
* `TauCeti.eq_of_forall_sum_filter_lt_eq`: a finite sequence is determined by its sums over the
  initial segments `{j | (j : ℕ) < m}`.
-/

public section

namespace TauCeti

open Finset

/-- **A finite sequence all of whose inclusive partial sums vanish is zero.** -/
theorem eq_zero_of_forall_sum_Iic_eq_zero {M : Type*} [AddCommMonoid M] (n : ℕ)
    {y : Fin (n + 1) → M} (hy : ∀ k, ∑ j ∈ Iic k, y j = 0) : y = 0 := by
  funext k
  induction k using WellFoundedLT.induction with
  | _ k ih =>
    have h := hy k
    rw [Iic_eq_cons_Iio, sum_cons, sum_eq_zero fun j hj ↦ ih j (mem_Iio.mp hj), add_zero] at h
    exact h

/-- **A finite sequence is determined by its sums over the initial segments** `{j | (j : ℕ) < m}`:
the inclusive partial sums of the difference of two sequences with the same such sums all vanish,
so `TauCeti.eq_zero_of_forall_sum_Iic_eq_zero` applies. -/
theorem eq_of_forall_sum_filter_lt_eq {M : Type*} [AddCommGroup M] {n : ℕ} {y z : Fin n → M}
    (h : ∀ m : ℕ, ∑ j ∈ univ.filter fun j : Fin n => (j : ℕ) < m, y j =
      ∑ j ∈ univ.filter fun j : Fin n => (j : ℕ) < m, z j) :
    y = z := by
  obtain _ | n := n
  · exact funext fun i => i.elim0
  have hIic : ∀ k : Fin (n + 1), ∑ j ∈ Iic k, (y - z) j = 0 := by
    intro k
    have hfilter : Iic k = univ.filter fun j : Fin (n + 1) => (j : ℕ) < (k : ℕ) + 1 := by
      ext j
      simp only [mem_Iic, mem_filter, mem_univ, true_and, Fin.le_def, Nat.lt_succ_iff]
    rw [hfilter]
    simp only [Pi.sub_apply, sum_sub_distrib, h ((k : ℕ) + 1), sub_self]
  funext i
  have hi := congrFun (eq_zero_of_forall_sum_Iic_eq_zero n hIic) i
  simpa only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using hi

end TauCeti

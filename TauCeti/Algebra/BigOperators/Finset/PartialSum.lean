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

end TauCeti

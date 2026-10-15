/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.BigOperators

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Products involving factorials in ordered fields

This file evaluates finite products in ordered fields whose factors stabilize to a simple
factorial quotient. Such products occur as accumulated losses in lattice basis estimates.
-/

public section

namespace TauCeti

open scoped BigOperators

/-- The product of the factors `max 1 ((i + 1) / 2)`, indexed from zero, is the factorial
quotient `n! / 2^(n - 1)`. -/
theorem prod_max_one_add_one_div_two {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (n : ℕ) :
    ∏ i : Fin n, max 1 ((((i : ℕ) : K) + 1) / 2) =
      (n.factorial : K) / 2 ^ (n - 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
      rw [Fin.prod_univ_one, max_eq_left]
      · norm_num
      · exact (div_le_one₀ (by norm_num : (0 : K) < 2)).2 (by norm_num)
  | more n _ ih =>
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      have hmax : max 1 ((((n + 1 : ℕ) : K) + 1) / 2) = ((n + 2 : ℕ) : K) / 2 := by
        have hle : (1 : K) ≤ (((n + 1 : ℕ) : K) + 1) / 2 := by
          apply (le_div_iff₀ (by norm_num : (0 : K) < 2)).2
          push_cast
          linarith [Nat.cast_nonneg (α := K) n]
        rw [max_eq_right hle]
        push_cast
        ring
      have hfac : ((n + 2).factorial : K) =
          ((n + 2 : ℕ) : K) * ((n + 1).factorial : K) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hmax, hfac, Nat.succ_sub_one, Nat.succ_sub_one]
      push_cast
      field_simp
      ring

end TauCeti

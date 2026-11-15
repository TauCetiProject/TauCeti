/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import TauCeti.Combinatorics.NoncrossingPartition.Mobius

/-!
# Exponential bounds on noncrossing Möbius coefficients

The blockwise Catalan formula bounds `‖μ(⊥, π)‖` by `4 ^ |s|`. Kreweras duality gives
the same bound for `‖μ(π, ⊤)‖`. Together with Catalan enumeration, these estimates control
the growth of free cumulants obtained by Möbius inversion.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 10.
-/

public section

open Finset IncidenceAlgebra

namespace TauCeti.NoncrossingPartition

variable {α R : Type*} [LinearOrder α] [NormedCommRing R] [NormOneClass R] {s : Finset α}

/-- A lower-interval Möbius coefficient of `NC(s)` is bounded exponentially in `|s|`. -/
theorem norm_mu_bot_le (π : NoncrossingPartition s) : ‖mu R ⊥ π‖ ≤ (4 : ℝ) ^ #s := by
  rw [mu_bot_eq_prod]
  calc
    ‖∏ B ∈ π.1.parts, (-1 : R) ^ (#B - 1) * catalan (#B - 1)‖
        ≤ ∏ B ∈ π.1.parts, (4 : ℝ) ^ #B := by
      refine (Finset.norm_prod_le _ _).trans
        (prod_le_prod₀ (fun _ _ => norm_nonneg _) fun B _ => ?_)
      calc
        ‖(-1 : R) ^ (#B - 1) * catalan (#B - 1)‖ ≤ (catalan (#B - 1) : ℝ) := by
          have hsign : ‖(-1 : R) ^ (#B - 1)‖ ≤ 1 := by
            simp
          have hcast : ‖(catalan (#B - 1) : R)‖ ≤ (catalan (#B - 1) : ℝ) := by
            simpa using (Nat.norm_cast_le (α := R) (catalan (#B - 1)))
          exact (norm_mul_le _ _).trans
            ((mul_le_mul hsign hcast (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
        _ ≤ (4 : ℝ) ^ (#B - 1) := by exact_mod_cast Nat.catalan_le_four_pow (#B - 1)
        _ ≤ (4 : ℝ) ^ #B := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    _ = (4 : ℝ) ^ #s := by rw [prod_pow_eq_pow_sum, π.1.sum_card_parts]

/-- An upper-interval Möbius coefficient of `NC(n)` satisfies the same exponential bound. -/
theorem norm_mu_top_le {n : ℕ} (π : NoncrossingPartition (univ : Finset (Fin n))) :
    ‖mu R π ⊤‖ ≤ (4 : ℝ) ^ n := by
  rw [mu_top_eq_mu_bot_kreweras]
  simpa using norm_mu_bot_le (R := R) (kreweras π)

end TauCeti.NoncrossingPartition

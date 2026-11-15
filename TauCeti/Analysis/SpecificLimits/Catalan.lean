/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import TauCeti.Combinatorics.Enumerative.Catalan
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Catalan generating function as a convergent series

Mathlib proves the formal identity `catalanSeries ^ 2 * X + 1 = catalanSeries` for the generating
function of the Catalan numbers. Since `catalan n ≤ 4 ^ n`, the series `∑ catalan n * q ^ n`
converges absolutely for `‖q‖ < 1 / 4` in any complete normed ring, and its sum `c`
satisfies the same quadratic equation `c ^ 2 * q + 1 = c`.

This is the form in which the Catalan numbers enter the resolvent transform of the semicircle law:
its expansion at infinity is the Catalan series in `z⁻²`.

## Main results

* `TauCeti.summable_norm_catalan_mul_pow`: absolute convergence for `‖q‖ < 1 / 4`.
* `TauCeti.tsum_catalan_mul_pow_sq_mul_add_one`: the sum `c` satisfies `c ^ 2 * q + 1 = c`.
-/

public section

open Finset

namespace TauCeti

variable {R : Type*} [NormedRing R] {q : R}

/-- The Catalan generating series converges absolutely inside the disc of radius `1 / 4`. -/
theorem summable_norm_catalan_mul_pow (hq : ‖q‖ < 4⁻¹) :
    Summable fun n ↦ ‖(catalan n : R) * q ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    ((summable_geometric_of_lt_one (by positivity) (by linarith : 4 * ‖q‖ < 1)).mul_left
      ‖(1 : R)‖)
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  calc ‖(catalan n : R) * q ^ n‖ ≤ catalan n * ‖(1 : R)‖ * ‖q‖ ^ n :=
        (norm_mul_le _ _).trans (mul_le_mul (Nat.norm_cast_le _) (norm_pow_le' _ hn)
          (by positivity) (by positivity))
    _ ≤ 4 ^ n * ‖(1 : R)‖ * ‖q‖ ^ n := by gcongr; exact_mod_cast Nat.catalan_le_four_pow n
    _ = ‖(1 : R)‖ * (4 * ‖q‖) ^ n := by ring

variable [CompleteSpace R]

/-- The sum `c = ∑ catalan n * q ^ n` of the Catalan generating series satisfies
`c ^ 2 * q + 1 = c` for `‖q‖ < 1 / 4`. -/
theorem tsum_catalan_mul_pow_sq_mul_add_one (hq : ‖q‖ < 4⁻¹) :
    (∑' n, (catalan n : R) * q ^ n) ^ 2 * q + 1 = ∑' n, (catalan n : R) * q ^ n := by
  have hs := summable_norm_catalan_mul_pow hq
  -- The Cauchy square of the series is the shifted series, by the Catalan recurrence.
  have hconv (n : ℕ) : ∑ kl ∈ antidiagonal n, (catalan kl.1 : R) * q ^ kl.1 *
      ((catalan kl.2 : R) * q ^ kl.2) = (catalan (n + 1) : R) * q ^ n := by
    rw [catalan_succ', Nat.cast_sum, sum_mul]
    refine sum_congr rfl fun kl hkl ↦ ?_
    rw [← mem_antidiagonal.1 hkl]
    push_cast
    rw [pow_add, (Nat.cast_commute (catalan kl.2) (q ^ kl.1)).symm.mul_mul_mul_comm]
  have hs' : Summable fun n ↦ (catalan (n + 1) : R) * q ^ n := by
    simpa only [hconv] using
      Summable.of_norm (summable_norm_sum_mul_antidiagonal_of_summable_norm hs hs)
  rw [sq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs hs]
  simp only [hconv]
  rw [(Summable.of_norm hs).tsum_eq_zero_add, ← hs'.tsum_mul_right]
  simp [pow_succ, mul_assoc, add_comm]

end TauCeti

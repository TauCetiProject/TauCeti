/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exponential lattice series

For a positive decay rate `a`, the two-sided exponential is summable over the
integers, and its sum equals `(1 + exp (-a)) / (1 - exp (-a))`.
The analogous one-sided positive tail is an ordinary geometric series.

## Provenance

Adapted from `ForTauCeti/Analysis/Fourier/Poisson/CauchyLattice.lean` in the
AIQ-Kitware DKPS formalization (Apache-2.0; Jon Crall and GPT 5.6 High).
-/

public section

open scoped BigOperators

namespace TauCeti

noncomputable section

/-- The positive tail of a geometric exponential series. -/
theorem tsum_nat_exp_neg_mul_add_one {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, Real.exp (-(a * (n + 1 : ℕ)))) =
      Real.exp (-a) / (1 - Real.exp (-a)) := by
  let q := Real.exp (-a)
  have hqnorm : ‖q‖ < 1 := by
    dsimp only [q]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
  calc
    (∑' n : ℕ, Real.exp (-(a * (n + 1 : ℕ)))) =
        ∑' n : ℕ, q ^ (n + 1) := by
      apply tsum_congr
      intro n
      -- The summand is the geometric power given by `Real.exp_nat_mul`.
      dsimp only [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = ∑' n : ℕ, q ^ n * q := by simp_rw [pow_succ]
    _ = (∑' n : ℕ, q ^ n) * q := tsum_mul_right
    _ = (1 - q)⁻¹ * q := by rw [tsum_geometric_of_norm_lt_one hqnorm]
    _ = Real.exp (-a) / (1 - Real.exp (-a)) := by
      simp only [q, div_eq_mul_inv]
      ring

/-- The two-sided exponential with positive rate is summable on the integer lattice. -/
theorem summable_exp_neg_mul_abs_int {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-(a * |(n : ℝ)|))) := by
  -- Mathlib already characterizes summability of natural-index exponentials.
  have hnat : Summable (fun n : ℕ => Real.exp (-(a * (n : ℝ)))) := by
    refine (Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos ha)).congr
      (fun n => ?_)
    congr 1
    ring
  apply Summable.of_nat_of_neg
  · simpa using hnat
  · simpa using hnat

/-- The two-sided geometric lattice sum of a decaying exponential. -/
theorem tsum_int_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, Real.exp (-(a * |(n : ℝ)|))) =
      (1 + Real.exp (-a)) / (1 - Real.exp (-a)) := by
  let f : ℤ → ℝ := fun n => Real.exp (-(a * |(n : ℝ)|))
  have hsum : Summable f := summable_exp_neg_mul_abs_int ha
  have heven : Function.Even f := by
    intro n
    simp only [f, Int.cast_neg, abs_neg]
  have hpnat :
      (∑' n : ℕ+, f (n : ℤ)) =
        ∑' n : ℕ, Real.exp (-(a * (n + 1 : ℕ))) := by
    simpa [f] using
      (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => Real.exp (-(a * (n : ℝ)))))
  calc
    (∑' n : ℤ, Real.exp (-(a * |(n : ℝ)|))) =
        f 0 + 2 • ∑' n : ℕ+, f (n : ℤ) :=
      tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsum
    _ = 1 + 2 * (Real.exp (-a) / (1 - Real.exp (-a))) := by
      rw [hpnat, tsum_nat_exp_neg_mul_add_one ha]
      simp [f]
    _ = (1 + Real.exp (-a)) / (1 - Real.exp (-a)) := by
      have hne : 1 - Real.exp (-a) ≠ 0 :=
        (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha))).ne'
      field_simp [hne]
      ring


end

end TauCeti

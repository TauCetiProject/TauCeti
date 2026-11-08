/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.BigOperators.Sum.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bounds on products of pairwise distances

Products of powers of pairwise distances admit a bound in terms of coordinate magnitudes.
-/

public section

open Real

namespace Finset

/-- Bound a product of powered pairwise distances by a product of coordinate magnitudes. -/
theorem prod_abs_sub_rpow_le_prod_one_add_abs_rpow {ι : Type*} [Fintype ι]
    {β : ℝ} (hβ : 0 ≤ β) (x : ι → ℝ) (pairs : Finset (ι × ι)) :
    (∏ z ∈ pairs, |x z.1 - x z.2| ^ β) ≤
      (∏ i : ι, (1 + |x i|)) ^ (2 * (β * (pairs.card : ℝ))) := by
  classical
  set p : ℝ := 2 * (β * (pairs.card : ℝ)) with hp_def
  let q : ℝ := ∏ i : ι, (1 + |x i|)
  have hqsum : 1 + ∑ i : ι, |x i| ≤ q := by
    simpa [q] using Finset.one_add_sum_le_prod_one_add (Finset.univ : Finset ι)
      (fun i => |x i|) (fun _ _ => abs_nonneg _)
  have hqone : 1 ≤ q := by
    have hsum : 0 ≤ ∑ i : ι, |x i| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hqnonneg : 0 ≤ q := by linarith [hqone]
  have hqpow : q ^ 2 ≥ 1 + 2 * ∑ i : ι, |x i| := by
    nlinarith [hqsum, hqone]
  have hpair : ∀ z ∈ pairs, |x z.1 - x z.2| ≤ q ^ 2 := by
    intro z hz
    have hi : |x z.1| ≤ ∑ i : ι, |x i| :=
      Finset.single_le_sum (f := fun i : ι => |x i|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    have hj : |x z.2| ≤ ∑ i : ι, |x i| :=
      Finset.single_le_sum (f := fun i : ι => |x i|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    have hdist := abs_sub_le (x z.1) 0 (x z.2)
    simp only [sub_zero, zero_sub, abs_neg] at hdist
    have hnonneg : 0 ≤ ∑ i : ι, |x i| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    nlinarith
  have hvander : (∏ z ∈ pairs, |x z.1 - x z.2| ^ β) ≤ q ^ p := by
    calc
      _ ≤ ∏ z ∈ pairs, (q ^ 2) ^ β := by
        apply Finset.prod_le_prod₀
          (fun z hz => by positivity)
          (fun z hz => Real.rpow_le_rpow (abs_nonneg _) (hpair z hz) hβ)
      _ = ((q ^ 2) ^ β) ^ (pairs.card : ℕ) := by
        simp [Finset.prod_const]
      _ = q ^ (2 * (β * (pairs.card : ℝ))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ q ^ 2),
          ← Real.rpow_natCast q 2, ← Real.rpow_mul hqnonneg]
        norm_num
      _ = q ^ p := by
        rw [hp_def]
  exact hvander

end Finset

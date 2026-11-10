/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Summability of products over a finite power

If `f : β → ℝ` is nonnegative and summable, then so is `k ↦ ∏ i, f (k i)` on `ι → β` for a
finite type `ι`, with sum at most `(∑' b, f b) ^ card ι`. For instance a weight
`∏ᵢ (1 + |kᵢ|)⁻²` on the lattice `ℤⁿ` is summable because `(1 + |m|)⁻²` is summable on `ℤ`.

## Main results

* `summable_prod_pi_of_nonneg`: the summability of `k ↦ ∏ i, f (k i)`.
-/

public section

open Finset

/-- If `f : β → ℝ` is nonnegative and summable, then so is `k ↦ ∏ i, f (k i)` on `ι → β` for a
finite type `ι`. -/
theorem summable_prod_pi_of_nonneg {ι β : Type*} [Fintype ι] {f : β → ℝ} (hf : Summable f)
    (h0 : 0 ≤ f) : Summable fun k : ι → β ↦ ∏ i, f (k i) := by
  classical
  refine summable_of_sum_le (c := (∑' b, f b) ^ Fintype.card ι)
    (fun k ↦ prod_nonneg fun i _ ↦ h0 _) fun s ↦ ?_
  calc ∑ k ∈ s, ∏ i, f (k i)
      ≤ ∑ k ∈ Fintype.piFinset fun i ↦ s.image (· i), ∏ i, f (k i) :=
        sum_le_sum_of_subset_of_nonneg
          (fun k hk ↦ Fintype.mem_piFinset.2 fun i ↦ mem_image_of_mem _ hk)
          fun k _ _ ↦ prod_nonneg fun i _ ↦ h0 _
    _ = ∏ i, ∑ b ∈ s.image (· i), f b := (prod_univ_sum _ _).symm
    _ ≤ ∏ _i : ι, ∑' b, f b :=
        prod_le_prod₀ (fun i _ ↦ sum_nonneg fun b _ ↦ h0 b)
          fun i _ ↦ hf.sum_le_tsum _ fun b _ ↦ h0 b
    _ = (∑' b, f b) ^ Fintype.card ι := by rw [prod_const, card_univ]

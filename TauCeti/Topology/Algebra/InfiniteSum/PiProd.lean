/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Summability of products over a finite power

If `f i : κ i → ℝ` is nonnegative and summable for every `i` in a finite type `ι`, then so is
`k ↦ ∏ i, f i (k i)` on `∀ i, κ i`. For instance a weight `∏ᵢ (1 + |kᵢ|)⁻²` on the lattice `ℤⁿ`
is summable because `(1 + |m|)⁻²` is summable on `ℤ`.

## Main results

* `Summable.prod_pi_of_nonneg`: the summability of `k ↦ ∏ i, f i (k i)`.
-/

public section

open Finset

/-- If `f i : κ i → ℝ` is nonnegative and summable for every `i` in a finite type `ι`, then so is
`k ↦ ∏ i, f i (k i)` on `∀ i, κ i`. -/
protected theorem Summable.prod_pi_of_nonneg {ι : Type*} {κ : ι → Type*} [Fintype ι]
    {f : ∀ i, κ i → ℝ} (hf : ∀ i, Summable (f i)) (h0 : ∀ i, 0 ≤ f i) :
    Summable fun k : ∀ i, κ i ↦ ∏ i, f i (k i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' b, f i b)
    (fun k ↦ prod_nonneg fun i _ ↦ h0 i _) fun s ↦ ?_
  calc ∑ k ∈ s, ∏ i, f i (k i)
      ≤ ∑ k ∈ Fintype.piFinset fun i ↦ s.image (· i), ∏ i, f i (k i) :=
        sum_le_sum_of_subset_of_nonneg
          (fun k hk ↦ Fintype.mem_piFinset.2 fun i ↦ mem_image_of_mem _ hk)
          fun k _ _ ↦ prod_nonneg fun i _ ↦ h0 i _
    _ = ∏ i, ∑ b ∈ s.image (· i), f i b := (prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' b, f i b :=
        prod_le_prod₀ (fun i _ ↦ sum_nonneg fun b _ ↦ h0 i b)
          fun i _ ↦ (hf i).sum_le_tsum _ fun b _ ↦ h0 i b

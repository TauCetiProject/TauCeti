/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Multi-index binomial coefficients

For multi-indices `d m : σ →₀ ℕ`, the multi-index binomial coefficient is
`d.prod fun j k ↦ (m j).choose k = ∏ⱼ (mⱼ choose dⱼ)`. It is the coefficient by which the Hasse
derivative `∂^d` scales the monomial `X^m`.

## Main results

* `Finsupp.prod_choose_eq_zero_iff`: the coefficient vanishes if and only if `¬d ≤ m`.
* `Finsupp.prod_choose_add_single`: Pascal's rule in a single coordinate `i`.
* `Finsupp.prod_choose_add_comm`: `∏ⱼ (aⱼ + bⱼ choose aⱼ)` is symmetric in `a` and `b`.
* `Finsupp.prod_choose_le_two_pow_degree`: the coefficient is at most `2 ^ |m|`.
-/

public section

namespace Finsupp

variable {σ : Type*}

/-- The multi-index binomial coefficient `∏ⱼ (mⱼ choose dⱼ)` vanishes if and only if
`¬d ≤ m`. -/
theorem prod_choose_eq_zero_iff {d m : σ →₀ ℕ} :
    (d.prod fun j k ↦ (m j).choose k) = 0 ↔ ¬d ≤ m := by
  simp only [prod_eq_zero_iff, mem_support_iff, Nat.choose_eq_zero_iff, le_def, not_forall,
    not_le]
  exact ⟨fun ⟨j, _, hj⟩ ↦ ⟨j, hj⟩, fun ⟨j, hj⟩ ↦ ⟨j, by omega, hj⟩⟩

/-- Pascal's rule for the multi-index binomial coefficient, in the coordinate `i`:
raising `nᵢ` by one adds the coefficient with `dᵢ` lowered by one, when `dᵢ ≠ 0`. -/
theorem prod_choose_add_single (n d : σ →₀ ℕ) (i : σ) :
    (d.prod fun j k ↦ ((n + single i 1 : σ →₀ ℕ) j).choose k) =
      (d.prod fun j k ↦ (n j).choose k) +
        if d i = 0 then 0 else (d - single i 1).prod fun j k ↦ (n j).choose k := by
  classical
  -- each product may be taken over `d.support`, since `choose · 0 = 1`
  have h0 (f : σ → ℕ) : ∀ j ∈ d.support, (f j).choose 0 = 1 := fun _ _ ↦ Nat.choose_zero_right _
  rw [prod_of_support_subset d subset_rfl _ (h0 _), prod_of_support_subset d subset_rfl _ (h0 _)]
  split_ifs with hi
  · rw [add_zero]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    have hij : i ≠ j := fun h ↦ mem_support_iff.1 (h ▸ hj) hi
    simp [hij]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hi
    replace hi := mem_support_iff.2 hi
    rw [prod_of_support_subset _ support_tsub _ (h0 _), ← Finset.mul_prod_erase _ _ hi,
      ← Finset.mul_prod_erase _ _ hi, ← Finset.mul_prod_erase _ _ hi]
    have h1 : ∏ j ∈ d.support.erase i, ((n + single i 1 : σ →₀ ℕ) j).choose (d j) =
        ∏ j ∈ d.support.erase i, (n j).choose (d j) :=
      Finset.prod_congr rfl fun j hj ↦ by simp [Finset.ne_of_mem_erase hj]
    have h2 : ∏ j ∈ d.support.erase i, (n j).choose ((d - single i 1 : σ →₀ ℕ) j) =
        ∏ j ∈ d.support.erase i, (n j).choose (d j) :=
      Finset.prod_congr rfl fun j hj ↦ by simp [Finset.ne_of_mem_erase hj]
    rw [h1, h2, ← add_mul]
    congr 1
    -- at `i`, this is Pascal's rule `(nᵢ + 1).choose (k + 1) = nᵢ.choose k + nᵢ.choose (k + 1)`
    simpa [hk, add_comm] using Nat.choose_succ_succ' (n i) k

/-- The multi-index binomial coefficient `∏ⱼ (aⱼ + bⱼ choose aⱼ)` is symmetric in `a` and `b`. -/
theorem prod_choose_add_comm (a b : σ →₀ ℕ) :
    (a.prod fun j k ↦ (k + b j).choose k) = b.prod fun j k ↦ (k + a j).choose k := by
  classical
  rw [Finsupp.prod_of_support_subset a Finset.subset_union_left (fun j k ↦ (k + b j).choose k)
      (fun _ _ ↦ Nat.choose_zero_right _),
    Finsupp.prod_of_support_subset b (Finset.subset_union_right (s₁ := a.support))
      (fun j k ↦ (k + a j).choose k) (fun _ _ ↦ Nat.choose_zero_right _)]
  exact Finset.prod_congr rfl fun j _ ↦ by rw [Nat.choose_symm_add, add_comm]

/-- The multi-index binomial coefficient `∏ⱼ (mⱼ choose dⱼ)` is at most `2 ^ |m|`, where
`|m| = ∑ⱼ mⱼ` is the degree of `m`. -/
theorem prod_choose_le_two_pow_degree (d m : σ →₀ ℕ) :
    (d.prod fun j k ↦ (m j).choose k) ≤ 2 ^ m.degree :=
  calc (d.prod fun j k ↦ (m j).choose k)
      ≤ ∏ j ∈ d.support, 2 ^ m j :=
        Finset.prod_le_prod fun j _ ↦ Nat.choose_le_two_pow (m j) (d j)
    _ = 2 ^ ∑ j ∈ d.support, m j := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ 2 ^ m.degree := by
      rw [degree_apply]
      exact Nat.pow_le_pow_right two_pos
        (Finset.sum_le_sum_of_ne_zero fun j _ hj ↦ mem_support_iff.2 hj)

end Finsupp

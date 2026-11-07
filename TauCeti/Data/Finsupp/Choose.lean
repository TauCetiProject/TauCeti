/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Choose.Sum
public import TauCeti.Data.Finsupp.Interval

/-!
# Multi-index binomial coefficients

For multi-indices `d m : σ →₀ ℕ`, the multi-index binomial coefficient is
`d.prod fun j k ↦ (m j).choose k = ∏ⱼ (mⱼ choose dⱼ)`. It is the coefficient by which the Hasse
derivative `∂^d` scales the monomial `X^m`.

## Main results

* `Finsupp.prod_choose_eq_zero`: the coefficient vanishes unless `d ≤ m`.
* `Finsupp.prod_choose_add_single`: Pascal's rule in a single coordinate `i`.
* `Finsupp.prod_choose_add_comm`: `∏ⱼ (aⱼ + bⱼ choose aⱼ)` is symmetric in `a` and `b`.
* `Finsupp.prod_choose_le_two_pow_degree`: the coefficient is at most `2 ^ |m|`.
* `Finsupp.prod_add_pow`: multi-index binomial expansion of `∏ⱼ (xⱼ + yⱼ) ^ γⱼ` over `β ≤ γ`.
-/

public section

namespace Finsupp

variable {σ : Type*}

/-- The multi-index binomial coefficient `∏ⱼ (mⱼ choose dⱼ)` vanishes unless `d ≤ m`. -/
theorem prod_choose_eq_zero {d m : σ →₀ ℕ} (h : ¬d ≤ m) :
    (d.prod fun j k ↦ (m j).choose k) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, m j < d j := by simpa [Finsupp.le_def] using h
  exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 (by omega)) (Nat.choose_eq_zero_of_lt hj)

/-- Pascal's rule for the multi-index binomial coefficient, in the coordinate `i`:
raising `nᵢ` by one adds the coefficient with `dᵢ` lowered by one, when `dᵢ ≠ 0`. -/
theorem prod_choose_add_single (n d : σ →₀ ℕ) (i : σ) :
    (d.prod fun j k ↦ ((n + single i 1 : σ →₀ ℕ) j).choose k) =
      (d.prod fun j k ↦ (n j).choose k) +
        if d i = 0 then 0 else (d - single i 1).prod fun j k ↦ (n j).choose k := by
  classical
  rw [Finsupp.prod_of_support_subset d subset_rfl
      (fun j k ↦ ((n + single i 1 : σ →₀ ℕ) j).choose k)
      (fun _ _ ↦ Nat.choose_zero_right _),
    Finsupp.prod_of_support_subset d subset_rfl (fun j k ↦ (n j).choose k)
      (fun _ _ ↦ Nat.choose_zero_right _)]
  split_ifs with hi
  · rw [add_zero]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    have hij : i ≠ j := fun h ↦ Finsupp.mem_support_iff.1 (h ▸ hj) hi
    simp [hij]
  · replace hi := Finsupp.mem_support_iff.2 hi
    rw [Finsupp.prod_of_support_subset _ support_tsub (fun j k ↦ (n j).choose k)
        (fun _ _ ↦ Nat.choose_zero_right _),
      ← Finset.mul_prod_erase _ _ hi,
      ← Finset.mul_prod_erase _ _ hi, ← Finset.mul_prod_erase _ _ hi]
    have h1 : ∏ j ∈ d.support.erase i, ((n + single i 1 : σ →₀ ℕ) j).choose (d j) =
        ∏ j ∈ d.support.erase i, (n j).choose (d j) :=
      Finset.prod_congr rfl fun j hj ↦ by simp [Finset.ne_of_mem_erase hj]
    have h2 : ∏ j ∈ d.support.erase i, (n j).choose ((d - single i 1 : σ →₀ ℕ) j) =
        ∏ j ∈ d.support.erase i, (n j).choose (d j) :=
      Finset.prod_congr rfl fun j hj ↦ by simp [Finset.ne_of_mem_erase hj]
    rw [h1, h2, ← add_mul]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero (Finsupp.mem_support_iff.1 hi)
    congr 1
    rw [Finsupp.add_apply, tsub_apply, single_eq_same, hk, Nat.add_sub_cancel,
      Nat.choose_succ_succ', add_comm]

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
    (d.prod fun j k ↦ (m j).choose k) ≤ 2 ^ m.degree := by
  by_cases hdm : d ≤ m
  · calc (d.prod fun j k ↦ (m j).choose k)
        ≤ ∏ j ∈ d.support, 2 ^ m j :=
          Finset.prod_le_prod fun j _ ↦ Nat.choose_le_two_pow (m j) (d j)
      _ ≤ ∏ j ∈ m.support, 2 ^ m j :=
          Finset.prod_le_prod_of_subset_of_one_le (support_mono hdm)
            fun _ _ _ ↦ Nat.one_le_two_pow
      _ = 2 ^ m.degree := by rw [Finset.prod_pow_eq_pow_sum, degree_apply]
  · rw [prod_choose_eq_zero hdm]
    exact Nat.zero_le _

open Classical in
/-- Multi-index binomial theorem: `∏ⱼ (xⱼ + yⱼ) ^ γⱼ` expands over `β ≤ γ` into
`∏ⱼ (γⱼ choose βⱼ) xⱼ ^ βⱼ yⱼ ^ (γⱼ - βⱼ)`. -/
theorem prod_add_pow {R : Type*} [CommSemiring R] (x y : σ → R) (γ : σ →₀ ℕ) :
    (γ.prod fun j k ↦ (x j + y j) ^ k) =
      ∑ β ∈ Finset.Iic γ,
        γ.prod fun j k ↦ (k.choose (β j) : R) * x j ^ β j * y j ^ (k - β j) := by
  classical
  induction γ using Finsupp.induction with
  | zero =>
    have h0 : Finset.Iic (0 : σ →₀ ℕ) = {0} := Finset.Iic_bot
    simp [h0]
  | single_add j k s hj hk ih =>
    -- Split the product at coordinate `j`, apply the univariate binomial theorem on `j`, and
    -- reindex `(m, β') ∈ Iic k ×ˢ Iic s` along `single j m + β' ∈ Iic (single j k + s)`.
    rw [Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _),
      Finsupp.prod_single_index (h := fun i n ↦ (x i + y i) ^ n) (pow_zero _), add_pow,
      Nat.range_succ_eq_Iic, ih, Finset.sum_mul_sum, Finsupp.sum_Iic_single_add k hj]
    refine Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun β' hβ' ↦ ?_
    have hsj : s j = 0 := notMem_support_iff.1 hj
    have hβ'j : β' j = 0 := nonpos_iff_eq_zero.1 ((Finset.mem_Iic.1 hβ' j).trans_eq hsj)
    rw [Finsupp.prod, Finsupp.prod, Finsupp.support_single_add hj hk, Finset.prod_cons]
    congr 1
    · simp only [Finsupp.add_apply, single_eq_same, hsj, hβ'j, add_zero]
      ac_rfl
    · refine Finset.prod_congr rfl fun i hi ↦ ?_
      have hij : j ≠ i := fun h ↦ hj (h ▸ hi)
      simp [hij]

end Finsupp

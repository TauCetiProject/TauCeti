/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Multi-index binomial coefficients

For multi-indices `d m : σ →₀ ℕ`, the multi-index binomial coefficient is
`d.prod fun j k ↦ (m j).choose k = ∏ⱼ (mⱼ choose dⱼ)`. It is the coefficient by which the Hasse
derivative `∂^d` scales the monomial `X^m`.

## Main results

* `Finsupp.prod_choose_eq_zero`: the coefficient vanishes unless `d ≤ m`.
* `Finsupp.prod_choose_eq_prod`: it is a product over any finite set containing the support of
  `d`.
* `Finsupp.prod_choose_add_single`: Pascal's rule in a single coordinate `i`.
-/

public section

namespace Finsupp

variable {σ : Type*}

/-- The multi-index binomial coefficient `∏ⱼ (mⱼ choose dⱼ)` vanishes unless `d ≤ m`. -/
theorem prod_choose_eq_zero {d m : σ →₀ ℕ} (h : ¬d ≤ m) :
    (d.prod fun j k ↦ (m j).choose k) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, m j < d j := by simpa [Finsupp.le_def] using h
  exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 (by omega)) (Nat.choose_eq_zero_of_lt hj)

/-- The multi-index binomial coefficient as a product over any finite set of indices containing
the support of the lower index. -/
theorem prod_choose_eq_prod {d : σ →₀ ℕ} (m : σ →₀ ℕ) {s : Finset σ}
    (hs : d.support ⊆ s) : (d.prod fun j k ↦ (m j).choose k) = ∏ j ∈ s, (m j).choose (d j) :=
  Finsupp.prod_of_support_subset _ hs _ fun _ _ ↦ Nat.choose_zero_right _

/-- Pascal's rule for the multi-index binomial coefficient, in the coordinate `i`:
raising `nᵢ` by one adds the coefficient with `dᵢ` lowered by one, when `dᵢ ≠ 0`. -/
theorem prod_choose_add_single (n d : σ →₀ ℕ) (i : σ) :
    (d.prod fun j k ↦ ((n + single i 1 : σ →₀ ℕ) j).choose k) =
      (d.prod fun j k ↦ (n j).choose k) +
        if d i = 0 then 0 else (d - single i 1).prod fun j k ↦ (n j).choose k := by
  classical
  rw [prod_choose_eq_prod _ subset_rfl, prod_choose_eq_prod _ subset_rfl]
  split_ifs with hi
  · rw [add_zero]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    have hij : i ≠ j := fun h ↦ Finsupp.mem_support_iff.1 (h ▸ hj) hi
    simp [hij]
  · replace hi := Finsupp.mem_support_iff.2 hi
    rw [prod_choose_eq_prod _ support_tsub, ← Finset.mul_prod_erase _ _ hi,
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

end Finsupp

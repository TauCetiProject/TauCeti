/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Filtered products

Weakening the condition `P` of a filtered product over `s` to `P i ∨ i = c`, for a point `c`
with `¬P c`, multiplies the product by the factor at `c` exactly when `c ∈ s`. This is the
bookkeeping that adds a closed endpoint to a sum over the points of a finite set in an open
interval.

For a family `u` of square roots of `1` with levels `k : ι → ℕ`, the products
`∏_{i ∈ s} u i ^ (k i - j)` for all `j` determine the products of the `u i` of each level `m ≥ 1`:
if they all equal one, so do the level products.

## Main results

* `Finset.prod_filter_or_eq_of_not`, `Finset.sum_filter_or_eq_of_not`: adjoining one point to
  the condition of a filtered product or sum.
* `Finset.prod_filter_eq_one_of_forall_prod_pow_tsub_eq_one`: the level products of square roots
  of `1` are trivial when all their truncated power products are.
-/

public section

namespace TauCeti

/-- Adjoining a point `c` with `¬P c` to the condition `P` of a filtered product over `s`
multiplies it by the factor at `c` exactly when `c ∈ s`. -/
@[to_additive /-- Adjoining a point `c` with `¬P c` to the condition `P` of a filtered sum over
`s` adds the term at `c` exactly when `c ∈ s`. -/]
theorem _root_.Finset.prod_filter_or_eq_of_not {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (s : Finset ι) (f : ι → M) (P : ι → Prop) [DecidablePred P] {c : ι} (hc : ¬P c) :
    ∏ i ∈ s with P i ∨ i = c, f i = (∏ i ∈ s with P i, f i) * if c ∈ s then f c else 1 := by
  rw [Finset.filter_or, Finset.prod_union (Finset.disjoint_filter.mpr fun i _ hi (hic : i = c) =>
    hc (hic ▸ hi)), Finset.filter_eq']
  split_ifs <;> simp

/-- If `u i ^ 2 = 1` whenever `0 < k i`, and `∏_{i ∈ s} u i ^ (k i - j) = 1` for every `j`, then
the product of the `u i` with `k i = m` is `1` for every `m ≥ 1`. Multiplying the identities at
`j = m - 1` and `j = m` isolates the product over `k i ≥ m`, and the product over `k i = m` is a
quotient of two such. -/
theorem _root_.Finset.prod_filter_eq_one_of_forall_prod_pow_tsub_eq_one {ι M : Type*}
    [CommMonoid M] (s : Finset ι) (k : ι → ℕ) (u : ι → M) (hu : ∀ i ∈ s, 0 < k i → u i ^ 2 = 1)
    (h : ∀ j, ∏ i ∈ s, u i ^ (k i - j) = 1) {m : ℕ} (hm : 0 < m) :
    ∏ i ∈ s with k i = m, u i = 1 := by
  have hT (m : ℕ) (hm : 0 < m) : ∏ i ∈ s with m ≤ k i, u i = 1 := by
    calc ∏ i ∈ s with m ≤ k i, u i = ∏ i ∈ s, u i ^ ((k i - (m - 1)) + (k i - m)) := by
          rw [Finset.prod_filter]
          refine Finset.prod_congr rfl fun i hi ↦ ?_
          split_ifs with hmi
          · rw [show k i - (m - 1) + (k i - m) = 2 * (k i - m) + 1 by omega, pow_succ, pow_mul,
              hu i hi (by omega), one_pow, one_mul]
          · rw [show k i - (m - 1) + (k i - m) = 0 by omega, pow_zero]
      _ = 1 := by simp only [pow_add, Finset.prod_mul_distrib, h, one_mul]
  have h₁ : (s.filter (m ≤ k ·)).filter (k · = m) = s.filter (k · = m) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun i _ ↦ by omega
  have h₂ : (s.filter (m ≤ k ·)).filter (fun i ↦ ¬k i = m) = s.filter (m + 1 ≤ k ·) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun i _ ↦ by omega
  have hsplit := Finset.prod_filter_mul_prod_filter_not (s.filter (m ≤ k ·)) (k · = m) u
  rwa [h₁, h₂, hT m hm, hT (m + 1) m.succ_pos, mul_one] at hsplit

end TauCeti

/-
Copyright (c) 2026 Ralf Stephan and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan, The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Intervals

/-!
# Product bounds for minima of finite sequences

For a positive increasing sequence, a product of pairwise minima is bounded by the product
of the first entries. If all first indices lie above a cut and some second index lies below
it, the bound gains the ratio across the cut. This retains a jump between consecutive minima
when estimating permutation products in exterior-power determinants.

Such a jump exists wherever the sequence grows over a range: the smallest of the consecutive
ratios `f k / f (k + 1)` for `m ≤ k < n` is at most their geometric mean, the `(n - m)`-th root
of the telescoped ratio `f m / f n` (`TauCeti.exists_mem_Ico_div_pow_le_div`).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §7.5.30.
  The geometric-mean choice of a jump is (7.41) there.
* `TauCeti.prod_min_le_div_mul_prod` is adapted from Ralf Stephan's
  `DiophantineApproximation/WedgeDomain.lean` in
  `rwst/Subspace-Theorems`, commit `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0).
-/

public section

open Finset

namespace TauCeti

/-- A product of pairwise minima gains the ratio across the first `k` indices when every
first index is above the cut and some second index is below it. -/
theorem prod_min_le_div_mul_prod {K ι : Type*} [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] [Fintype ι] {N k : ℕ} {μ : ℕ → K}
    (hμm : MonotoneOn μ (Set.Iio N)) (hμp : ∀ j < N, 0 < μ j)
    {i j : ι → ℕ} (hi : ∀ b, i b < N) (hj : ∀ b, j b < N)
    (h : ∀ b, k ≤ i b) (hk : ∃ b, j b < k) :
    ∏ b, min (μ (i b)) (μ (j b)) ≤ μ (k - 1) / μ k * ∏ b, μ (i b) := by
  classical
  have hm0 (b) : 0 ≤ min (μ (i b)) (μ (j b)) :=
    le_min (hμp _ (hi b)).le (hμp _ (hj b)).le
  obtain ⟨b₀, hb₀⟩ := hk
  have hkN : k < N := (h b₀).trans_lt (hi b₀)
  have hk0 : 0 < μ k := hμp k hkN
  have hr : 0 ≤ μ (k - 1) / μ k := div_nonneg (hμp _ (by omega)).le hk0.le
  rw [← mul_prod_erase _ _ (mem_univ b₀),
    ← mul_prod_erase _ (fun b ↦ μ (i b)) (mem_univ b₀), ← mul_assoc]
  refine mul_le_mul ?_ (prod_le_prod₀ (fun b _ ↦ hm0 b) fun b _ ↦ min_le_left _ _)
    (prod_nonneg fun b _ ↦ hm0 b) (mul_nonneg hr (hμp _ (hi b₀)).le)
  calc
    min (μ (i b₀)) (μ (j b₀)) ≤ μ (j b₀) := min_le_right _ _
    _ ≤ μ (k - 1) := hμm (hj b₀) (by simp only [Set.mem_Iio]; omega) (by omega)
    _ = μ (k - 1) / μ k * μ k := (div_mul_cancel₀ _ hk0.ne').symm
    _ ≤ μ (k - 1) / μ k * μ (i b₀) :=
      mul_le_mul_of_nonneg_left (hμm hkN (hi b₀) (h b₀)) hr

/-- **Some consecutive ratio is at most the geometric mean.** For a sequence positive on
`[m, n]` with `m < n`, some `k` with `m ≤ k < n` has `(f k / f (k + 1)) ^ (n - m) ≤ f m / f n`:
the smallest of the `n - m` consecutive ratios, raised to the power `n - m`, is at most their
product, which telescopes to `f m / f n`. -/
theorem exists_mem_Ico_div_pow_le_div {K : Type*} [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] {f : ℕ → K} {m n : ℕ} (hmn : m < n)
    (hf : ∀ i ∈ Icc m n, 0 < f i) :
    ∃ k ∈ Ico m n, (f k / f (k + 1)) ^ (n - m) ≤ f m / f n := by
  have hpos (i : ℕ) (hi : i ∈ Ico m n) : 0 < f i / f (i + 1) := by
    rw [mem_Ico] at hi
    exact div_pos (hf i (mem_Icc.2 ⟨hi.1, hi.2.le⟩)) (hf (i + 1) (mem_Icc.2 ⟨by omega, hi.2⟩))
  -- The consecutive ratios telescope.
  have htel (j : ℕ) (hmj : m ≤ j) (hjn : j ≤ n) :
      ∏ i ∈ Ico m j, f i / f (i + 1) = f m / f j := by
    induction j, hmj using Nat.le_induction with
    | base => rw [Ico_self, prod_empty, div_self (hf m (mem_Icc.2 ⟨le_rfl, hmn.le⟩)).ne']
    | succ j hmj ih =>
      rw [prod_Ico_succ_top hmj, ih (by omega),
        div_mul_div_cancel₀ (hf j (mem_Icc.2 ⟨hmj, by omega⟩)).ne']
  obtain ⟨k, hk, hmin⟩ := (Ico m n).exists_min_image (fun i ↦ f i / f (i + 1)) (nonempty_Ico.2 hmn)
  refine ⟨k, hk, ?_⟩
  calc (f k / f (k + 1)) ^ (n - m) = ∏ _i ∈ Ico m n, f k / f (k + 1) := by
        rw [prod_const, Nat.card_Ico]
    _ ≤ ∏ i ∈ Ico m n, f i / f (i + 1) :=
        prod_le_prod₀ (fun _ _ ↦ (hpos k hk).le) fun i hi ↦ hmin i hi
    _ = f m / f n := htel n hmn.le le_rfl

end TauCeti

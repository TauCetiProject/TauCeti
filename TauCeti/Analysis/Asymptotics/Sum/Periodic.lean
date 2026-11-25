/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.PSeries
import TauCeti.Algebra.BigOperators.Finset.Periodic
import TauCeti.Algebra.BigOperators.Module
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Norm bounds and zero-mean criterion for periodic partial sums

For a sequence `a : ℕ → M` that is `N`-periodic on positive indices (`a (k + N) = a k` for all
`1 ≤ k`), vanishing of the period sum `∑ j ∈ Icc 1 N, a j` makes the partial sums
`m ↦ ∑ j ∈ Icc 1 m, a j` periodic on all of `ℕ` (`Finset.periodic_sum_Icc_of_sum_eq_zero`), hence
uniformly bounded in norm by `∑ j ∈ Icc 1 N, ‖a j‖` whenever `N ≠ 0`. Conversely, in any normed
vector space over `ℝ`, if `a` is `N`-periodic on `k ≥ 1` and its partial sums are `O(1)`, then the
full-period sums `m • ∑ j ∈ Icc 1 N, a j` remain bounded as `m → ∞`, forcing the period sum to
vanish.

For a complex sequence `a : ℕ → ℂ` that is `N`-periodic on `k ≥ 1` (`N ≠ 0`) with vanishing period
sum `∑ k ∈ Icc 1 N, a k = 0` — such as a nontrivial Dirichlet character or the norm coefficients of
a nontrivial ray class character over a degree-one number field — a single summation by parts
against `k ^ (-z)` with `Re z = 0` would lose a logarithm
(`∑_{k ≤ n} ‖(k + 1) ^ (-i t) - k ^ (-i t)‖` grows like `|t| log n`). Subtracting the period
average of the first partial sums makes the second partial sums bounded too, and second-order
summation by parts (`Finset.sum_Icc_add_two_by_parts'_sub`) against the `O(k⁻²)` second difference
of `k ↦ k ^ (-z)` recovers a uniform `O(1)` bound on `∑ k ∈ Icc 1 n, a k * k ^ (-z)` for every `z`
with `0 ≤ z.re`. The half-plane `0 ≤ z.re` is sharp: for `z.re < 0` and `a k = (-1) ^ k` (`N = 2`),
the `n`-th summand itself has norm `n ^ (-z.re) → ∞`, so the partial sums cannot be bounded.

## Main results

* `Finset.norm_sum_Icc_le_of_sum_eq_zero`: if `N ≠ 0`, `a (k + N) = a k` for `k ≥ 1`, and
  `∑ j ∈ Icc 1 N, a j = 0`, then `‖∑ j ∈ Icc 1 m, a j‖ ≤ ∑ j ∈ Icc 1 N, ‖a j‖` for all `m : ℕ`.
* `TauCeti.sum_Icc_eq_zero_of_periodic_of_isBigO_one`: conversely, if `a : ℕ → E` in a real normed
  space is `N`-periodic on `k ≥ 1` and `m ↦ ∑ k ∈ Icc 1 m, a k` is `O(1)`, then
  `∑ k ∈ Icc 1 N, a k = 0`.
* `TauCeti.exists_norm_sum_Icc_mul_natCast_cpow_neg_le` and
  `TauCeti.isBigO_sum_Icc_mul_natCast_cpow_neg`: uniform `O(1)` partial-sum bounds for
  `∑ k ∈ Icc 1 n, a k * k ^ (-z)` when `a` is `N`-periodic on `k ≥ 1` (`N ≠ 0`) with zero period
  sum and `0 ≤ z.re`, together with the positive-exponent versions for `z.re ≤ 0`.
-/

public section

namespace Finset

/-- **Uniform partial-sum bound for a zero-mean periodic sequence.** If `N ≠ 0`, `a (k + N) = a k`
for all `1 ≤ k`, and `∑ j ∈ Icc 1 N, a j = 0`, every partial sum `∑ j ∈ Icc 1 m, a j` has norm at
most `∑ j ∈ Icc 1 N, ‖a j‖`. -/
theorem norm_sum_Icc_le_of_sum_eq_zero {M : Type*} [SeminormedAddCommGroup M] {a : ℕ → M} {N : ℕ}
    (hN : N ≠ 0) (hper : ∀ k, 1 ≤ k → a (k + N) = a k)
    (hsum : ∑ j ∈ Icc 1 N, a j = 0) (m : ℕ) :
    ‖∑ j ∈ Icc 1 m, a j‖ ≤ ∑ j ∈ Icc 1 N, ‖a j‖ := by
  rw [sum_Icc_eq_sum_Icc_mod_of_sum_eq_zero hper hsum m]
  have hlt : m % N ≤ N := (Nat.mod_lt m (Nat.pos_of_ne_zero hN)).le
  exact (norm_sum_le _ _).trans
    (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hlt) fun _ _ _ ↦ norm_nonneg _)

end Finset

namespace TauCeti

open Asymptotics Filter

/-- **Bounded partial sums of a periodic sequence force vanishing period sum.** If `a : ℕ → E` in a
real normed space satisfies `a (k + N) = a k` for all `k ≥ 1` and its partial sums are `O(1)`, then
`∑ k ∈ Icc 1 N, a k = 0`. -/
theorem sum_Icc_eq_zero_of_periodic_of_isBigO_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℕ → E} {N : ℕ} (hper : ∀ k, 1 ≤ k → a (k + N) = a k)
    (hbdd : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop] (1 : ℕ → ℝ)) :
    ∑ k ∈ Finset.Icc 1 N, a k = 0 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · by_contra hS
    have hSpos : 0 < ‖∑ k ∈ Finset.Icc 1 N, a k‖ := norm_pos_iff.mpr hS
    obtain ⟨c, hc⟩ := hbdd.bound
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hc
    let m : ℕ := max n₀ (⌊max c 0 / ‖∑ k ∈ Finset.Icc 1 N, a k‖⌋₊ + 1)
    have hmN : n₀ ≤ m * N :=
      (le_max_left _ _).trans (Nat.le_mul_of_pos_right m (Nat.pos_of_ne_zero hN))
    have hle := hn₀ (m * N) hmN
    rw [Finset.sum_Icc_mul_eq_nsmul_of_periodic hper m, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
      Real.norm_natCast, Pi.one_apply, norm_one, mul_one] at hle
    have hlt : max c 0 < (m : ℝ) * ‖∑ k ∈ Finset.Icc 1 N, a k‖ :=
      (div_lt_iff₀ hSpos).mp
        ((Nat.lt_floor_add_one _).trans_le (by exact_mod_cast le_max_right n₀ _))
    linarith [le_max_left c 0]

private theorem norm_sum_Icc_mul_secondDiff_le {B : ℕ → ℂ} {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hB : ∀ k, ‖B k‖ ≤ M₂) {z : ℂ} (hz : 0 ≤ z.re) (m : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 m, B k *
        ((((k + 2 : ℕ) : ℂ) ^ (-z) - ((k + 1 : ℕ) : ℂ) ^ (-z)) -
          (((k + 1 : ℕ) : ℂ) ^ (-z) - (k : ℂ) ^ (-z)))‖ ≤
      2 * M₂ * ‖z‖ * ‖z + 1‖ := by
  have hsq : ∑ k ∈ Finset.Icc 1 m, ((k : ℝ) ^ 2)⁻¹ ≤ 2 := by
    rw [show Finset.Icc 1 m = Finset.Ioo 0 (m + 1) by ext k; simp; omega]
    simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 (m + 1)
  calc ‖∑ k ∈ Finset.Icc 1 m, B k *
          ((((k + 2 : ℕ) : ℂ) ^ (-z) - ((k + 1 : ℕ) : ℂ) ^ (-z)) -
            (((k + 1 : ℕ) : ℂ) ^ (-z) - (k : ℂ) ^ (-z)))‖
      ≤ ∑ k ∈ Finset.Icc 1 m, ‖B k‖ *
          ‖(((k + 2 : ℕ) : ℂ) ^ (-z) - ((k + 1 : ℕ) : ℂ) ^ (-z)) -
            (((k + 1 : ℕ) : ℂ) ^ (-z) - (k : ℂ) ^ (-z))‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ ↦ norm_mul _ _))
    _ ≤ ∑ k ∈ Finset.Icc 1 m, M₂ * (‖z‖ * ‖z + 1‖ / (k : ℝ) ^ 2) :=
        Finset.sum_le_sum fun k hk ↦ mul_le_mul (hB k)
          (norm_natCast_add_two_cpow_neg_sub_sub_le hz (Finset.mem_Icc.mp hk).1)
          (norm_nonneg _) hM₂
    _ = M₂ * ‖z‖ * ‖z + 1‖ * ∑ k ∈ Finset.Icc 1 m, ((k : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ ≤ M₂ * ‖z‖ * ‖z + 1‖ * 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2 * M₂ * ‖z‖ * ‖z + 1‖ := by ring

/-- **Uniform partial-sum bound for index-power twists of a zero-mean periodic sequence.**
Let `a : ℕ → ℂ` be periodic of period `N ≠ 0` on positive indices (`a (k + N) = a k` for all
`k ≥ 1`) with vanishing period sum `∑ k ∈ Icc 1 N, a k = 0`. Then for every `z : ℂ` with
`0 ≤ z.re`, the twisted partial sums `∑ k ∈ Icc 1 n, a k * k ^ (-z)` are uniformly bounded in norm
for all `n : ℕ`. -/
theorem exists_norm_sum_Icc_mul_natCast_cpow_neg_le {a : ℕ → ℂ} {N : ℕ} (hN : N ≠ 0)
    (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (hsum : ∑ k ∈ Finset.Icc 1 N, a k = 0)
    {z : ℂ} (hz : 0 ≤ z.re) :
    ∃ C : ℝ, ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, a k * (k : ℂ) ^ (-z)‖ ≤ C := by
  let A₁ : ℕ → ℂ := fun k ↦ ∑ j ∈ Finset.Icc 1 k, a j
  let M₁ : ℝ := ∑ j ∈ Finset.Icc 1 N, ‖a j‖
  have hA₁_per : Function.Periodic A₁ N := Finset.periodic_sum_Icc_of_sum_eq_zero hper hsum
  have hA₁_le (k : ℕ) : ‖A₁ k‖ ≤ M₁ := Finset.norm_sum_Icc_le_of_sum_eq_zero hN hper hsum k
  let μ : ℂ := (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, A₁ j
  let b : ℕ → ℂ := fun k ↦ A₁ k - μ
  have hb_sum : ∑ j ∈ Finset.Icc 1 N, b j = 0 := by
    simp [b, Finset.sum_sub_distrib, μ,
      mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr hN : (N : ℂ) ≠ 0)]
  let B : ℕ → ℂ := fun k ↦ ∑ j ∈ Finset.Icc 1 k, b j
  let M₂ : ℝ := ∑ j ∈ Finset.Icc 1 N, ‖b j‖
  have hB_le (k : ℕ) : ‖B k‖ ≤ M₂ :=
    Finset.norm_sum_Icc_le_of_sum_eq_zero hN (fun j _ ↦ by simp [b, hA₁_per j]) hb_sum k
  have hM₁ : 0 ≤ M₁ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hM₂ : 0 ≤ M₂ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  let f : ℕ → ℂ := fun k ↦ (k : ℂ) ^ (-z)
  refine ⟨M₁ + 2 * ‖μ‖ + M₂ * ‖z‖ + 2 * M₂ * ‖z‖ * ‖z + 1‖, fun n ↦ ?_⟩
  rcases n with _ | _ | m
  · rw [Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.sum_empty, norm_zero]
    positivity
  · rw [Finset.Icc_self, Finset.sum_singleton, norm_mul]
    have hterm : ‖a 1‖ * ‖f 1‖ ≤ M₁ := by simpa [A₁, f] using hA₁_le 1
    have hrest : 0 ≤ 2 * ‖μ‖ + M₂ * ‖z‖ + 2 * M₂ * ‖z‖ * ‖z + 1‖ := by positivity
    linarith
  · have hsbp : ∑ k ∈ Finset.Icc 1 (m + 2), a k * f k =
        A₁ (m + 2) * f (m + 2) - μ * (f (m + 2) - f 1) - B (m + 1) * (f (m + 2) - f (m + 1)) +
          ∑ k ∈ Finset.Icc 1 m, B k * ((f (k + 2) - f (k + 1)) - (f (k + 1) - f k)) := by
      simpa only [smul_eq_mul] using Finset.sum_Icc_add_two_by_parts'_sub a f μ m
    rw [hsbp]
    have hb1 : ‖A₁ (m + 2) * f (m + 2)‖ ≤ M₁ := by
      rw [norm_mul]
      simpa [f] using mul_le_mul (hA₁_le (m + 2))
        (norm_natCast_cpow_neg_le_one hz (m + 2)) (norm_nonneg _) hM₁
    have hb2 : ‖μ * (f (m + 2) - f 1)‖ ≤ 2 * ‖μ‖ := by
      rw [norm_mul, mul_comm 2]
      refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (norm_nonneg μ)
      linarith [norm_natCast_cpow_neg_le_one hz (m + 2), norm_natCast_cpow_neg_le_one hz 1]
    have hb3 : ‖B (m + 1) * (f (m + 2) - f (m + 1))‖ ≤ M₂ * ‖z‖ := by
      rw [norm_mul]
      exact mul_le_mul (hB_le (m + 1))
        (norm_natCast_add_one_cpow_neg_sub_le_norm hz (by omega)) (norm_nonneg _) hM₂
    exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add ((norm_sub_le _ _).trans (add_le_add hb1 hb2)) hb3))
      (norm_sum_Icc_mul_secondDiff_le hM₂ hB_le hz m))

/-- **Asymptotic `O(1)` form** of `exists_norm_sum_Icc_mul_natCast_cpow_neg_le`. -/
theorem isBigO_sum_Icc_mul_natCast_cpow_neg {a : ℕ → ℂ} {N : ℕ} (hN : N ≠ 0)
    (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (hsum : ∑ k ∈ Finset.Icc 1 N, a k = 0)
    {z : ℂ} (hz : 0 ≤ z.re) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, a k * (k : ℂ) ^ (-z)) =O[atTop] (1 : ℕ → ℝ) := by
  obtain ⟨C, hC⟩ := exists_norm_sum_Icc_mul_natCast_cpow_neg_le hN hper hsum hz
  exact IsBigO.of_bound C (Eventually.of_forall fun n ↦ by simpa using hC n)

/-- Positive-exponent version of `exists_norm_sum_Icc_mul_natCast_cpow_neg_le`, for `z.re ≤ 0`. -/
theorem exists_norm_sum_Icc_mul_natCast_cpow_le {a : ℕ → ℂ} {N : ℕ} (hN : N ≠ 0)
    (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (hsum : ∑ k ∈ Finset.Icc 1 N, a k = 0)
    {z : ℂ} (hz : z.re ≤ 0) :
    ∃ C : ℝ, ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, a k * (k : ℂ) ^ z‖ ≤ C := by
  simpa using exists_norm_sum_Icc_mul_natCast_cpow_neg_le hN hper hsum
    (z := -z) (by simpa using hz)

/-- Positive-exponent version of `isBigO_sum_Icc_mul_natCast_cpow_neg`, for `z.re ≤ 0`. -/
theorem isBigO_sum_Icc_mul_natCast_cpow {a : ℕ → ℂ} {N : ℕ} (hN : N ≠ 0)
    (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (hsum : ∑ k ∈ Finset.Icc 1 N, a k = 0)
    {z : ℂ} (hz : z.re ≤ 0) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, a k * (k : ℂ) ^ z) =O[atTop] (1 : ℕ → ℝ) := by
  simpa using isBigO_sum_Icc_mul_natCast_cpow_neg hN hper hsum
    (z := -z) (by simpa using hz)

end TauCeti

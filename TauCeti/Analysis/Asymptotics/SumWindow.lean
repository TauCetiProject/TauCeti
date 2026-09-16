/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic.FieldSimp

/-!
# Linear growth of partial sums from a window bound

If nonnegative terms `f n` have sums over the multiplicative windows `q x < n ≤ x` bounded by a
multiple of `x`, for a fixed ratio `0 ≤ q < 1` and all large `x`, then their partial sums
`∑_{1 ≤ n ≤ x} f n` are `O(x)`: the partial sum up to `x` is the window sum plus the partial sum
up to `q x`, and the window bounds form a geometric series.

This is the summation step of Chebyshev-type bounds, where a local estimate on windows
`(q x, x]` comes from a smoothed average and the global linear bound is what is needed.

## Main results

* `TauCeti.isBigO_sum_Icc_of_sum_Ioc_floor_mul_le`: a window bound `O(x)` implies partial sums
  `O(x)`.
* `TauCeti.exists_sum_Icc_le_mul_of_isBigO`: partial sums that are `O(x)` are bounded by `C N`
  at every natural cutoff `N`, with one constant `C`.
-/

public section

open Asymptotics Filter

namespace TauCeti

/-- **Summing windows.** If nonnegative terms `f n` have sums over the windows `q x < n ≤ x`
bounded by `K x` for all large `x`, where `0 ≤ q < 1` is a fixed ratio, then their partial sums
`∑_{1 ≤ n ≤ x} f n` are `O(x)`. -/
theorem isBigO_sum_Icc_of_sum_Ioc_floor_mul_le {f : ℕ → ℝ} (hf : 0 ≤ f) {q K : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h : ∀ᶠ x : ℝ in atTop, ∑ n ∈ Finset.Ioc ⌊q * x⌋₊ ⌊x⌋₊, f n ≤ K * x) :
    (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) =O[atTop] fun x ↦ x := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 h
  set S : ℝ → ℝ := fun x ↦ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n with hS
  have hSmono : Monotone S := fun x y hxy ↦
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hxy))
      fun n _ _ ↦ hf n
  have hSnn : ∀ x, 0 ≤ S x := fun x ↦ Finset.sum_nonneg fun n _ ↦ hf n
  -- Beyond `x₁` we have `q x ≤ x - 1`, so peeling off the window `(q x, x]` lowers `⌊x⌋₊`.
  set x₁ : ℝ := max x₀ (1 / (1 - q))
  have hq1' : 0 < 1 - q := by linarith
  set K' : ℝ := max K 0 / (1 - q) with hK'
  have hK'nn : 0 ≤ K' := by positivity
  have hK'eq : K' * q + max K 0 = K' := by
    rw [hK']
    field_simp
    ring
  have key : ∀ N : ℕ, ∀ x : ℝ, 0 ≤ x → ⌊x⌋₊ ≤ N → S x ≤ K' * x + S x₁ := by
    intro N
    induction N with
    | zero =>
      intro x hx hN
      have : S x = 0 := by simp [hS, Nat.le_zero.1 hN]
      rw [this]
      have := hSnn x₁
      positivity
    | succ N ih =>
      intro x hx hN
      rcases le_or_gt x x₁ with hxx | hxx
      · have := hSmono hxx
        have : 0 ≤ K' * x := by positivity
        linarith
      have hxx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hxx.le
      have hxq : q * x ≤ x - 1 := by
        have h1 : 1 / (1 - q) < x := lt_of_le_of_lt (le_max_right _ _) hxx
        rw [div_lt_iff₀ hq1'] at h1
        nlinarith
      have hfloor : ⌊q * x⌋₊ ≤ N := by
        have h1 : ⌊q * x⌋₊ ≤ ⌊x - 1⌋₊ := Nat.floor_mono hxq
        rw [Nat.floor_sub_one] at h1
        omega
      have hqx : 0 ≤ q * x := by positivity
      have hsplit : S x = S (q * x) + ∑ n ∈ Finset.Ioc ⌊q * x⌋₊ ⌊x⌋₊, f n :=
        (Finset.sum_Ioc_consecutive f (Nat.zero_le _)
          (Nat.floor_mono (by nlinarith))).symm
      have hwin := hx₀ x hxx₀
      have hrec := ih (q * x) hqx hfloor
      have hK : K * x ≤ max K 0 * x := mul_le_mul_of_nonneg_right (le_max_left _ _) hx
      calc S x ≤ K' * (q * x) + S x₁ + max K 0 * x := by linarith
        _ = (K' * q + max K 0) * x + S x₁ := by ring
        _ = K' * x + S x₁ := by rw [hK'eq]
  refine .of_bound (K' + S x₁) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hS' : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n = S x := by
    simp only [hS, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  rw [hS', Real.norm_of_nonneg (hSnn x), Real.norm_of_nonneg hx0]
  have := key ⌊x⌋₊ x hx0 le_rfl
  have := hSnn x₁
  nlinarith

/-- **A uniform linear bound from linear growth.** If the partial sums `∑_{1 ≤ n ≤ x} f n` of
nonnegative terms are `O(x)`, then a single constant `C` bounds them by `C N` at every natural
cutoff `N`, including the finitely many cutoffs below the range where the `O(x)` estimate starts. -/
theorem exists_sum_Icc_le_mul_of_isBigO {f : ℕ → ℝ} (hf : 0 ≤ f)
    (h : (fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) =O[atTop] fun x ↦ x) :
    ∃ C : ℝ, ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, f n ≤ C * N := by
  obtain ⟨c, hc⟩ := h.bound
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hc
  set S : ℕ → ℝ := fun N ↦ ∑ n ∈ Finset.Icc 1 N, f n with hS
  have hSmono : Monotone S := fun M N hMN ↦
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hMN) fun n _ _ ↦ hf n
  have hSnn : ∀ N, 0 ≤ S N := fun N ↦ Finset.sum_nonneg fun n _ ↦ hf n
  refine ⟨max c (S ⌈x₀⌉₊), fun N ↦ ?_⟩
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  rcases le_or_gt ⌈x₀⌉₊ N with hN | hN
  · have hbound := hx₀ N ((Nat.le_ceil x₀).trans (Nat.cast_le.2 hN))
    rw [Nat.floor_natCast, Real.norm_of_nonneg (hSnn N), Real.norm_of_nonneg hN0] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hN0)
  · rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · simp
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    calc S N ≤ S ⌈x₀⌉₊ := hSmono hN.le
      _ ≤ S ⌈x₀⌉₊ * N := le_mul_of_one_le_right (hSnn _) hN1
      _ ≤ max c (S ⌈x₀⌉₊) * N := mul_le_mul_of_nonneg_right (le_max_right _ _) hN0

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Weight-two row sums on a finite group

For a function `W` on a finite additive group `M` and a point `a ∈ M`, the row sum
`∑_{n ∈ ℤ} W(n • a) n⁻²` converges absolutely, being dominated by `∑_{n ∈ ℤ} n⁻² = π² / 3`. On
even functions these row sums are diagonally dominant: the terms `n = ±1` contribute `2 W(a)`,
while the remaining terms have norm at most `(π² / 3 - 2) ‖W‖_∞ < 2 ‖W‖_∞`. Hence an even
function whose row sums vanish on its support is zero.

This is the injectivity input for the weight-two cusp–Eisenstein decomposition, where `M` is the
group of residue pairs modulo `N` and the row sums are the constant terms of weighted weight-two
Eisenstein series.

## Main results

* `TauCeti.norm_intCast_zpow_neg_two`: `‖(n : ℂ) ^ (-2)‖ = (n ^ 2)⁻¹`.
* `TauCeti.summable_zsmul_mul_zpow_neg_two`: the row sums converge absolutely.
* `TauCeti.eq_zero_of_forall_tsum_zsmul_mul_zpow_neg_two_eq_zero`: the injectivity of the row
  sums on even functions.
-/

public section

namespace TauCeti

/-- The norm of `(n : ℂ) ^ (-2)` for an integer `n` is the real number `(n ^ 2)⁻¹`. -/
theorem norm_intCast_zpow_neg_two (n : ℤ) : ‖(n : ℂ) ^ (-2 : ℤ)‖ = ((n : ℝ) ^ 2)⁻¹ := by
  rw [norm_zpow, Complex.norm_intCast, _root_.zpow_neg, ← sq_abs (n : ℝ)]
  norm_cast

variable {M : Type*} [AddGroup M] [Finite M]

/-- On a finite additive group, the weight-two row sums `∑_{n ∈ ℤ} W(n • a) n⁻²` converge
absolutely. -/
theorem summable_zsmul_mul_zpow_neg_two (W : M → ℂ) (a : M) :
    Summable fun n : ℤ ↦ W (n • a) * (n : ℂ) ^ (-2 : ℤ) := by
  obtain ⟨C, hC⟩ := (Set.finite_range fun a ↦ ‖W a‖).bddAbove
  refine Summable.of_norm_bounded
    ((Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).mul_left C) fun n ↦ ?_
  rw [norm_mul, norm_intCast_zpow_neg_two, one_div]
  exact mul_le_mul_of_nonneg_right (hC ⟨_, rfl⟩) (by positivity)

open Real in
/-- **Diagonal dominance of the weight-two row sums.** Let `W` be an even function on a finite
additive group. If the row sum `∑_{n ∈ ℤ} W(n • a) n⁻²` vanishes at every point `a` of the
support of `W`, then `W = 0`. -/
theorem eq_zero_of_forall_tsum_zsmul_mul_zpow_neg_two_eq_zero
    {W : M → ℂ} (heven : ∀ a, W (-a) = W a)
    (h : ∀ a, W a ≠ 0 → ∑' n : ℤ, W (n • a) * (n : ℂ) ^ (-2 : ℤ) = 0) : W = 0 := by
  -- At a point `a` where `‖W‖` is maximal, the terms `n = ±1` of the row sum contribute
  -- `2 W(a)`, while the others have total norm at most `‖W a‖ (π² / 3 - 2) < 2 ‖W a‖`.
  classical
  by_contra hW
  obtain ⟨a, ha⟩ := Finite.exists_max fun a ↦ ‖W a‖
  have hWa : W a ≠ 0 := by
    refine fun h0 ↦ hW (funext fun b ↦ ?_)
    simpa [h0] using ha b
  set m := ‖W a‖ with hm
  have hm0 : 0 < m := norm_pos_iff.mpr hWa
  -- the comparison series `m ∑ n⁻² = m π² / 3`
  let b : ℤ → ℝ := fun n ↦ m * ((n : ℝ) ^ 2)⁻¹
  have hb : HasSum b (m * (π ^ 2 / 3)) := hasSum_int_inv_sq.mul_left m
  let g : ℤ → ℂ := fun n ↦ W (n • a) * (n : ℂ) ^ (-2 : ℤ)
  have hgb (n : ℤ) : ‖g n‖ ≤ b n := by
    simp only [g, b, norm_mul, norm_intCast_zpow_neg_two]
    exact mul_le_mul_of_nonneg_right (ha _) (by positivity)
  have hg : HasSum g 0 := by
    have hs : Summable g := Summable.of_norm_bounded hb.summable hgb
    exact h a hWa ▸ hs.hasSum
  have h1 : g 1 = W a := by simp [g]
  have h2 : g (-1) = W a := by simp [g, heven]
  have hb1 : b 1 = m := by simp [b]
  have hb2 : b (-1) = m := by simp [b]
  -- remove the terms `n = ± 1`
  have hg' := (hg.update 1 0).update (-1) 0
  have hb' := (hb.update 1 0).update (-1) 0
  have hle := hg'.norm_le_of_bounded hb' fun n ↦ by
    by_cases hn : n = -1
    · subst hn; simp
    by_cases hn' : n = 1
    · subst hn'; simp
    simp only [Function.update_of_ne hn, Function.update_of_ne hn']
    exact hgb n
  simp only [Function.update_of_ne (by norm_num : (-1 : ℤ) ≠ 1), h1, h2, hb1, hb2] at hle
  have hnorm : ‖(0 : ℂ) - W a + (0 - W a + 0)‖ = 2 * m := by
    rw [show (0 : ℂ) - W a + (0 - W a + 0) = -(2 * W a) by ring, norm_neg, norm_mul]
    simp [hm]
  rw [hnorm] at hle
  have hpi : π ^ 2 < 12 := by nlinarith [Real.pi_lt_d2, pi_pos]
  nlinarith

end TauCeti

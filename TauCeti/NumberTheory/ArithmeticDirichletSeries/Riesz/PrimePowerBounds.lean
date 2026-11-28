/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# Geometric bounds for Riesz ramps at powers

A nonnegative cap can only decrease a positive-part ramp. At positive powers of a base `p > 1`,
the comparison series has ratio `p⁻¹`, or `p⁻²` when only odd exponents are retained. The bounds do
not depend on the exponent cutoff or on how the caps vary with the exponent.
-/

public section

open Finset

namespace TauCeti

/-- A finite sum of positive-part ramps with nonnegative caps on a geometric sequence is at
most the sum of the entire geometric sequence. -/
theorem sum_max_sub_mul_pow_le (s : Finset ℕ) {a r : ℝ} (ha : 0 ≤ a)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (w : ℕ → ℝ) (hw : ∀ k ∈ s, 0 ≤ w k) :
    ∑ k ∈ s, max (a * r ^ k - w k) 0 ≤ a / (1 - r) := by
  have hgeom := summable_geometric_of_lt_one hr₀ hr₁
  calc
    _ ≤ ∑ k ∈ s, a * r ^ k := sum_le_sum fun k hk ↦
      max_le (sub_le_self _ (hw k hk)) (mul_nonneg ha (pow_nonneg hr₀ _))
    _ ≤ ∑' k : ℕ, a * r ^ k := (hgeom.mul_left a).sum_le_tsum s fun _ _ ↦ by positivity
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr₀ hr₁, div_eq_mul_inv]

/-- Riesz ramps at any finite set of exponents in `1, 1 + d, 1 + 2d, …` are bounded by the
geometric series starting at `a / p` with ratio `p⁻ᵈ`. -/
theorem sum_max_div_pow_sub_le_of_progression (s : Finset ℕ) {a p : ℝ} (ha : 0 ≤ a)
    (hp : 1 < p) {d : ℕ} (hd : 0 < d) (hs : ∀ k ∈ s, ∃ j, k = d * j + 1)
    (w : ℕ → ℝ) (hw : ∀ k ∈ s, 0 ≤ w k) :
    ∑ k ∈ s, max (a / p ^ k - w k) 0 ≤ (a / p) / (1 - (p ^ d)⁻¹) := by
  let e (k : ℕ) := (k - 1) / d
  have hindex (k : ℕ) (hk : k ∈ s) : d * e k + 1 = k := by
    obtain ⟨j, rfl⟩ := hs k hk
    simp [e, Nat.mul_div_cancel_left _ hd]
  have he : Set.InjOn e (↑s : Set ℕ) := fun k hk l hl h ↦
    (hindex k hk).symm.trans ((congrArg (fun j ↦ d * j + 1) h).trans (hindex l hl))
  have hpd : 1 < p ^ d := one_lt_pow₀ hp hd.ne'
  calc
    _ = ∑ j ∈ s.image e, max ((a / p) * (p ^ d)⁻¹ ^ j - w (d * j + 1)) 0 := by
      rw [sum_image he]
      refine sum_congr rfl fun k hk ↦ ?_
      have hpow : p ^ k = (p ^ d) ^ e k * p := by
        calc
          p ^ k = p ^ (d * e k + 1) := congrArg (p ^ ·) (hindex k hk).symm
          _ = _ := by rw [pow_succ, pow_mul]
      rw [hpow, hindex k hk, inv_pow]
      simp [div_eq_mul_inv, mul_inv_rev, mul_assoc]
    _ ≤ _ := sum_max_sub_mul_pow_le _ (div_nonneg ha (zero_lt_one.trans hp).le)
      (by positivity) (inv_lt_one_of_one_lt₀ hpd) _ fun j hj ↦ by
        obtain ⟨k, hk, rfl⟩ := mem_image.mp hj
        exact (hindex k hk).symm ▸ hw k hk

/-- Riesz ramps at any finite set of positive exponents are bounded by `a / (p - 1)`. -/
theorem sum_max_div_pow_sub_le (s : Finset ℕ) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 < p)
    (hs : ∀ k ∈ s, 0 < k) (w : ℕ → ℝ) (hw : ∀ k ∈ s, 0 ≤ w k) :
    ∑ k ∈ s, max (a / p ^ k - w k) 0 ≤ a / (p - 1) := by
  calc
    _ ≤ (a / p) / (1 - (p ^ 1)⁻¹) := sum_max_div_pow_sub_le_of_progression s ha hp
      Nat.one_pos (fun k hk ↦ ⟨k - 1, by simpa using (Nat.sub_add_cancel (hs k hk)).symm⟩) w hw
    _ = _ := by
      simp only [pow_one]
      have hp₀ : p ≠ 0 := by linarith
      have hp₁ : p - 1 ≠ 0 := by linarith
      field_simp

/-- Riesz ramps at any finite set of odd exponents are bounded by `a * p / (p² - 1)`. -/
theorem sum_max_div_odd_pow_sub_le (s : Finset ℕ) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 < p)
    (hs : ∀ k ∈ s, Odd k) (w : ℕ → ℝ) (hw : ∀ k ∈ s, 0 ≤ w k) :
    ∑ k ∈ s, max (a / p ^ k - w k) 0 ≤ a * p / (p ^ 2 - 1) := by
  calc
    _ ≤ (a / p) / (1 - (p ^ 2)⁻¹) := sum_max_div_pow_sub_le_of_progression s ha hp
      (by decide) (fun k hk ↦ ⟨k / 2, (Nat.two_mul_div_two_add_one_of_odd (hs k hk)).symm⟩)
      w hw
    _ = _ := by
      have hp₀ : p ≠ 0 := by linarith
      have hp₂ : p ^ 2 - 1 ≠ 0 := by nlinarith
      field_simp

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Subadditive

/-!
# Lower bounds for submultiplicative sequences

A lower bound of exponential rate `r` at arbitrarily large indices gives the same rate,
with no prefactor, at every index. This is a consequence of the limit and infimum
properties of the roots in Fekete's lemma.
-/

public section

open Filter
open scoped Topology

namespace Submultiplicative

/-- If a submultiplicative sequence with `0 ≤ u 1` is at least `C * r ^ n` at arbitrarily
large indices, then it is at least `r ^ n` at every index, including zero. -/
theorem pow_le_of_frequently_ge_mul_pow {u : ℕ → ℝ} (hu : Submultiplicative u)
    (hu₁ : 0 ≤ u 1) {C r : ℝ} (hC : 0 < C) (hr : 0 < r)
    (h : ∃ᶠ n in atTop, C * r ^ n ≤ u n) (n : ℕ) : r ^ n ≤ u n := by
  have hu₀ (m : ℕ) : 0 ≤ u m := by
    obtain ⟨k, hmk, hk⟩ := frequently_atTop.mp h m
    have hkm : (k - m) * 1 + m = k := by omega
    have hle := hu.apply_mul_add_le (k - m) 1 m hu₁
    rw [hkm] at hle
    by_contra! hm
    exact (mul_pos hC (pow_pos hr k)).not_ge
      (hk.trans (hle.trans (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hu₁ _) hm.le)))
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · obtain ⟨k, hk⟩ := h.exists
    have hk₀ : 0 < u k := (mul_pos hC (pow_pos hr k)).trans_le hk
    simpa using (le_mul_iff_one_le_left hk₀).mp (by simpa using hu 0 k)
  have hinv : Tendsto (fun k : ℕ ↦ (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun k : ℕ ↦ C ^ (k : ℝ)⁻¹ * r) atTop (𝓝 r) := by
    simpa using (((Real.continuous_const_rpow hC.ne').tendsto 0).comp hinv).mul_const r
  have hroot : ∃ᶠ k : ℕ in atTop, C ^ (k : ℝ)⁻¹ * r ≤ u k ^ (k : ℝ)⁻¹ := by
    refine (h.and_eventually (eventually_gt_atTop 0)).mono fun k ⟨hk, hk₀⟩ ↦ ?_
    have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk₀
    have hle := Real.rpow_le_rpow (mul_nonneg hC.le (pow_nonneg hr.le k)) hk (inv_nonneg.mpr hkR.le)
    rwa [Real.mul_rpow hC.le (pow_nonneg hr.le k), ← Real.rpow_natCast,
      Real.rpow_rpow_inv hr.le hkR.ne'] at hle
  have hl := le_of_tendsto_of_tendsto_of_frequently hlim (hu.tendsto_lim hu₀) hroot
  have hle := Real.rpow_le_rpow hr.le (hl.trans (hu.lim_le_rpow hu₀ hn.ne')) (Nat.cast_nonneg n)
  rwa [Real.rpow_natCast r, Real.rpow_inv_rpow (hu₀ n) (Nat.cast_ne_zero.mpr hn.ne')] at hle

end Submultiplicative

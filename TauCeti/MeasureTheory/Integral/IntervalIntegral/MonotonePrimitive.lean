/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integrals of primitives of monotone functions

If `F` is nondecreasing on `[0, R]`, then `2 ∫₀^R ∫₀^t F ≤ R ∫₀^R F`: the primitive
`G(t) = ∫₀^t F` satisfies `G(t) + G(R - t) ≤ G(R)`, and integrating over `[0, R]` gives the claim.
-/

public section

open MeasureTheory Set

namespace intervalIntegral

/-- The integral of the primitive of a nondecreasing function on `[0, R]` is at most
half the area of the rectangle with base `R` and height equal to its final value. -/
theorem two_mul_integral_primitive_le {F : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hF : MonotoneOn F (Icc 0 R)) :
    2 * (∫ t in 0..R, ∫ s in 0..t, F s) ≤ R * ∫ s in 0..R, F s := by
  let G (t : ℝ) := ∫ s in 0..t, F s
  have hi {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ R) :
      IntervalIntegrable F volume a b := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hF.mono (Icc_subset_Icc ha hb)
  have hG : IntervalIntegrable G volume 0 R :=
    (intervalIntegral.continuousOn_primitive_interval
      ((intervalIntegrable_iff' (by finiteness)).mp (hi le_rfl hR le_rfl))).intervalIntegrable
  have hrev : IntervalIntegrable (fun t ↦ G (R - t)) volume 0 R := by
    simpa using hG.symm.comp_sub_left R
  have hsum (t : ℝ) (ht : t ∈ Icc 0 R) : G t + G (R - t) ≤ G R := by
    have hr : 0 ≤ R - t := sub_nonneg.mpr ht.2
    have hend : t + (R - t) = R := by ring
    have hi' := hi hr (by linarith [ht.1] : R - t ≤ R) le_rfl
    have hshift : IntervalIntegrable (fun s ↦ F (s + (R - t))) volume 0 t := by
      convert hi'.comp_add_right (R - t) using 1 <;> ring
    have hmono := intervalIntegral.integral_mono_on ht.1 (hi le_rfl ht.1 ht.2) hshift
      (fun s hs ↦ hF ⟨hs.1, hs.2.trans ht.2⟩ ⟨by linarith [hs.1], by linarith [hs.2]⟩
        (by linarith : s ≤ s + (R - t)))
    rw [intervalIntegral.integral_comp_add_right, zero_add, hend] at hmono
    dsimp only [G]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi le_rfl hr (by linarith [ht.1])) hi']
    linarith
  have hb := intervalIntegral.integral_mono_on hR (hG.add hrev) intervalIntegrable_const hsum
  rw [intervalIntegral.integral_add hG hrev, intervalIntegral.integral_comp_sub_left,
    sub_self, sub_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hb
  dsimp only [G] at hb
  linarith

end intervalIntegral

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.RealPart

/-!
# Horizontal comparison of Hadamard logarithmic derivatives

For an entire function of order at most one with zeros in the unit strip, compare its
logarithmic derivative at `s` with that at `2 + s.im * I`. After retaining the poles in the
unit-height window, the error is bounded by the positive real-part kernel at the reference
point. This is the partial-fraction method for the local logarithmic derivative, as in
Montgomery and Vaughan, *Multiplicative Number Theory I*, §10.2.
-/

public section

open Complex

namespace TauCeti

/-- After retaining the inverse at `s` for the nearby ordinate, the difference between the
horizontal reciprocal kernels is bounded by the positive kernel at `w`. -/
private theorem norm_sub_inv_sub_window_le {s w ρ : ℂ} (hw : w.re = 2) (him : w.im = s.im)
    (hρ : ρ.re ∈ Set.Icc 0 1) (hd : ‖w - s‖ ≤ 3) :
    ‖(if |ρ.im - s.im| ≤ 1 then 0 else (s - ρ)⁻¹) - (w - ρ)⁻¹‖ ≤
      12 * ((w - ρ)⁻¹).re := by
  have hre : 1 ≤ (w - ρ).re := by simp only [sub_re, hw]; linarith [hρ.2]
  have h₀ : 0 < ‖w - ρ‖ := zero_lt_one.trans_le (hre.trans (re_le_norm _))
  rw [inv_re, normSq_eq_norm_sq, ← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos h₀)]
  split_ifs with h
  · rw [zero_sub, norm_neg, norm_inv, sq, ← mul_assoc, inv_mul_cancel₀ h₀.ne', one_mul]
    have hRe : (w - ρ).re ≤ 2 := by simp only [sub_re, hw]; linarith [hρ.1]
    have hIm : |(w - ρ).im| ≤ 1 := by simpa [him, abs_sub_comm] using h
    have hnorm : ‖w - ρ‖ ≤ 3 := (norm_le_abs_re_add_abs_im _).trans (by
      rw [abs_of_nonneg (zero_le_one.trans hre)]
      linarith)
    linarith
  · have hs : 1 ≤ ‖s - ρ‖ :=
      (by simpa [abs_sub_comm] using (le_of_lt (lt_of_not_ge h)) : 1 ≤ |(s - ρ).im|).trans
        (abs_im_le_norm _)
    have hs₀ : 0 < ‖s - ρ‖ := zero_lt_one.trans_le hs
    have hw₀ : w - ρ ≠ 0 := norm_ne_zero_iff.mp h₀.ne'
    rw [inv_sub_inv (norm_ne_zero_iff.mp hs₀.ne') hw₀, sub_sub_sub_cancel_right,
      norm_div, norm_mul, div_mul_eq_mul_div, div_le_iff₀ (mul_pos hs₀ h₀)]
    have ht : ‖w - ρ‖ ≤ 4 * ‖s - ρ‖ := by
      linarith [norm_sub_le_norm_sub_add_norm_sub w s ρ]
    have hc : ‖w - s‖ * ‖w - ρ‖ ≤ 12 * ‖s - ρ‖ := by
      calc
        _ ≤ 3 * (4 * ‖s - ρ‖) := mul_le_mul hd ht (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    calc
      _ = (‖w - s‖ * ‖w - ρ‖) * ‖w - ρ‖ := by ring
      _ ≤ (12 * ‖s - ρ‖) * ‖w - ρ‖ := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hre) (mul_nonneg hs₀.le h₀.le)]

open scoped Classical in
/-- Subtract the poles within one unit of the ordinate of `s` from the logarithmic derivative
of an entire function of order at most one with no zero at the origin. The error relative to
its value at `w = 2 + s.im * I` is bounded by twelve times the positive real-part sum at `w`.
The divisor indexes the zeros with their multiplicities. -/
theorem OrderLE.norm_logDeriv_sub_window_sub_le {f : ℂ → ℂ} (h : OrderLE f 1)
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hstrip : ∀ ρ, f ρ = 0 → ρ.re ∈ Set.Icc 0 1)
    {s w : ℂ} (hs : f s ≠ 0) (hw : w.re = 2) (him : w.im = s.im) (hd : ‖w - s‖ ≤ 3) :
    let d := MeromorphicOn.divisor f Set.univ
    ‖logDeriv f s - (∑' ρ : d.support, if |(ρ : ℂ).im - s.im| ≤ 1 then
      ((d ρ).toNat : ℂ) / (s - (ρ : ℂ)) else 0) - logDeriv f w‖ ≤
      12 * ∑' ρ : d.support, ((d ρ).toNat : ℝ) * (1 / (w - (ρ : ℂ))).re := by
  classical
  let d := MeromorphicOn.divisor f Set.univ
  have ha : AnalyticOnNhd ℂ f Set.univ := fun ρ _ ↦ hf.analyticAt ρ
  have hzero (ρ : d.support) : f ρ = 0 := by
    have hρ := ρ.property
    rw [Function.mem_support, ha.meromorphicOn.divisor_eq_analyticOrderNatAt
      (hf.analyticAt _) (Set.mem_univ _), Int.natCast_ne_zero] at hρ
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hρ
  have hw₀ : f w ≠ 0 := fun hwz ↦ by simpa [hw] using (hstrip w hwz).2
  let A (z : ℂ) (ρ : d.support) : ℂ := ((d ρ).toNat : ℂ) * (1 / (z - (ρ : ℂ)) + 1 / (ρ : ℂ))
  let W (ρ : d.support) : ℂ := if |(ρ : ℂ).im - s.im| ≤ 1 then
    ((d ρ).toNat : ℂ) / (s - (ρ : ℂ)) else 0
  let K (ρ : d.support) : ℝ := ((d ρ).toNat : ℝ) * (1 / (w - (ρ : ℂ))).re
  have hK : Summable K := by
    refine h.summable_divisor_mul_re_one_div_sub (C := 1) hf (by norm_num) ?_ w
    intro ρ hρ
    have hmem := hstrip ρ (hzero ⟨ρ, ne_of_gt hρ⟩)
    simpa only [abs_of_nonneg hmem.1] using hmem.2
  have hbound (ρ : d.support) : ‖A s ρ - A w ρ - W ρ‖ ≤ 12 * K ρ := by
    have hk := norm_sub_inv_sub_window_le hw him (hstrip ρ (hzero ρ)) hd
    have he : A s ρ - A w ρ - W ρ = ((d ρ).toNat : ℂ) *
        ((if |(ρ : ℂ).im - s.im| ≤ 1 then 0 else (s - (ρ : ℂ))⁻¹) - (w - (ρ : ℂ))⁻¹) := by
      dsimp only [A, W]
      split_ifs <;> simp only [div_eq_mul_inv, one_mul] <;> ring
    rw [he, norm_mul, Complex.norm_natCast]
    calc
      _ ≤ ((d ρ).toNat : ℝ) * (12 * ((w - (ρ : ℂ))⁻¹).re) :=
        mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg _)
      _ = _ := by simp only [K, one_div, mul_left_comm]
  have hA (z : ℂ) : Summable (A z) :=
    (h.summable_norm_divisor_mul_one_div_sub_add_one_div hf (by norm_num) z).of_norm
  have hAs := hA s
  have hAw := hA w
  have hE := Summable.of_norm_bounded (hK.mul_left 12) hbound
  have hW : Summable W := ((hAs.sub hAw).sub hE).congr fun ρ ↦ by ring
  have he := tsum_of_norm_bounded (hK.mul_left 12).hasSum hbound
  rw [(hAs.sub hAw).tsum_sub hW, hAs.tsum_sub hAw] at he
  rw [hK.tsum_mul_left] at he
  have hAt (z : ℂ) (hz : f z ≠ 0) : logDeriv f z = logDeriv f 0 + ∑' ρ, A z ρ :=
    h.logDeriv_eq_add_tsum hf h0 hz
  rw [hAt s hs, hAt w hw₀]
  convert he using 2
  ring

end TauCeti

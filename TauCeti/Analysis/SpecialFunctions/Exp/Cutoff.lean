/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Smooth exponential cutoffs with length-independent integral bounds

The function `(1 - exp (-scale * t)) * (1 - exp (-scale * (L - t)))` vanishes at
both ends of `[0,L]`. At positive scale its squared derivative has integral at most
`2 * scale`, and the integral of its squared-cutoff defect is at most `4 / scale`.
These estimates control the cutoff error in Ricci integral bounds from index forms.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Claim 9.47, for
  the index-form application. That argument uses piecewise linear cutoffs; the smooth
  exponential cutoff and the constants here are an alternative construction.
* Related formalizations: https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
-/

public section

open Set MeasureTheory intervalIntegral
open scoped ContDiff

noncomputable section

namespace TauCeti.ExponentialCutoff

/-- Endpoint-zero smooth exponential cutoff with independent length and scale. -/
def cutoff (L scale t : ℝ) : ℝ :=
  (1 - Real.exp (-scale * t)) * (1 - Real.exp (-scale * (L - t)))

/-- The exponential cutoff is smooth for every real length and scale. -/
theorem contDiff_cutoff (L scale : ℝ) : ContDiff ℝ ∞ (cutoff L scale) := by
  unfold cutoff
  fun_prop

/-- The cutoff vanishes at the left endpoint, without sign restrictions. -/
@[simp] theorem cutoff_zero (L scale : ℝ) : cutoff L scale 0 = 0 := by
  simp [cutoff]

/-- The cutoff vanishes at the right endpoint, including a zero-length interval. -/
@[simp] theorem cutoff_end (L scale : ℝ) : cutoff L scale L = 0 := by
  simp [cutoff]

/-- Explicit derivative of the exponential cutoff, valid on the entire real line. -/
theorem hasDerivAt_cutoff (L scale t : ℝ) :
    HasDerivAt (cutoff L scale)
      (scale * (Real.exp (-scale * t) - Real.exp (-scale * (L - t)))) t := by
  have hA := ((hasDerivAt_id t).const_mul (-scale)).exp
  have hB := (((hasDerivAt_id t).const_sub L).const_mul (-scale)).exp
  convert (hA.const_sub 1).mul (hB.const_sub 1) using 1 <;>
    first | rfl | (simp only [id_eq]; ring)

/-- On a nonnegative-length interval and at nonnegative scale, the cutoff lies in `[0,1]`. -/
theorem cutoff_mem_Icc {L scale t : ℝ} (hscale : 0 ≤ scale) (ht : t ∈ Icc 0 L) :
    cutoff L scale t ∈ Icc 0 1 := by
  have hA : Real.exp (-scale * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
  have hB : Real.exp (-scale * (L - t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [ht.2])
  have hA0 := (Real.exp_pos (-scale * t)).le
  have hB0 := (Real.exp_pos (-scale * (L - t))).le
  constructor
  · exact mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)
  · exact (mul_le_mul (show 1 - Real.exp (-scale * t) ≤ 1 by linarith)
      (show 1 - Real.exp (-scale * (L - t)) ≤ 1 by linarith)
      (sub_nonneg.mpr hB) zero_le_one).trans_eq (one_mul 1)

/-- The squared-cutoff defect is bounded by the two decaying endpoint exponentials. -/
theorem cutoff_defect_le (L scale t : ℝ) :
    1 - cutoff L scale t ^ 2 ≤
      2 * (Real.exp (-scale * t) + Real.exp (-scale * (L - t))) := by
  have hAB := mul_nonneg (Real.exp_pos (-scale * t)).le
    (Real.exp_pos (-scale * (L - t))).le
  have hlo : 1 - Real.exp (-scale * t) - Real.exp (-scale * (L - t)) ≤ cutoff L scale t := by
    dsimp [cutoff]
    nlinarith
  nlinarith [sq_nonneg (1 - cutoff L scale t)]

private theorem integral_exp_neg_mul_le {L scale : ℝ} (hscale : 0 < scale) :
    (∫ t : ℝ in 0..L, Real.exp (-scale * t)) ≤ 1 / scale := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hscale.ne')]
  simp only [mul_zero, integral_exp, Real.exp_zero, smul_eq_mul]
  have hpos := (Real.exp_pos (-(scale * L))).le
  apply (mul_le_mul_iff_of_pos_left hscale).mp
  field_simp
  nlinarith

-- Both public integral bounds use this same positive exponential-pair majorant.
private theorem integral_le_exp_pair {f : ℝ → ℝ} {L scale K : ℝ}
    (hL : 0 ≤ L) (hscale : 0 < scale) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc 0 L, f t ≤
      K * (Real.exp (-scale * t) + Real.exp (-scale * (L - t)))) :
    (∫ t in (0 : ℝ)..L, f t) ≤ K * (2 / scale) := by
  by_cases hf : IntervalIntegrable f volume 0 L
  swap
  · rw [integral_undef hf]
    positivity
  have hA : Continuous (fun t : ℝ ↦ Real.exp (-scale * t)) := by fun_prop
  have hB : Continuous (fun t : ℝ ↦ Real.exp (-scale * (L - t))) := by fun_prop
  have hreflect : (∫ t : ℝ in 0..L, Real.exp (-scale * (L - t))) =
      ∫ t : ℝ in 0..L, Real.exp (-scale * t) := by
    rw [intervalIntegral.integral_comp_sub_left (fun t ↦ Real.exp (-scale * t)) L]
    simp only [sub_self, sub_zero]
  calc
    (∫ t in (0 : ℝ)..L, f t) ≤
        ∫ t in (0 : ℝ)..L,
          K * (Real.exp (-scale * t) + Real.exp (-scale * (L - t))) :=
      intervalIntegral.integral_mono_on hL hf
        (((hA.add hB).const_mul K).intervalIntegrable 0 L) hbound
    _ = K * (2 * ∫ t : ℝ in 0..L, Real.exp (-scale * t)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hA.intervalIntegrable 0 L) (hB.intervalIntegrable 0 L),
        hreflect, ← two_mul]
    _ ≤ K * (2 / scale) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [mul_one_div] using
          mul_le_mul_of_nonneg_left (integral_exp_neg_mul_le hscale) (by norm_num : (0 : ℝ) ≤ 2)) hK

/-- The integrated squared-cutoff defect is at most `4/scale`, independently of length. -/
theorem integral_cutoff_defect_le {L scale : ℝ} (hL : 0 ≤ L) (hscale : 0 < scale) :
    (∫ t : ℝ in 0..L, 1 - cutoff L scale t ^ 2) ≤ 4 / scale := by
  have h := integral_le_exp_pair (K := 2) hL hscale (by norm_num)
    (fun t _ ↦ cutoff_defect_le L scale t)
  exact h.trans_eq (by ring)

/-- The squared cutoff derivative is bounded by the exponential pair at twice the scale. -/
theorem deriv_cutoff_sq_le (L scale t : ℝ) :
    deriv (cutoff L scale) t ^ 2 ≤
      2 * scale ^ 2 * (Real.exp (-(2 * scale) * t) + Real.exp (-(2 * scale) * (L - t))) := by
  rw [(hasDerivAt_cutoff L scale t).deriv]
  have hsq (u : ℝ) : Real.exp (-(2 * scale) * u) = Real.exp (-scale * u) ^ 2 := by
    rw [show -(2 * scale) * u = 2 * (-scale * u) by ring]
    exact Real.exp_nat_mul (-scale * u) 2
  rw [hsq, hsq]
  nlinarith [sq_nonneg (scale * (Real.exp (-scale * t) + Real.exp (-scale * (L - t))))]

/-- The integrated squared derivative is at most `2*scale` at any nonnegative scale.
The oriented integral permits arbitrary real interval length, including reversed intervals. -/
theorem integral_deriv_cutoff_sq_le {L scale : ℝ} (hscale : 0 ≤ scale) :
    (∫ t : ℝ in 0..L, deriv (cutoff L scale) t ^ 2) ≤ 2 * scale := by
  rcases hscale.eq_or_lt with hs | hs
  · subst scale
    simp_rw [(hasDerivAt_cutoff L 0 _).deriv]
    simp
  by_cases hL : 0 ≤ L
  swap
  · rw [integral_symm]
    exact (neg_nonpos.mpr (integral_nonneg_of_forall (le_of_not_ge hL)
      (fun t ↦ sq_nonneg (deriv (cutoff L scale) t)))).trans (by positivity)
  have h := integral_le_exp_pair (scale := 2 * scale) (K := 2 * scale ^ 2)
    hL (by positivity) (by positivity)
    (fun t _ ↦ deriv_cutoff_sq_le L scale t)
  exact h.trans_eq (by field_simp [hs.ne'])

/-- Removing the squared cutoff from a function bounded above by a nonnegative constant
costs at most `4 * K / scale` in its integral. No integrability of the defect is assumed. -/
theorem integral_mul_defect_le {f : ℝ → ℝ} {L scale K : ℝ}
    (hL : 0 ≤ L) (hscale : 0 < scale) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc 0 L, f t ≤ K) :
    (∫ t : ℝ in 0..L, (1 - cutoff L scale t ^ 2) * f t) ≤ K * (4 / scale) := by
  by_cases hf : IntervalIntegrable
      (fun t ↦ (1 - cutoff L scale t ^ 2) * f t) volume 0 L
  swap
  · rw [integral_undef hf]
    positivity
  have hcont : Continuous (fun t ↦ K * (1 - cutoff L scale t ^ 2)) :=
    continuous_const.mul (continuous_const.sub ((contDiff_cutoff L scale).continuous.pow 2))
  calc
    _ ≤ ∫ t : ℝ in 0..L, K * (1 - cutoff L scale t ^ 2) := by
      apply integral_mono_on hL hf (hcont.intervalIntegrable 0 L)
      intro t ht
      have hφ := cutoff_mem_Icc hscale.le ht
      have hdef : 0 ≤ 1 - cutoff L scale t ^ 2 := by nlinarith [hφ.1, hφ.2]
      simpa only [mul_comm K] using mul_le_mul_of_nonneg_left (hbound t ht) hdef
    _ = K * ∫ t : ℝ in 0..L, 1 - cutoff L scale t ^ 2 := integral_const_mul _ _
    _ ≤ K * (4 / scale) :=
      mul_le_mul_of_nonneg_left (integral_cutoff_defect_le hL hscale) hK

/-- A bound for a squared-cutoff integral gives a length-independent bound for the
unweighted integral when the integrand has a nonnegative upper bound. -/
theorem integral_le_of_integral_cutoff_sq_mul_le {f : ℝ → ℝ} {L scale K C : ℝ}
    (hL : 0 ≤ L) (hscale : 0 < scale) (hK : 0 ≤ K)
    (hf : IntervalIntegrable f volume 0 L) (hbound : ∀ t ∈ Icc 0 L, f t ≤ K)
    (hweighted : (∫ t : ℝ in 0..L, cutoff L scale t ^ 2 * f t) ≤ C) :
    (∫ t : ℝ in 0..L, f t) ≤ C + K * (4 / scale) := by
  have hφ : Continuous (fun t : ℝ ↦ cutoff L scale t ^ 2) :=
    (contDiff_cutoff L scale).continuous.pow 2
  have hdef : Continuous (fun t : ℝ ↦ 1 - cutoff L scale t ^ 2) :=
    continuous_const.sub hφ
  have hsplit : (∫ t : ℝ in 0..L, f t) =
      (∫ t : ℝ in 0..L, cutoff L scale t ^ 2 * f t) +
        ∫ t : ℝ in 0..L, (1 - cutoff L scale t ^ 2) * f t := by
    rw [← intervalIntegral.integral_add (hf.continuousOn_mul hφ.continuousOn)
      (hf.continuousOn_mul hdef.continuousOn)]
    congr 1
    ext t
    ring
  rw [hsplit]
  exact add_le_add hweighted (integral_mul_defect_le hL hscale hK hbound)

end TauCeti.ExponentialCutoff

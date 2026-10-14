/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Analysis.Contour.Winding.Number.Segment.Formula
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.Complex.WindingNormalization
import Mathlib.Analysis.Calculus.Deriv.Linear
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Reparam
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Convex.Segment

/-!
# Winding bounds for a straight segment

The winding real part of an oriented segment at a point strictly to its left lies between zero
and one half. Positivity follows from the imaginary part of the reciprocal kernel; the logarithm
formula bounds the argument increment by `π`. Affine reparametrization preserves the index
and reversal negates it away from the segment.
-/

public section

open Complex MeasureTheory Set
namespace TauCeti.Contour
private theorem windingNumber_unitSegment_re_bounds {q : ℂ} (hq : 0 < q.im) :
    0 < (windingNumber (fun t : ℝ ↦ (t : ℂ)) 0 1 q).re ∧
    (windingNumber (fun t : ℝ ↦ (t : ℂ)) 0 1 q).re < 1 / 2 := by
  have hn := windingNumber_segment_of_im_ne_zero (a := 0) (b := 1)
    (v := 1) (z₀ := 0) one_ne_zero hq.ne'
  simp only [one_mul, add_zero, Complex.ofReal_zero, Complex.ofReal_one] at hn
  have hupper : (windingNumber (fun t : ℝ ↦ (t : ℂ)) 0 1 q).re < 1 / 2 := by
    rw [hn, Complex.re_inv_two_pi_I_mul, Complex.sub_im, Complex.log_im, Complex.log_im]
    have h1 : arg (1 - q) < 0 := arg_neg_iff.mpr (by simp; linarith)
    have h0 := neg_pi_lt_arg (0 - q)
    apply (div_lt_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr
    linarith
  have hne (t : ℝ) : (t : ℂ) - q ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    linarith
  have hf : Continuous (fun t : ℝ ↦ ((t : ℂ) - q)⁻¹) :=
    ((Complex.continuous_ofReal).sub continuous_const).inv₀ hne
  have hfi : IntervalIntegrable (fun t : ℝ ↦ ((t : ℂ) - q)⁻¹) volume 0 1 :=
    hf.continuousOn.intervalIntegrable
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      (Complex.ofRealCLM.hasDerivAt (x := t))
  have hh : windingNumber (fun t : ℝ ↦ (t : ℂ)) 0 1 q =
      (2 * (Real.pi : ℂ) * I)⁻¹ * ∫ t in (0 : ℝ)..1, ((t : ℂ) - q)⁻¹ := by
    apply (windingNumber_eq_integral_of_avoidance
      Complex.continuous_ofReal.continuousOn (fun t _ ↦ sub_ne_zero.mp (hne t)) ?_).trans
    · exact congrArg (fun w ↦ (2 * (Real.pi : ℂ) * I)⁻¹ * w)
        (intervalIntegral.integral_congr fun t _ ↦ by
          rw [(hd t).deriv, mul_one])
    · exact hfi.congr fun t _ ↦ by rw [(hd t).deriv, mul_one]
  have hpos (t : ℝ) : 0 < (((t : ℂ) - q)⁻¹).im := by
    rw [Complex.inv_im]
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
    exact div_pos hq (Complex.normSq_pos.mpr (hne t))
  have hInt : 0 < ∫ t in (0 : ℝ)..1, (((t : ℂ) - q)⁻¹).im :=
    intervalIntegral.integral_pos zero_lt_one (Complex.continuous_im.comp hf).continuousOn
      (fun t _ ↦ (hpos t).le) ⟨0, ⟨le_rfl, zero_le_one⟩, hpos 0⟩
  refine ⟨?_, hupper⟩
  rw [hh, Complex.re_inv_two_pi_I_mul]
  have hIm : (∫ t in (0 : ℝ)..1, ((t : ℂ) - q)⁻¹).im =
      ∫ t in (0 : ℝ)..1, (((t : ℂ) - q)⁻¹).im :=
    (intervalIntegral.intervalIntegral_im hfi).symm
  rw [hIm]
  exact div_pos hInt (mul_pos (by norm_num) Real.pi_pos)

/-- A point strictly left of a directed segment has winding real part between zero and one half. -/
theorem windingNumber_segment_re_mem_Ioo {p q z : ℂ} (hleft : 0 < ((z - p) / (q - p)).im) :
    (windingNumber (fun t : ℝ ↦ p + t • (q - p)) 0 1 z).re ∈ Ioo 0 (1 / 2) := by
  have hv : q - p ≠ 0 := by
    intro h
    simp only [h, div_zero, Complex.zero_im] at hleft
    exact hleft.false
  have he : windingNumber (fun t : ℝ ↦ p + t • (q - p)) 0 1 z =
      windingNumber (fun t : ℝ ↦ (t : ℂ)) 0 1 ((z - p) / (q - p)) := by
    calc
      _ = windingNumber (fun t : ℝ ↦ (q - p) * (t : ℂ) + p) 0 1 z := by
        apply windingNumber_congr_curve
        intro t _
        simp only [Complex.real_smul]
        ring
      _ = windingNumber (fun t : ℝ ↦ (t : ℂ)) 0 1 ((q - p)⁻¹ * (z - p)) :=
        windingNumber_affine_preimage hv
      _ = _ := by rw [div_eq_mul_inv, mul_comm]
  rw [he]
  exact windingNumber_unitSegment_re_bounds hleft

private theorem absolutelyContinuous_segment (p q : ℂ) :
    AbsolutelyContinuousOnInterval (fun t : ℝ ↦ p + t • (q - p)) 0 1 :=
  (show ContDiffOn ℝ 1 (fun t : ℝ ↦ p + t • (q - p)) (uIcc 0 1) from
    by fun_prop).absolutelyContinuousOnInterval

private theorem notMem_segment_trace {p q z : ℂ} (hz : z ∉ segment ℝ p q) :
    z ∉ (fun t : ℝ ↦ p + t • (q - p)) '' uIcc 0 1 := by
  simpa only [uIcc_of_le zero_le_one, ← segment_eq_image'] using hz

/-- An increasing affine parametrization preserves the winding number of a straight segment. -/
theorem windingNumber_segment_interval {p q z : ℂ} {a b : ℝ} (hab : a < b)
    (hz : z ∉ segment ℝ p q) :
    windingNumber (fun t : ℝ ↦ p + ((t - a) / (b - a)) • (q - p)) a b z =
      windingNumber (fun t : ℝ ↦ p + t • (q - p)) 0 1 z := by
  let θ := fun t : ℝ ↦ (t - a) / (b - a)
  have hγ := absolutelyContinuous_segment p q
  have hθ : AbsolutelyContinuousOnInterval θ a b := by
    have h : ContDiffOn ℝ 1 θ (uIcc a b) := by dsimp [θ]; fun_prop
    exact h.absolutelyContinuousOnInterval
  have hmono : MonotoneOn θ (Icc a b) := by
    intro x _ y _ hxy
    exact div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_pos.mpr hab).le
  have havoid := notMem_segment_trace hz
  exact AbsolutelyContinuousOnInterval.windingNumber_comp_of_monotoneOn
    hγ hθ hab.le hmono (by simp) (by simp [(sub_pos.mpr hab).ne']) havoid

/-- Reversing a straight segment negates its winding number away from that segment. -/
theorem windingNumber_segment_swap {p q z : ℂ} (hz : z ∉ segment ℝ p q) :
    windingNumber (fun t : ℝ ↦ q + t • (p - q)) 0 1 z =
      -windingNumber (fun t : ℝ ↦ p + t • (q - p)) 0 1 z := by
  have hγ := absolutelyContinuous_segment p q
  have hθ : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ 1 - t) 0 1 := by
    have h : ContDiffOn ℝ 1 (fun t : ℝ ↦ 1 - t) (uIcc 0 1) := by fun_prop
    exact h.absolutelyContinuousOnInterval
  have h := hγ.windingNumber_comp_of_antitoneOn hθ
    zero_le_one (fun x _ y _ hxy ↦ sub_le_sub_left hxy 1) (by norm_num) (by norm_num)
    (notMem_segment_trace hz)
  apply Eq.trans _ h
  apply windingNumber_congr_curve
  intro t _
  simp only [Function.comp_apply, Complex.real_smul]
  push_cast
  ring

end TauCeti.Contour

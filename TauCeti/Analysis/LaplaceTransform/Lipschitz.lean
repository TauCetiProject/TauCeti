/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Laplace integrability of Lipschitz functions

On the nonnegative ray, Lipschitz control bounds growth by an affine function. Hence one-sided
Laplace integrals of such functions converge absolutely at every rate with positive real part.
-/

public section

open MeasureTheory Set
open scoped NNReal

/-- A function Lipschitz on the nonnegative ray is integrable there after exponential damping
at any complex rate with positive real part. -/
theorem LipschitzOnWith.integrableOn_cexp_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {K : ℝ≥0} {f : ℝ → E} {s : ℂ}
    (hf : LipschitzOnWith K f (Ici 0)) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ ↦ Complex.exp (-s * t) • f t) (Ioi 0) := by
  have hconst := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).const_mul ‖f 0‖
  have hlin := (TauCeti.integrableOn_pow_mul_exp_neg_mul_Ioi 1 hs).const_mul (K : ℝ)
  refine (hconst.add hlin).mono' ?_ ?_
  · have he : Continuous (fun t : ℝ ↦ Complex.exp (-s * t)) := by fun_prop
    exact (he.continuousOn.smul (hf.mono Ioi_subset_Ici_self).continuousOn)
      |>.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₀ : 0 ≤ t := (mem_Ioi.mp ht).le
    have hsub : ‖f t - f 0‖ ≤ (K : ℝ) * t := by
      simpa [Real.norm_of_nonneg ht₀] using
        (lipschitzOnWith_iff_norm_sub_le.mp hf) (x := t) ht₀ (y := 0) (by simp)
    have hnorm : ‖f t‖ ≤ ‖f 0‖ + (K : ℝ) * t := calc
      ‖f t‖ ≤ ‖f 0‖ + ‖f t - f 0‖ := norm_le_norm_add_norm_sub' ..
      _ ≤ _ := add_le_add_right hsub _
    simp only [Pi.add_apply, norm_smul, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul, pow_one]
    calc
      Real.exp (-(s.re * t)) * ‖f t‖ ≤ Real.exp (-(s.re * t)) * (‖f 0‖ + (K : ℝ) * t) := by
        gcongr
      _ = _ := by ring

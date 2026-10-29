/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CurveIntegral.Basic
public import TauCeti.Analysis.Calculus.Deriv.Complex
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Planar circulation and curl

The oriented real plane is `ℂ`, with positive basis `(1, Complex.I)`. The circulation of a
field with components `P, Q` uses the real 1-form `P dx + Q dy`; its curl is `∂x Q - ∂y P`.
The raw-curve integrand agrees with Mathlib's `curveIntegral` on a `Path`, including for paths
whose derivative is defined only almost everywhere.

These conventions fix the signs for planar Green identities.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- The real 1-form `P dx + Q dy` on the positively oriented complex plane. -/
def oneForm (P Q : ℂ → ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  P z • Complex.reCLM + Q z • Complex.imCLM

/-- Evaluation of the planar 1-form in real coordinates. -/
@[simp]
theorem oneForm_apply (P Q : ℂ → ℝ) (z v : ℂ) :
    oneForm P Q z v = P z * v.re + Q z * v.im := by
  simp [oneForm]

/-- The planar 1-form as a field of continuous linear maps in the coordinate projections. -/
theorem oneForm_eq_clm (P Q : ℂ → ℝ) :
    oneForm P Q = fun z ↦ P z • Complex.reCLM + Q z • Complex.imCLM := by
  ext z v
  simp [oneForm_apply]

/-- A continuous planar field gives a continuous field of real linear 1-forms. -/
theorem _root_.Continuous.oneForm {P Q : ℂ → ℝ} (hP : Continuous P) (hQ : Continuous Q) :
    Continuous (oneForm P Q) := by
  rw [oneForm_eq_clm]
  exact (hP.smul continuous_const).add (hQ.smul continuous_const)

/-- A continuous compactly supported planar field has uniformly bounded 1-form operator norm. -/
theorem exists_bound_oneForm {P Q : ℂ → ℝ}
    (hP : Continuous P) (hQ : Continuous Q)
    (hcP : HasCompactSupport P) (hcQ : HasCompactSupport Q) :
    ∃ C, ∀ z, ‖oneForm P Q z‖ ≤ C := by
  obtain ⟨CP, hCP⟩ := hcP.exists_bound_of_continuous hP
  obtain ⟨CQ, hCQ⟩ := hcQ.exists_bound_of_continuous hQ
  refine ⟨CP * ‖Complex.reCLM‖ + CQ * ‖Complex.imCLM‖, fun z ↦ ?_⟩
  rw [oneForm_eq_clm]
  exact (norm_add_le _ _).trans (by
    simp only [norm_smul]
    gcongr
    · exact hCP z
    · exact hCQ z)

/-- The integrand of circulation along a raw curve on an oriented real interval. -/
@[expose]
def circulationFun (P Q : ℂ → ℝ) (γ : ℝ → ℂ) (t : ℝ) : ℝ :=
  P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im

/-- The raw circulation integrand is the planar 1-form applied to the velocity. -/
theorem circulationFun_eq_oneForm (P Q : ℂ → ℝ) (γ : ℝ → ℂ) (t : ℝ) :
    circulationFun P Q γ t = oneForm P Q (γ t) (deriv γ t) := by
  simp [circulationFun]

/-- Curl in the positive real basis `(1, Complex.I)`. These are real Fréchet derivatives,
so this definition is used for differentiable fields; directional Green identities state
their slice derivatives separately. -/
@[expose]
def curl (P Q : ℂ → ℝ) (z : ℂ) : ℝ :=
  fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I

/-- Globally real `C¹` fields have continuous curl. -/
theorem _root_.ContDiff.continuous_curl {P Q : ℂ → ℝ} (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    Continuous (curl P Q) := by
  have heq : curl P Q = fun z ↦ fderiv ℝ Q z 1 - fderiv ℝ P z Complex.I :=
    rfl
  rw [heq]
  exact ((ContinuousLinearMap.apply ℝ ℝ 1).continuous.comp
    (hQ.continuous_fderiv (by simp))).sub
      ((ContinuousLinearMap.apply ℝ ℝ Complex.I).continuous.comp
        (hP.continuous_fderiv (by simp)))

/-- Compact support of the field implies compact support of its curl. -/
theorem _root_.HasCompactSupport.curl {P Q : ℂ → ℝ}
    (hcP : HasCompactSupport P) (hcQ : HasCompactSupport Q) : HasCompactSupport (curl P Q) := by
  have hQ := (hcQ.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ ↦ L 1) (by simp)
  have hP := (hcP.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ ↦ L Complex.I) (by simp)
  convert hQ.sub hP using 1
  ext z
  rfl

/-- For differentiable fields the curl agrees with the difference of the directional slice
derivatives used in the graph-cell identities. -/
theorem curl_eq_deriv_slices {P Q : ℂ → ℝ} {z : ℂ}
    (hP : DifferentiableAt ℝ P z) (hQ : DifferentiableAt ℝ Q z) :
    curl P Q z = deriv (fun x : ℝ ↦ Q ⟨x, z.im⟩) z.re -
      deriv (fun y : ℝ ↦ P ⟨z.re, y⟩) z.im := by
  rw [curl, hQ.hasFDerivAt.hasDerivAt_re_slice.deriv,
    hP.hasFDerivAt.hasDerivAt_im_slice.deriv]

/-- Mathlib's curve integral is the circulation integral in real coordinates. -/
theorem curveIntegral_oneForm_eq {p q : ℂ} (γ : Path p q) (P Q : ℂ → ℝ) :
    curveIntegral (oneForm P Q) γ =
      ∫ t in (0 : ℝ)..1, circulationFun P Q γ.extend t := by
  rw [curveIntegral_eq_intervalIntegral_deriv]
  simp only [← circulationFun_eq_oneForm]

/-- Continuous coefficients are genuinely Bochner integrable along a straight segment. -/
theorem intervalIntegrable_circulationFun_segment {p q : ℂ} {P Q : ℂ → ℝ}
    (hP : ContinuousOn P (segment ℝ p q)) (hQ : ContinuousOn Q (segment ℝ p q)) :
    IntervalIntegrable (circulationFun P Q (Path.segment p q).extend) volume 0 1 := by
  have hc : CurveIntegrable (oneForm P Q) (Path.segment p q) := by
    rw [curveIntegrable_segment]
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    have hm : Set.MapsTo (AffineMap.lineMap p q) (Set.Icc (0 : ℝ) 1) (segment ℝ p q) :=
      fun _ ht ↦ (convex_segment p q).lineMap_mem (left_mem_segment ℝ p q)
        (right_mem_segment ℝ p q) ht
    simpa only [oneForm_apply, Pi.add_def, Pi.mul_def, Function.comp_apply] using
      ((hP.comp (by fun_prop) hm).mul continuousOn_const).add
        ((hQ.comp (by fun_prop) hm).mul continuousOn_const)
  simpa only [← circulationFun_eq_oneForm] using
    (curveIntegrable_iff_intervalIntegrable_deriv _ _).mp hc

end TauCeti.Green

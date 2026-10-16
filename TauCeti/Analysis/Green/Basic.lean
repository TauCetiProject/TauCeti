/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import TauCeti.Analysis.Calculus.Deriv.Complex

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
    have hp := hP.comp (by fun_prop) hm
    have hq := hQ.comp (by fun_prop) hm
    simpa only [oneForm_apply, Pi.add_def, Pi.mul_def, Function.comp_apply] using
      (hp.mul continuousOn_const).add (hq.mul continuousOn_const)
  apply (intervalIntegrable_congr_ae ?_).mpr hc
  rw [uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [curveIntegralFun_def, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  exact circulationFun_eq_oneForm P Q (Path.segment p q).extend t

end TauCeti.Green

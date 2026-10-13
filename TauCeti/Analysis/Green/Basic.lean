/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Planar circulation and curl

The oriented real plane is `ℂ`, with positive basis `(1, Complex.I)`. The circulation of a
field with components `P, Q` uses the real 1-form `P dx + Q dy`; its curl is `∂x Q - ∂y P`.
The raw-curve integrand agrees with Mathlib's `curveIntegral` on a `Path`, including for paths
whose derivative is defined only almost everywhere. No new integral is introduced.

These conventions fix the signs for planar Green identities and their flux form.
-/

public section

noncomputable section

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
def circulationFun (P Q : ℂ → ℝ) (γ : ℝ → ℂ) (t : ℝ) : ℝ :=
  P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im

/-- The raw circulation integrand is the planar 1-form applied to the velocity. -/
theorem circulationFun_eq_oneForm (P Q : ℂ → ℝ) (γ : ℝ → ℂ) (t : ℝ) :
    circulationFun P Q γ t = oneForm P Q (γ t) (deriv γ t) := by
  simp [circulationFun]

/-- Coordinate formula for the raw circulation integrand. -/
theorem circulationFun_def (P Q : ℂ → ℝ) (γ : ℝ → ℂ) (t : ℝ) :
    circulationFun P Q γ t = P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im :=
  (rfl)

/-- Curl in the positive real basis `(1, Complex.I)`. These are real Fréchet derivatives,
so this definition is used for differentiable fields; directional Green identities state
their slice derivatives separately. -/
def curl (P Q : ℂ → ℝ) (z : ℂ) : ℝ :=
  fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I

/-- The curl of `P dx + Q dy` is `∂x Q - ∂y P`. -/
theorem curl_def (P Q : ℂ → ℝ) (z : ℂ) :
    curl P Q z = fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I :=
  (rfl)

/-- Mathlib's curve integral is the circulation integral in real coordinates. The endpoint
difference between `derivWithin` and `deriv` is already handled by Mathlib's integral API. -/
theorem curveIntegral_oneForm_eq {p q : ℂ} (γ : Path p q) (P Q : ℂ → ℝ) :
    curveIntegral (oneForm P Q) γ =
      ∫ t in (0 : ℝ)..1, circulationFun P Q γ.extend t := by
  rw [curveIntegral_eq_intervalIntegral_deriv]
  simp only [← circulationFun_eq_oneForm]

end TauCeti.Green

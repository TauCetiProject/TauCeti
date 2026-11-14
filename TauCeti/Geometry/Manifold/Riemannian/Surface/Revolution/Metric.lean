/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Revolution.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
public import TauCeti.Topology.Algebra.Module.BilinearForm
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The metric and Christoffel symbols of a surface of revolution

The metric in the original profile parameter is `f² du² + (f'² + g'²) dv²`.
The formulas below compute the native Christoffel symbols from this metric,
including the meridional coefficient for a profile not parametrized by arclength.
-/

public noncomputable section

open scoped ContDiff
open ContinuousLinearMap

namespace TauCeti.SurfaceOfRevolution

private def angularForm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
  (fst ℝ ℝ ℝ).smulRight (fst ℝ ℝ ℝ)

private def meridionalForm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
  (snd ℝ ℝ ℝ).smulRight (snd ℝ ℝ ℝ)

/-- The metric coefficients of the first fundamental form as a continuous bilinear form. -/
def metric (f g : ℝ → ℝ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
  f p.2 ^ 2 • angularForm + profileSpeedSq f g p.2 • meridionalForm

/-- Evaluation of the metric in the angular and profile coordinate directions. -/
@[simp]
theorem metric_apply (f g : ℝ → ℝ) (p w z : ℝ × ℝ) :
    metric f g p w z = f p.2 ^ 2 * w.1 * z.1 + profileSpeedSq f g p.2 * w.2 * z.2 := by
  simp [metric, angularForm, meridionalForm, mul_assoc]

/-- This bilinear form is exactly the Euclidean inner product pulled back by the
parametrization. -/
theorem metric_eq_inner_fderiv {f g : ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p.2) (hg : DifferentiableAt ℝ g p.2) (w z : ℝ × ℝ) :
    metric f g p w z =
      inner ℝ (fderiv ℝ (parametrization f g) p w)
        (fderiv ℝ (parametrization f g) p z) := by
  rw [metric_apply, inner_fderiv_parametrization hf hg]

/-- The first fundamental form is nondegenerate at every regular profile point of nonzero
radius. -/
theorem metric_nondegenerate {f g : ℝ → ℝ} {p : ℝ × ℝ}
    (hr : f p.2 ≠ 0) (hs : profileSpeedSq f g p.2 ≠ 0) :
    (metric f g p).toBilinForm.Nondegenerate := by
  apply (metric f g p).nondegenerate_toBilinForm_iff_injective.mpr
  intro w z hwz
  apply Prod.ext
  · apply mul_left_cancel₀ (pow_ne_zero 2 hr)
    simpa using DFunLike.congr_fun hwz (1, 0)
  · apply mul_left_cancel₀ hs
    simpa using DFunLike.congr_fun hwz (0, 1)

/-- The derivative of the profile-speed coefficient in an arbitrary profile parameter. -/
theorem hasDerivAt_profileSpeedSq {f g : ℝ → ℝ} {v : ℝ}
    (hf : DifferentiableAt ℝ (deriv f) v) (hg : DifferentiableAt ℝ (deriv g) v) :
    HasDerivAt (profileSpeedSq f g)
      (2 * (deriv f v * deriv (deriv f) v + deriv g v * deriv (deriv g) v)) v := by
  have heq : profileSpeedSq f g = fun t ↦ deriv f t ^ 2 + deriv g t ^ 2 :=
    funext (profileSpeedSq_def f g)
  rw [heq]
  convert (hf.hasDerivAt.pow 2).add (hg.hasDerivAt.pow 2) using 1
  norm_num
  ring

/-- The differential of the actual first fundamental form, including its profile-speed
derivative. -/
theorem fderiv_metric {f g : ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p.2)
    (hff : DifferentiableAt ℝ (deriv f) p.2)
    (hgg : DifferentiableAt ℝ (deriv g) p.2) (w z q : ℝ × ℝ) :
    fderiv ℝ (metric f g) p w z q =
      2 * f p.2 * deriv f p.2 * w.2 * z.1 * q.1 +
      2 * (deriv f p.2 * deriv (deriv f) p.2 + deriv g p.2 * deriv (deriv g) p.2) *
        w.2 * z.2 * q.2 := by
  let : NormedSpace ℝ ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ) := inferInstance
  have ha := (hf.hasDerivAt.pow 2).hasFDerivAt.comp p hasFDerivAt_snd
  have hb := (hasDerivAt_profileSpeedSq hff hgg).hasFDerivAt.comp p hasFDerivAt_snd
  have hd : HasFDerivAt (metric f g) _ p :=
    (ha.smul_const angularForm).add (hb.smul_const meridionalForm)
  rw [hd.fderiv]
  simp [angularForm, meridionalForm, mul_assoc, mul_left_comm, mul_comm]

/-- All Christoffel symbols at once, as the native Christoffel bilinear map. This includes
`Γ¹₁₂ = Γ¹₂₁ = f'/f`, `Γ²₁₁ = -ff'/(f'²+g'²)` and
`Γ²₂₂ = (f'f''+g'g'')/(f'²+g'²)`; the other coefficients vanish. -/
theorem christoffelSecondKind_metric {f g : ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p.2)
    (hff : DifferentiableAt ℝ (deriv f) p.2)
    (hgg : DifferentiableAt ℝ (deriv g) p.2)
    (hr : f p.2 ≠ 0) (hs : profileSpeedSq f g p.2 ≠ 0) (w z : ℝ × ℝ) :
    Manifold.christoffelSecondKind (metric f g) p w z =
      (deriv f p.2 / f p.2 * (w.1 * z.2 + w.2 * z.1),
        -(f p.2 * deriv f p.2) / profileSpeedSq f g p.2 * w.1 * z.1 +
          (deriv f p.2 * deriv (deriv f) p.2 + deriv g p.2 * deriv (deriv g) p.2) /
            profileSpeedSq f g p.2 * w.2 * z.2) := by
  have hnd := metric_nondegenerate hr hs
  have h₁ := Manifold.apply_christoffelSecondKind hnd w z (1, 0)
  have h₂ := Manifold.apply_christoffelSecondKind hnd w z (0, 1)
  simp only [metric_apply, Manifold.christoffelFirstKind_apply,
    fderiv_metric hf hff hgg] at h₁ h₂
  apply Prod.ext
  · rw [div_mul_eq_mul_div, eq_div_iff hr]
    apply mul_left_cancel₀ hr
    nlinarith [h₁]
  · apply mul_left_cancel₀ hs
    field_simp [hs]
    nlinarith [h₂]

end TauCeti.SurfaceOfRevolution

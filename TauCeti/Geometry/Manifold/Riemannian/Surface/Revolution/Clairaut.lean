/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Revolution.Metric
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Clairaut's integral in revolution coordinates

The angular geodesic equation implies that `f(v)² u'` is constant on a connected parameter
interval. For a unit-speed curve this is `f(v) cos β`, where `β` is the actual Euclidean
angle between its immersed velocity and the positive parallel direction. The coordinate
equation used in the calculus lemmas is kept explicit.
-/

public noncomputable section

open scoped InnerProductSpace

namespace TauCeti.SurfaceOfRevolution

/-- The angular geodesic equation makes the derivative of Clairaut's integral vanish. -/
theorem hasDerivAt_angularMomentum_eq_zero {f a v : ℝ → ℝ} {t a' v' : ℝ}
    (hf : DifferentiableAt ℝ f (v t)) (ha : HasDerivAt a a' t)
    (hv : HasDerivAt v v' t) (hr : f (v t) ≠ 0)
    (heq : a' + 2 * (deriv f (v t) / f (v t)) * a t * v' = 0) :
    HasDerivAt (fun s ↦ f (v s) ^ 2 * a s) 0 t := by
  have hz : 2 * f (v t) * deriv f (v t) * v' * a t + f (v t) ^ 2 * a' = 0 := by
    calc
      _ = f (v t) ^ 2 *
          (a' + 2 * (deriv f (v t) / f (v t)) * a t * v') := by
        field_simp
        ring
      _ = 0 := by rw [heq, mul_zero]
  have hd := ((hf.hasDerivAt.comp t hv).pow 2).mul ha
  have hz' : 2 * f (v t) ^ (2 - 1) * (deriv f (v t) * v') * a t + f (v t) ^ 2 * a' = 0 := by
    norm_num
    nlinarith [hz]
  exact hd.congr_deriv hz'

/-- Clairaut's coordinate integral is constant on any open connected parameter set on which
the angular geodesic equation holds. -/
theorem angularMomentum_eq_of_coordinateEquation {f u v : ℝ → ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hc : IsPreconnected s)
    (hf : ∀ t ∈ s, DifferentiableAt ℝ f (v t))
    (hu : ∀ t ∈ s, DifferentiableAt ℝ (deriv u) t)
    (hv : ∀ t ∈ s, DifferentiableAt ℝ v t)
    (hr : ∀ t ∈ s, f (v t) ≠ 0)
    (heq : ∀ t ∈ s,
      deriv (deriv u) t + 2 * (deriv f (v t) / f (v t)) * deriv u t * deriv v t = 0)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    f (v a) ^ 2 * deriv u a = f (v b) ^ 2 * deriv u b := by
  have hd (t : ℝ) (ht : t ∈ s) :=
    hasDerivAt_angularMomentum_eq_zero (hf t ht) (hu t ht).hasDerivAt
      (hv t ht).hasDerivAt (hr t ht) (heq t ht)
  exact hs.is_const_of_deriv_eq_zero hc
    (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hd t ht).deriv) ha hb

/-- The geometric form of Clairaut's quantity: at unit speed, radius times the cosine of
the angle with the positive parallel is radius squared times angular velocity. -/
theorem radius_mul_cos_angle {f g : ℝ → ℝ} {p w : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p.2) (hg : DifferentiableAt ℝ g p.2)
    (hr : 0 < f p.2) (hw : ‖fderiv ℝ (parametrization f g) p w‖ = 1) :
    f p.2 * Real.cos (InnerProductGeometry.angle
      (fderiv ℝ (parametrization f g) p w)
      (fderiv ℝ (parametrization f g) p (1, 0))) = f p.2 ^ 2 * w.1 := by
  have hinner := inner_fderiv_parametrization hf hg (1, 0) (1, 0)
  rw [real_inner_self_eq_norm_sq] at hinner
  have hp : ‖fderiv ℝ (parametrization f g) p (1, 0)‖ = f p.2 := by
    nlinarith [hinner, norm_nonneg (fderiv ℝ (parametrization f g) p (1, 0))]
  have hangle := InnerProductGeometry.cos_angle_mul_norm_mul_norm
    (fderiv ℝ (parametrization f g) p w) (fderiv ℝ (parametrization f g) p (1, 0))
  rw [hw, hp, inner_fderiv_parametrization hf hg] at hangle
  nlinarith [hangle]

end TauCeti.SurfaceOfRevolution

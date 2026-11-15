/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Revolution.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Clairaut's integral in revolution coordinates

The angular geodesic equation implies that `f(v)² u'` is constant on a connected parameter
interval. For a unit-speed curve with positive radius this is `f(v) cos β`, where `β` is the
actual Euclidean angle between its immersed velocity and the positive parallel direction.
The coordinate equation used in the calculus lemmas is kept explicit.

Ported from Yangyang Li's formalization in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory/tree/b442a9f3077a4be3823b712ec92b2335dd34e771/ForTauCeti/Geometry/Manifold/Riemannian/Surface/Revolution).

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*,
  [electronic edition](https://academicweb.nd.edu/~lnicolae/Lectures.pdf),
  Example 5.1.16 and Theorem 5.1.17, pp. 211–212.
-/

public noncomputable section

open scoped InnerProductSpace

namespace TauCeti.SurfaceOfRevolution

/-- The angular momentum per unit mass: radius squared times angular velocity `ω`,
where `v` is the profile coordinate. -/
def angularMomentum (f : ℝ → ℝ) (v ω : ℝ) : ℝ :=
  f v ^ 2 * ω

/-- Angular momentum is radius squared times angular velocity. -/
@[simp]
theorem angularMomentum_def (f : ℝ → ℝ) (v ω : ℝ) :
    angularMomentum f v ω = f v ^ 2 * ω :=
  (rfl)

/-- The angular geodesic equation makes the derivative of Clairaut's integral vanish. -/
theorem hasDerivAt_angularMomentum_zero {f a v : ℝ → ℝ} {t a' v' : ℝ}
    (hf : DifferentiableAt ℝ f (v t)) (ha : HasDerivAt a a' t)
    (hv : HasDerivAt v v' t) (hr : f (v t) ≠ 0)
    (heq : a' + 2 * (deriv f (v t) / f (v t)) * a t * v' = 0) :
    HasDerivAt (fun s ↦ angularMomentum f (v s) (a s)) 0 t := by
  simp only [angularMomentum_def]
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
    linear_combination hz
  exact hd.congr_deriv hz'

/-- Clairaut's coordinate integral is constant on any open connected parameter set on which
the angular geodesic equation holds. -/
theorem angularMomentum_eq_of_coordinateEquation {f ω v : ℝ → ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hc : IsPreconnected s)
    (hf : ∀ t ∈ s, DifferentiableAt ℝ f (v t))
    (hω : ∀ t ∈ s, DifferentiableAt ℝ ω t)
    (hv : ∀ t ∈ s, DifferentiableAt ℝ v t)
    (hr : ∀ t ∈ s, f (v t) ≠ 0)
    (heq : ∀ t ∈ s,
      deriv ω t + 2 * (deriv f (v t) / f (v t)) * ω t * deriv v t = 0)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    angularMomentum f (v a) (ω a) = angularMomentum f (v b) (ω b) := by
  have hd (t : ℝ) (ht : t ∈ s) :=
    hasDerivAt_angularMomentum_zero (hf t ht) (hω t ht).hasDerivAt
      (hv t ht).hasDerivAt (hr t ht) (heq t ht)
  exact hs.is_const_of_deriv_eq_zero hc
    (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hd t ht).deriv) ha hb

/-- The geometric form of Clairaut's quantity: at unit speed, radius times the cosine of
the angle with the positive parallel is radius squared times angular velocity. -/
theorem radius_mul_cos_angle_eq_sq_mul_fst {f g : ℝ → ℝ} {p w : ℝ × ℝ}
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
  linear_combination hangle

end TauCeti.SurfaceOfRevolution

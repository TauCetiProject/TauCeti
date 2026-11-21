/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Curve.FrameCoordinates
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Geodesic curvature in an orthonormal frame

Let `z = ⟪e₀, γ'⟫ + i ⟪e₁, γ'⟫` be the velocity coordinates in an orthonormal frame,
and let `ω(X) = ⟪e₁, ∇_X e₀⟫` be its connection one-form. Differentiating the coordinates
gives `z' = (∇_t γ')₀ + i (∇_t γ')₁ - i ω(γ') z`.

For a positively oriented frame and a regular curve this implies
`k_g ‖γ'‖ = Im(z' / z) + ω(γ')`. Thus the geodesic curvature integral splits into the turning
of the tangent in the frame and the integral of the connection form. This is the boundary
identity used with the surface structure equation `dω = -K vol` in Gauss–Bonnet. The formula
allows arbitrary regular parametrizations and only needs the frame on an open neighborhood of
the point on the curve.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018,
  Chapter 9 (geodesic curvature and Gauss–Bonnet).
-/

public noncomputable section

open Bundle CovariantDerivative Filter TauCeti.Manifold
open scoped ContDiff Manifold Topology InnerProductSpace

namespace IsLocalFrameOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {s : Fin 2 → Π x : M, TangentSpace I x} {u : Set M}
  {γ : ℝ → M} {t : ℝ}

/-- The derivative of the complex velocity coordinates in an orthonormal local frame is the
coordinate covariant acceleration minus `i ω(γ') z`. This holds for any metric connection. -/
theorem hasDerivAt_frameVelocityCoordinates (hs : IsLocalFrameOn I E 1 s u)
    (hu : IsOpen u) (ho : ∀ x ∈ u, Orthonormal ℝ (fun i ↦ s i x))
    {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
    (hcov : IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov) (ht : γ t ∈ u)
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    HasDerivAt (frameVelocityCoordinates s γ)
      ((inner ℝ (s 0 (γ t)) (alongCurve cov γ (curveVelocity I γ) t) : ℂ) +
        (inner ℝ (s 1 (γ t)) (alongCurve cov γ (curveVelocity I γ) t) : ℂ) * Complex.I -
          Complex.I * (hs.connectionForm cov 0 1 (γ t) ![curveVelocity I γ t] : ℂ) *
            frameVelocityCoordinates s γ t) t := by
  have hγ₁ := hγ.mdifferentiableAt two_ne_zero
  have hframe (i : Fin 2) := (hs.contMDiffAt hu ht i).mdifferentiableAt one_ne_zero
  have hcoord (i : Fin 2) := differentiableAt_sectionCoord γ (fun r ↦ s i (γ r))
    ((hframe i).comp t hγ₁) (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hd (i : Fin 2) := hcov.hasDerivAt_inner_alongCurve hγ₁ (hcoord i)
    hγ.differentiableAt_sectionCoord_curveVelocity
  have hinner (i : Fin 2) :
      inner ℝ (alongCurve cov γ (fun r ↦ s i (γ r)) t) (curveVelocity I γ t) =
        (frameVelocityCoordinates s γ t).re *
          hs.coeff 0 (γ t) (cov (s i) (γ t) (curveVelocity I γ t)) +
        (frameVelocityCoordinates s γ t).im *
          hs.coeff 1 (γ t) (cov (s i) (γ t) (curveVelocity I γ t)) := by
    rw [alongCurve_pullback cov γ (s i) (hasMFDerivAt_curveVelocity hγ₁) (hframe i),
      real_inner_comm, curveVelocity_eq_frameVelocityCoordinates hs ht (ho _ ht)]
    simp [inner_add_left, real_inner_smul_left, ← hs.coeff_eq_inner ht (ho _ ht)]
  have h0 := hd 0
  have h1 := hd 1
  rw [hinner] at h0 h1
  simp only [Fin.isValue, mul_zero, add_zero, zero_add,
    hs.coeff_covariantDerivative_self_eq_zero le_rfl hu ho hcov] at h0 h1
  rw [hs.coeff_covariantDerivative_swap le_rfl hu ho hcov _ 0 1] at h1
  convert h0.ofReal_comp.add (h1.ofReal_comp.mul_const Complex.I) using 1
  · funext r
    simpa only [Pi.add_apply, frameVelocityCoordinates_re, frameVelocityCoordinates_im] using
      (Complex.re_add_im (frameVelocityCoordinates s γ r)).symm
  · simp only [connectionForm_apply, Matrix.cons_val_zero]
    apply Complex.ext <;> simp <;> ring

/-- **The boundary moving-frame formula.** For a regular curve in a positively oriented
orthonormal local frame, geodesic curvature times speed is the turning rate `Im(z' / z)` plus
the connection one-form evaluated on the velocity. No unit-speed assumption is needed. At a
stationary point both sides are zero with the totalized division convention. -/
theorem geodesicCurvature_mul_norm_curveVelocity_eq (hs : IsLocalFrameOn I E 1 s u)
    (hu : IsOpen u) (ho : ∀ x ∈ u, Orthonormal ℝ (fun i ↦ s i x))
    (o : TauCeti.Manifold.Orientation I M (Fin 2)) (ht : γ t ∈ u)
    (hor : s 1 (γ t) = (letI := o.fact_finrank_tangentSpace (γ t);
      (o.orientationAt (γ t)).rightAngleRotation (s 0 (γ t))))
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    geodesicCurvature γ (orientedUnitNormal o γ) t * ‖curveVelocity I γ t‖ =
      (deriv (frameVelocityCoordinates s γ) t / frameVelocityCoordinates s γ t).im +
        hs.connectionForm (leviCivitaConnection I M) 0 1 (γ t) ![curveVelocity I γ t] := by
  by_cases hv : curveVelocity I γ t = 0
  · have hz : frameVelocityCoordinates s γ t = 0 := by
      rw [← norm_eq_zero, norm_frameVelocityCoordinates hs ht (ho _ ht), hv, norm_zero]
    simp [hv, hz, connectionForm_apply]
  have hd := (hs.hasDerivAt_frameVelocityCoordinates hu ho
    (isMetricCompatible_leviCivitaConnection (I := I) (M := M)) ht hγ).deriv
  have hnorm : Complex.normSq (frameVelocityCoordinates s γ t) =
      ‖curveVelocity I γ t‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, norm_frameVelocityCoordinates hs ht (ho _ ht)]
  have hsq : (frameVelocityCoordinates s γ t).re ^ 2 +
      (frameVelocityCoordinates s γ t).im ^ 2 = ‖curveVelocity I γ t‖ ^ 2 := by
    simpa [Complex.normSq_apply, pow_two] using hnorm
  have hne : ‖curveVelocity I γ t‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [geodesicCurvature_def, orientedUnitNormal_eq_frameVelocityCoordinates o (ho _ ht) hor,
    inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_comm (s 0 (γ t)) (acceleration (leviCivitaConnection I M) γ t),
    real_inner_comm (s 1 (γ t)) (acceleration (leviCivitaConnection I M) γ t), hd, Complex.div_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, mul_zero, add_zero, zero_add, sub_zero, acceleration_def, hnorm]
  field_simp
  linear_combination
    hs.connectionForm (leviCivitaConnection I M) 0 1 (γ t) ![curveVelocity I γ t] * hsq

end IsLocalFrameOn

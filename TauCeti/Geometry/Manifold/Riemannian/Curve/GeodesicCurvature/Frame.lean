/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Curve.FrameCoordinates.Connection
public import TauCeti.Geometry.Manifold.Riemannian.Curve.FrameCoordinates.OrientedNormal

/-!
# Geodesic curvature in an orthonormal frame

Let `z = ⟪e₀, γ'⟫ + i ⟪e₁, γ'⟫` be the velocity coordinates of a curve in a positively oriented
orthonormal local frame of a surface, and let `ω(X) = ⟪e₁, ∇_X e₀⟫` be the connection one-form of
the Levi-Civita connection `∇`. Then `k_g ‖γ'‖ = Im(z' / z) + ω(γ')`
(`IsLocalFrameOn.geodesicCurvature_mul_norm_curveVelocity_eq`). Where `z ≠ 0`, `Im(z' / z)` is
the turning rate of the unit tangent read in the frame. The identity is pointwise; integrating it
along a regular `C²` arc in the frame domain splits the geodesic curvature integral over the arc
into the turning of the tangent in the frame and the integral of the connection form. Jumps of the
unit tangent between arcs, as at the corners of a piecewise regular curve, are not seen by this
integral and need separate treatment. This is the boundary identity used with the surface
structure equation `dω = -K vol` in Gauss–Bonnet.

The formula allows arbitrary parametrizations, including stationary points. There `Im(z' / z)` is
zero by the totalized division convention rather than a turning rate, and both sides vanish. It
needs the curve differentiable at `t`, with its velocity differentiable in the
tangent-bundle trivialization centered at `γ t`, and the frame only on an open neighborhood of
the point on the curve. The derivative of `z` itself holds for any metric connection
(`IsLocalFrameOn.hasDerivAt_frameVelocityCoordinates`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018,
  Chapter 9 (geodesic curvature and Gauss–Bonnet).
-/

public noncomputable section

open Bundle CovariantDerivative TauCeti.Manifold
open scoped Manifold

namespace IsLocalFrameOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {s : Fin 2 → Π x : M, TangentSpace I x} {u : Set M}
  {γ : ℝ → M} {t : ℝ}

/-- **The boundary moving-frame formula.** In a positively oriented orthonormal local frame,
geodesic curvature times speed is `Im(z' / z)` plus the Levi-Civita connection one-form evaluated
on the velocity. Where `z ≠ 0`, `Im(z' / z)` is the turning rate of the unit tangent in the frame.
The curve need only be differentiable at `t`, with its velocity differentiable in the
tangent-bundle trivialization centered at `γ t`, and no unit-speed assumption is needed. At a
stationary point `Im(z' / z)` is zero by the totalized division convention, and both sides are
zero. -/
theorem geodesicCurvature_mul_norm_curveVelocity_eq (hs : IsLocalFrameOn I E 1 s u)
    (hu : IsOpen u) (ho : ∀ x ∈ u, Orthonormal ℝ (fun i ↦ s i x))
    (o : TauCeti.Manifold.Orientation I M (Fin 2)) (ht : γ t ∈ u)
    (hor : s 1 (γ t) = (letI := o.fact_finrank_tangentSpace (γ t);
      (o.orientationAt (γ t)).rightAngleRotation (s 0 (γ t))))
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hγv : DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ (curveVelocity I γ) (γ t)) t) :
    geodesicCurvature γ (orientedUnitNormal o γ) t * ‖curveVelocity I γ t‖ =
      (deriv (frameVelocityCoordinates s γ) t / frameVelocityCoordinates s γ t).im +
        hs.connectionForm (leviCivitaConnection I M) 0 1 (γ t) ![curveVelocity I γ t] := by
  by_cases hv : curveVelocity I γ t = 0
  · simp [hv, connectionForm_apply]
  have hsp : curveVelocity I γ t ∈ Submodule.span ℝ (Set.range fun i ↦ s i (γ t)) :=
    hs.generating ht Submodule.mem_top
  have hz : frameVelocityCoordinates s γ t ≠ 0 :=
    (frameVelocityCoordinates_eq_zero_iff hsp).not.mpr hv
  -- The connection term of `z' / z` is `-i ω(γ')`, which cancels against `ω(γ')`.
  rw [(hs.hasDerivAt_frameVelocityCoordinates hu ho
      (isMetricCompatible_leviCivitaConnection (I := I) (M := M)) ht hγ hγv).deriv]
  simp only [sub_div, mul_div_cancel_right₀ _ hz, Complex.sub_im, Complex.I_mul_im,
    Complex.ofReal_re, sub_add_cancel]
  -- What remains is the normal component of the acceleration, read in the frame.
  rw [geodesicCurvature_def,
    orientedUnitNormal_eq_frameVelocityCoordinates o ((ho _ ht).norm_eq_one 0) hor,
    inner_add_right, real_inner_smul_right, real_inner_smul_right, acceleration_def,
    Complex.div_im, Complex.normSq_eq_norm_sq, norm_frameVelocityCoordinates (ho _ ht) hsp]
  simp [real_inner_comm]
  field_simp
  ring

end IsLocalFrameOn

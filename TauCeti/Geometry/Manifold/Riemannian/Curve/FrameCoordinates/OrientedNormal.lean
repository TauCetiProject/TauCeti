/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Curve.FrameCoordinates.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Curve.OrientedNormal

/-!
# The oriented unit normal in an orthonormal frame

Let `o` orient a Riemannian surface, let `J` be the right-angle rotation of the tangent plane at
`γ t`, and let `s = (s₀, s₁)` satisfy `‖s₀‖ = 1` and `s₁ = J s₀` there. If `z` is the frame
coordinate of the velocity, the oriented unit normal `J γ' / ‖γ'‖` has coordinates
`(-Im z, Re z) / ‖γ'‖` (`TauCeti.Manifold.orientedUnitNormal_eq_frameVelocityCoordinates`).
Only the pair at the evaluation point is used: neither a local frame nor any regularity is needed.
At a stationary point both sides are zero, with the totalized division `x / 0 = 0`.

For a pair of unit vectors, the compatibility `s₁ = J s₀` is the normalization `vol(s₀, s₁) = 1`
(`TauCeti.Manifold.Orientation.eq_rightAngleRotation_iff_riemannianVolumeForm_eq_one`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 9.
-/

public section

open Bundle
open scoped Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  {s : Fin 2 → Π x : M, TangentSpace I x} {γ : ℝ → M} {t : ℝ}

/-- For a pair `(s₀, s₁)` at `γ t` with `‖s₀‖ = 1` and `s₁ = J s₀`, the oriented unit normal has
frame coordinates `(-Im z, Re z) / ‖γ'‖`. Only the pair at the evaluation point is used. At a
stationary point both sides are zero, with the totalized division `x / 0 = 0`. -/
theorem orientedUnitNormal_eq_frameVelocityCoordinates
    (o : Orientation I M (Fin 2))
    (hunit : ‖s 0 (γ t)‖ = 1)
    (hor : s 1 (γ t) = (letI := o.fact_finrank_tangentSpace (γ t);
      (o.orientationAt (γ t)).rightAngleRotation (s 0 (γ t)))) :
    orientedUnitNormal o γ t =
      (-(frameVelocityCoordinates s γ t).im / ‖curveVelocity I γ t‖) • s 0 (γ t) +
        ((frameVelocityCoordinates s γ t).re / ‖curveVelocity I γ t‖) • s 1 (γ t) := by
  let := o.fact_finrank_tangentSpace (γ t)
  have ho : Orthonormal ℝ (fun i ↦ s i (γ t)) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hor, hunit]
  have hvel := curveVelocity_eq_frameVelocityCoordinates ho
    ((ho.linearIndependent.span_eq_top_of_card_eq_finrank (by simpa using this.out.symm)).ge
      Submodule.mem_top)
  have hJ : (o.orientationAt (γ t)).rightAngleRotation (s 1 (γ t)) = -s 0 (γ t) := by
    rw [hor, (o.orientationAt (γ t)).rightAngleRotation_rightAngleRotation]
  have hJv : (o.orientationAt (γ t)).rightAngleRotation (curveVelocity I γ t) =
      -(frameVelocityCoordinates s γ t).im • s 0 (γ t) +
        (frameVelocityCoordinates s γ t).re • s 1 (γ t) := by
    rw [hvel]
    simp only [map_add, map_smul, ← hor, hJ, smul_neg, neg_smul]
    abel
  rw [orientedUnitNormal_apply, NormedSpace.normalize, map_smul, hJv]
  module

end TauCeti.Manifold

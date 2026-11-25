/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.ClosedBall.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.OutwardUnitNormal
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Outward

/-!
# The outward unit normal of the closed unit ball

For the Euclidean metric on the closed unit ball of a real inner product space `E` of dimension
`n + 1` (`TauCeti.closedBallEuclideanMetric`), the outward unit normal at a point `x` of the
boundary sphere is the radial vector `x` itself, read as a tangent vector through the differential
of the inclusion (`TauCeti.outwardUnitNormal_closedBall`). Consequently the inner product of a
tangent vector `v` with the inward unit normal `ν_in = -ν_out` is `-⟨v, x⟩`, computed in `E`
(`TauCeti.inner_neg_outwardUnitNormal_closedBall`).

The radial vector has norm one, points outward (`TauCeti.isOutwardPointing_closedBall_radial`) and
is orthogonal to the tangent vectors of the boundary, because the squared norm is constant on the
boundary sphere (`TauCeti.inner_mvfderiv_subtypeVal_closedBall_boundary`); the three laws
characterize the outward unit normal (`TauCeti.eq_outwardUnitNormal_iff`).
-/

public section

open Bundle Metric Module Set
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n + 1)]

/-- At a point `x` of the boundary sphere of the closed unit ball, the tangent vectors of the
boundary, read in `E`, are orthogonal to the radius vector `x`. -/
theorem inner_mvfderiv_subtypeVal_closedBall_boundary
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1))
    (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    ⟪((q : closedBall (0 : E) 1) : E),
      mvfderiv (𝓡∂ (n + 1)) (Subtype.val : closedBall (0 : E) 1 → E) q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1) →
            closedBall (0 : E) 1) q w)⟫ = 0 := by
  set B := closedBall (0 : E) 1
  set j : (𝓡∂ (n + 1)).boundary B → E := fun y ↦ ((y : B) : E)
  have hB : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : B → E) q :=
    (contMDiff_subtypeVal_closedBall (n := n + 1) (k := 1)).mdifferentiableAt one_ne_zero
  have hι : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary B → B) q :=
    (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := 1) B).contMDiff.mdifferentiableAt
      one_ne_zero
  have hj := hB.hasMFDerivAt.comp q hι.hasMFDerivAt
  have hsq := (hasStrictFDerivAt_norm_sq (j q)).hasFDerivAt.hasMFDerivAt.comp q hj
  have hconst : (fun y : E ↦ ‖y‖ ^ 2) ∘ j = fun _ ↦ (1 : ℝ) := by
    funext y
    simp [j, (isBoundaryPoint_closedBall_iff (n := n + 1)).mp y.property]
  rw [hconst] at hsq
  have hL := hsq.mfderiv
  rw [mfderiv_const] at hL
  have h := congrArg (fun L : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q →L[ℝ] ℝ ↦ L w) hL
  have h' : (2 : ℕ) • ⟪((q : B) : E), mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : B → E) q
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary B → B) q w)⟫ = 0 := h.symm
  rw [mvfderiv_apply_eq_mfderiv_apply]
  simpa using h'

/-- The **outward unit normal of the closed unit ball** at a point `x` of its boundary sphere is
the radial vector `x`: the differential of the inclusion maps it to `x`. -/
theorem mvfderiv_outwardUnitNormal_closedBall
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    mvfderiv (𝓡∂ (n + 1)) (Subtype.val : closedBall (0 : E) 1 → E) q (outwardUnitNormal q) =
      ((q : closedBall (0 : E) 1) : E) := by
  set x : closedBall (0 : E) 1 := (q : closedBall (0 : E) 1)
  set v : TangentSpace (𝓡∂ (n + 1)) x :=
    (subtypeValClosedBallTangentEquiv (n := n + 1) x).symm (x : E)
  have hd : mvfderiv (𝓡∂ (n + 1)) (Subtype.val : closedBall (0 : E) 1 → E) x v = x := by
    rw [mvfderiv_subtypeVal_closedBall]
    exact (subtypeValClosedBallTangentEquiv (n := n + 1) x).apply_symm_apply _
  have hx : ‖(x : E)‖ = 1 := (isBoundaryPoint_closedBall_iff (n := n + 1)).mp q.property
  have hv : v = outwardUnitNormal q := by
    refine eq_outwardUnitNormal_iff.mpr ⟨?_, isOutwardPointing_closedBall_radial x q.property,
      fun w ↦ ?_⟩
    · rw [norm_tangentSpace_closedBall, hd, hx]
    · rw [inner_tangentSpace_closedBall, hd]
      exact inner_mvfderiv_subtypeVal_closedBall_boundary q w
  rw [← hv, hd]

/-- The outward unit normal of the closed unit ball at a point `x` of its boundary sphere is the
radial vector `x`, read as a tangent vector through the differential of the inclusion. -/
theorem outwardUnitNormal_closedBall (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    outwardUnitNormal q =
      (subtypeValClosedBallTangentEquiv (n := n + 1) (q : closedBall (0 : E) 1)).symm
        ((q : closedBall (0 : E) 1) : E) := by
  rw [← mvfderiv_outwardUnitNormal_closedBall q, mvfderiv_subtypeVal_closedBall]
  exact ((subtypeValClosedBallTangentEquiv (n := n + 1) _).symm_apply_apply _).symm

/-- On the boundary sphere of the closed unit ball, the inner product of a tangent vector `v` with
the inward unit normal `-ν_out(x)` is `-⟨v, x⟩`, computed in `E`. -/
theorem inner_neg_outwardUnitNormal_closedBall
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1))
    (v : TangentSpace (𝓡∂ (n + 1)) (q : closedBall (0 : E) 1)) :
    ⟪v, -outwardUnitNormal q⟫ =
      -⟪mvfderiv (𝓡∂ (n + 1)) (Subtype.val : closedBall (0 : E) 1 → E) q v,
        ((q : closedBall (0 : E) 1) : E)⟫ := by
  rw [inner_neg_right, inner_tangentSpace_closedBall, mvfderiv_outwardUnitNormal_closedBall]

end TauCeti

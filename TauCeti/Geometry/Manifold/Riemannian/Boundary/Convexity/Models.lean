/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Convexity.Basic
public import TauCeti.Geometry.Manifold.Riemannian.ClosedBall.SecondFundamentalForm
public import TauCeti.Geometry.Manifold.Riemannian.EuclideanHalfSpace
import TauCeti.Geometry.Manifold.Instances.ClosedBall.Boundary

/-!
# Convexity of the boundary of the closed unit ball and of the half-space

For the Euclidean metrics:

* the boundary of the closed unit ball of a real inner product space of dimension `n + 1` is
  strictly convex (`TauCeti.isStrictlyConvexBoundary_closedBall`), since its second fundamental
  form is the induced metric;
* the boundary of the closed half-space `{x⁰ ≥ 0}` is convex at every point
  (`TauCeti.isConvexAt_euclideanHalfSpace`), since its second fundamental form vanishes, and for
  `n ≥ 1` it is nowhere strictly convex (`TauCeti.not_isStrictlyConvexAt_euclideanHalfSpace`);
* since `II = h` on the ball, for `n ≥ 1` the best constant `c` in the uniform bound `II ≥ c h`
  is `1` (`TauCeti.forall_mul_boundaryInducedForm_le_boundarySecondFundamentalForm_closedBall_iff`),
  while for `n = 0` every `c` works, as on every manifold with boundary of dimension one;
* in dimension one the half-line `[0, ∞)` is strictly convex
  (`TauCeti.isStrictlyConvexBoundary_euclideanHalfSpace_one`), because the tangent space of its
  boundary is zero.
-/

public section

open Bundle Metric Module
open scoped Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

/-- **The closed unit ball has strictly convex boundary**: for the Euclidean metric,
`II_q(u, u) = |dι u|² > 0` for every nonzero `u ∈ T_q∂B`. -/
theorem isStrictlyConvexBoundary_closedBall {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)] :
    IsStrictlyConvexBoundary n (closedBall (0 : E) 1) :=
  isStrictlyConvexBoundary_iff.2 fun q ↦ isStrictlyConvexAt_iff.2 fun _ hu ↦
    boundarySecondFundamentalForm_closedBall_eq_boundaryInducedForm q ▸
      boundaryInducedForm_self_pos q hu

/-- **The best uniform convexity constant of the closed unit ball is `1`.** For `n ≥ 1`, the
bound `II_q(u, u) ≥ c h_q(u, u)` holds at every point `q` of the unit sphere bounding the closed
unit ball of a space of dimension `n + 1` and every `u ∈ T_q∂B` exactly when `c ≤ 1`, since
`II = h`. For `n = 0` the bound holds for every `c`
(`TauCeti.mul_boundaryInducedForm_le_boundarySecondFundamentalForm_of_eq_zero`). -/
theorem forall_mul_boundaryInducedForm_le_boundarySecondFundamentalForm_closedBall_iff {n : ℕ}
    [NeZero n] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (finrank ℝ E = n + 1)] {c : ℝ} :
    (∀ (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1))
        (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q),
        c * boundaryInducedForm q u u ≤ boundarySecondFundamentalForm q u u) ↔ c ≤ 1 := by
  simp only [boundarySecondFundamentalForm_closedBall_eq_boundaryInducedForm]
  refine ⟨fun h ↦ ?_, fun hc q u ↦ ?_⟩
  · obtain ⟨q⟩ : Nonempty ((𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) := inferInstance
    obtain ⟨u, hu⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
    exact le_of_mul_le_mul_right ((h q u).trans_eq (one_mul _).symm)
      (boundaryInducedForm_self_pos q (u := u) hu)
  · exact (mul_le_mul_of_nonneg_right hc (boundaryInducedForm_self_nonneg q u)).trans_eq
      (one_mul _)

/-- **The half-space has convex boundary**: for the Euclidean metric on `{x⁰ ≥ 0}`, the second
fundamental form of the boundary hyperplane vanishes, so the boundary is convex at every point. -/
theorem isConvexAt_euclideanHalfSpace {n : ℕ}
    (q : (𝓡∂ (n + 1)).boundary (EuclideanHalfSpace (n + 1))) :
    IsConvexAt q :=
  isConvexAt_iff.2 fun u ↦ (boundarySecondFundamentalForm_euclideanHalfSpace q u u).ge

/-- **The half-space is nowhere strictly convex** in dimension at least two: for `n ≥ 1` the
boundary hyperplane has a nonzero tangent vector, on which the second fundamental form
vanishes. -/
theorem not_isStrictlyConvexAt_euclideanHalfSpace {n : ℕ} [NeZero n]
    (q : (𝓡∂ (n + 1)).boundary (EuclideanHalfSpace (n + 1))) :
    ¬ IsStrictlyConvexAt q := fun h ↦ by
  have hu : (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin n)) ≠ 0 := by simp
  exact (isStrictlyConvexAt_iff.1 h _ hu).ne'
    (boundarySecondFundamentalForm_euclideanHalfSpace q _ _)

/-- **The half-line is strictly convex**: in dimension one the tangent space of the boundary is
zero, so the condition is vacuous. -/
theorem isStrictlyConvexBoundary_euclideanHalfSpace_one :
    IsStrictlyConvexBoundary 0 (EuclideanHalfSpace 1) :=
  isStrictlyConvexBoundary_iff.2 (isStrictlyConvexAt_of_eq_zero rfl)

end TauCeti

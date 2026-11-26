/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.ClosedBall.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Isometry
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Calculus

/-!
# The Hessian on the closed unit ball

The inclusion of the closed unit ball of a real inner product space `E` of dimension `n`, with its
Euclidean metric `TauCeti.closedBallEuclideanMetric`, into `E` with its flat metric is a local
Riemannian isometry (`TauCeti.isLocalRiemannianIsometry_subtypeVal_closedBall`): it is analytic, its
differential is invertible at every point, including the points of the boundary sphere, and the
metric of the ball is induced by it. The naturality of the Levi-Civita connection under local
Riemannian isometries holds at boundary points as well, so the Hessian of the restriction
`f ∘ ι` of a function `f : E → ℝ`, `C²` at `x`, is the second Fréchet derivative of `f` at every
point of the closed ball, boundary included:

`Hess (f ∘ ι)(u, w) = D²f(x)(dι u, dι w)`.

In particular `Hess (1 - |x|²) = -2 g` (`TauCeti.hessian_one_sub_norm_sq_closedBall`).

## Main statements

* `TauCeti.hessian_comp_subtypeVal_closedBall`: the Hessian of `f ∘ ι` on the closed unit ball is
  the second Fréchet derivative of `f`.
* `TauCeti.hessian_one_sub_norm_sq_closedBall`: the Hessian of `1 - |x|²` is `-2` times the
  Euclidean metric.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (induced metrics on submanifolds).
-/

public section

open Bundle Metric Module TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace Gradient

noncomputable section

namespace TauCeti

variable {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n)]

/-- **The Hessian on the closed unit ball.** For a function `f : E → ℝ`, `C²` at a point `x` of
the closed unit ball, the Hessian of its restriction `f ∘ ι` for the Euclidean metric is the second
Fréchet derivative of `f` at `x`, evaluated on the images of the tangent vectors under the
differential of the inclusion. This holds at the points of the boundary sphere as well. -/
theorem hessian_comp_subtypeVal_closedBall {f : E → ℝ} {x : closedBall (0 : E) 1}
    (hf : ContDiffAt ℝ 2 f x) (u w : TangentSpace (𝓡∂ n) x) :
    hessian (𝓡∂ n) (f ∘ Subtype.val) x u w =
      fderiv ℝ (fderiv ℝ f) x
        (mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x u)
        (mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x w) := by
  have : FiniteDimensional ℝ E :=
    Module.finite_of_finrank_pos (by rw [Fact.out (p := finrank ℝ E = n)]; exact NeZero.pos n)
  have hgrad : DifferentiableAt ℝ (∇ f) x :=
    (hf.gradient_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [isLocalRiemannianIsometry_subtypeVal_closedBall.hessian_comp
    (contMDiffAt_iff_contDiffAt.2 hf), hessian_eq_iteratedFDeriv_model_space hgrad,
    iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val, NormedSpace.fromTangentSpace_apply,
    mvfderiv_apply_eq_mfderiv_apply]

/-- On the closed unit ball, the Hessian of `1 - |x|²` is `-2` times the Euclidean metric, at
every point including the points of the boundary sphere. -/
theorem hessian_one_sub_norm_sq_closedBall (x : closedBall (0 : E) 1)
    (u w : TangentSpace (𝓡∂ n) x) :
    hessian (𝓡∂ n) (fun y : closedBall (0 : E) 1 ↦ 1 - ‖(y : E)‖ ^ 2) x u w = -2 * ⟪u, w⟫ := by
  have hf : fderiv ℝ (fun y : E ↦ 1 - ‖y‖ ^ 2) = -fderiv ℝ (fun z : E ↦ ‖z‖ ^ 2) :=
    funext fun _ ↦ fderiv_const_sub 1
  have h := hessian_comp_subtypeVal_closedBall (f := fun y : E ↦ 1 - ‖y‖ ^ 2)
    ((contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffAt (x := (x : E))) u w
  rw [Function.comp_def] at h
  rw [h, hf, fderiv_neg, neg_apply, neg_apply, fderiv_fderiv_norm_sq_apply,
    inner_tangentSpace_closedBall, neg_mul]

end TauCeti

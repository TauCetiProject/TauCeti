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
import TauCeti.Analysis.Calculus.SecondDerivative

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

In particular `Hess (1 - |x|²) = -2 g` (`TauCeti.hessian_one_sub_norm_sq_closedBall`), and for the
second boundary defining function `ρ' = (2 + ⟪a, x⟫)(1 - |x|²)`, `Hess ρ' = (2 + ⟪a, x⟫) Hess ρ` on
vectors `u` with `dι u` orthogonal to `x`; at a boundary point these are exactly the vectors tangent
to the boundary sphere. For `‖a‖ ≤ 1` both Hessians are negative on every nonzero such vector, so
the two defining functions `ρ` and `ρ'` give the same sign there.

## Main statements

* `TauCeti.hessian_comp_subtypeVal_closedBall`: the Hessian of `f ∘ ι` on the closed unit ball is
  the second Fréchet derivative of `f`.
* `TauCeti.hessian_one_sub_norm_sq_closedBall`: the Hessian of `1 - |x|²` is `-2` times the
  Euclidean metric, so it is negative on every nonzero vector
  (`TauCeti.hessian_one_sub_norm_sq_closedBall_apply_self_neg`).
* `TauCeti.hessian_two_add_inner_mul_one_sub_norm_sq_closedBall`: the Hessian of
  `(2 + ⟪a, x⟫)(1 - |x|²)`, with its restriction to vectors orthogonal to `x`
  (`TauCeti.hessian_two_add_inner_mul_one_sub_norm_sq_closedBall_of_inner_eq_zero`) and its sign
  there for `‖a‖ ≤ 1`
  (`TauCeti.hessian_two_add_inner_mul_one_sub_norm_sq_closedBall_apply_self_neg`).

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
  have h := hessian_comp_subtypeVal_closedBall (f := fun y : E ↦ 1 - ‖y‖ ^ 2)
    ((contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffAt (x := (x : E))) u w
  rw [Function.comp_def] at h
  rw [h, fderiv_fderiv_one_sub_norm_sq_apply, inner_tangentSpace_closedBall, neg_mul]

/-- On the closed unit ball, the Hessian of `1 - |x|²` is negative on every nonzero tangent
vector, at every point including the points of the boundary sphere. -/
theorem hessian_one_sub_norm_sq_closedBall_apply_self_neg (x : closedBall (0 : E) 1)
    {u : TangentSpace (𝓡∂ n) x} (hu0 : u ≠ 0) :
    hessian (𝓡∂ n) (fun y : closedBall (0 : E) 1 ↦ 1 - ‖(y : E)‖ ^ 2) x u u < 0 := by
  rw [hessian_one_sub_norm_sq_closedBall, real_inner_self_eq_norm_sq]
  have := norm_pos_iff.2 hu0
  nlinarith

/-- On the closed unit ball, the Hessian of `(2 + ⟪a, x⟫)(1 - |x|²)` at `x` is
`-2 (2 + ⟪a, x⟫) g(u, w) - 2 (⟪a, dι u⟫ ⟪x, dι w⟫ + ⟪a, dι w⟫ ⟪x, dι u⟫)`, at every point including
the points of the boundary sphere. -/
theorem hessian_two_add_inner_mul_one_sub_norm_sq_closedBall (a : E)
    (x : closedBall (0 : E) 1) (u w : TangentSpace (𝓡∂ n) x) :
    hessian (𝓡∂ n) (fun y : closedBall (0 : E) 1 ↦ (2 + ⟪a, (y : E)⟫) * (1 - ‖(y : E)‖ ^ 2)) x u w =
      -2 * (2 + ⟪a, (x : E)⟫) * ⟪u, w⟫ -
        2 * (⟪a, mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x u⟫ *
            ⟪(x : E), mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x w⟫ +
          ⟪a, mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x w⟫ *
            ⟪(x : E), mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x u⟫) := by
  have hl : ContDiff ℝ 2 (fun y : E ↦ 2 + ⟪a, y⟫) :=
    contDiff_const.add (contDiff_const.inner ℝ contDiff_id)
  have hq : ContDiff ℝ 2 (fun y : E ↦ 1 - ‖y‖ ^ 2) := contDiff_const.sub (contDiff_norm_sq ℝ)
  have h := hessian_comp_subtypeVal_closedBall (f := fun y : E ↦ (2 + ⟪a, y⟫) * (1 - ‖y‖ ^ 2))
    ((hl.mul hq).contDiffAt (x := (x : E))) u w
  rw [Function.comp_def] at h
  rw [h, fderiv_fderiv_fun_mul_apply hl.contDiffAt hq.contDiffAt, inner_tangentSpace_closedBall]
  set v₁ := mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x u
  set v₂ := mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x w
  -- The derivatives of the two factors.
  have hdl : fderiv ℝ (fun y : E ↦ 2 + ⟪a, y⟫) = fun _ ↦ innerSL ℝ a := by
    funext y
    rw [fderiv_const_add]
    exact (innerSL ℝ a).fderiv
  have hdq (y : E) : fderiv ℝ (fun y : E ↦ 1 - ‖y‖ ^ 2) y = -(2 • innerSL ℝ y) := by
    rw [fderiv_const_sub, fderiv_norm_sq_apply]
  rw [hdl, fderiv_fun_const, fderiv_fderiv_one_sub_norm_sq_apply, hdq]
  simp only [Pi.zero_apply, zero_apply, innerSL_apply_apply, neg_apply, smul_apply,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- On vectors `u`, `w` with `dι u`, `dι w` orthogonal to `x` (`⟪x, dι u⟫ = ⟪x, dι w⟫ = 0`; at a
boundary point these are exactly the vectors tangent to the boundary sphere), the Hessian of the
defining function `ρ' = (2 + ⟪a, x⟫) ρ`, `ρ = 1 - |x|²`, is
`(2 + ⟪a, x⟫) Hess ρ(u, w) = -2 (2 + ⟪a, x⟫) g(u, w)`. -/
theorem hessian_two_add_inner_mul_one_sub_norm_sq_closedBall_of_inner_eq_zero (a : E)
    (x : closedBall (0 : E) 1) {u w : TangentSpace (𝓡∂ n) x}
    (hu : ⟪(x : E), mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x u⟫ = 0)
    (hw : ⟪(x : E), mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x w⟫ = 0) :
    hessian (𝓡∂ n) (fun y : closedBall (0 : E) 1 ↦ (2 + ⟪a, (y : E)⟫) * (1 - ‖(y : E)‖ ^ 2)) x u w =
      (2 + ⟪a, (x : E)⟫) *
        hessian (𝓡∂ n) (fun y : closedBall (0 : E) 1 ↦ 1 - ‖(y : E)‖ ^ 2) x u w := by
  rw [hessian_two_add_inner_mul_one_sub_norm_sq_closedBall, hessian_one_sub_norm_sq_closedBall,
    hu, hw]
  ring

/-- For `‖a‖ ≤ 1`, the Hessian of the defining function `ρ' = (2 + ⟪a, x⟫)(1 - |x|²)` of the closed
unit ball is negative on every nonzero vector `u` with `dι u` orthogonal to `x`; at a boundary point
these are exactly the nonzero vectors tangent to the boundary sphere. Together with
`TauCeti.hessian_one_sub_norm_sq_closedBall_apply_self_neg`, the Hessians of `ρ'` and of
`ρ = 1 - |x|²` have the same (negative) sign on these vectors. -/
theorem hessian_two_add_inner_mul_one_sub_norm_sq_closedBall_apply_self_neg {a : E}
    (ha : ‖a‖ ≤ 1) (x : closedBall (0 : E) 1) {u : TangentSpace (𝓡∂ n) x} (hu0 : u ≠ 0)
    (hu : ⟪(x : E), mvfderiv (𝓡∂ n) (Subtype.val : closedBall (0 : E) 1 → E) x u⟫ = 0) :
    hessian (𝓡∂ n)
      (fun y : closedBall (0 : E) 1 ↦ (2 + ⟪a, (y : E)⟫) * (1 - ‖(y : E)‖ ^ 2)) x u u < 0 := by
  rw [hessian_two_add_inner_mul_one_sub_norm_sq_closedBall_of_inner_eq_zero a x hu hu]
  have hx : ‖(x : E)‖ ≤ 1 := mem_closedBall_zero_iff.1 x.property
  have h₁ := abs_real_inner_le_norm a (x : E)
  have h₂ : ‖a‖ * ‖(x : E)‖ ≤ 1 := by nlinarith [norm_nonneg a, norm_nonneg (x : E)]
  have h₃ := neg_abs_le ⟪a, (x : E)⟫
  exact mul_neg_of_pos_of_neg (by linarith)
    (hessian_one_sub_norm_sq_closedBall_apply_self_neg x hu0)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Hessian.Piola

/-!
# Divergence-form linearization of the Monge–Ampère determinant

The determinant first variation in the Hessian direction of a scalar perturbation is the
scalar divergence of the cofactor flux. This identifies the divergence and determinant forms of
the linearized Monge–Ampère operator, including at singular Hessians. Only `C³` regularity of the
potential and `C²` regularity of the perturbation near the point are required.

The Hessian Piola identity and its trace contraction are in
`TauCeti.Analysis.Calculus.FDeriv.Hessian.Piola`.
-/

public section

open TauCeti
open scoped Gradient Matrix.Norms.Operator ContDiff

namespace OrthonormalBasis

/-- The determinant first variation in a Hessian direction equals the scalar divergence of
the cofactor Hessian flux of that perturbation. -/
theorem hasDerivAt_det_hessianOperator_add_smul
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : OrthonormalBasis ι ℝ E) {u v : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (hv : ContDiffAt ℝ 2 v x) :
    HasDerivAt (fun t : ℝ ↦
      (LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator u x).toLinearMap +
        t • LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator v x).toLinearMap).det)
      (LinearMap.trace ℝ E (fderiv ℝ (fun y ↦
        Matrix.toLin b.toBasis b.toBasis
          (LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator u y).toLinearMap).adjugate
          (∇ v y)) x).toLinearMap) 0 := by
  rw [b.trace_fderiv_adjugate_hessianOperator_gradient hu hv]
  let A := LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator u x).toLinearMap
  let B := LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator v x).toLinearMap
  have h := (Matrix.differentiable_det A).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A) (by simp)
  rw [one_smul] at h
  convert h using 1
  · funext t
    simp only [A, B, Function.comp_apply, id_eq]
  · exact (Matrix.fderiv_det_apply_adjugate A B).symm

end OrthonormalBasis

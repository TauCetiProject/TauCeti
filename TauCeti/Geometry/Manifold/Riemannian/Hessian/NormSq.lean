/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.CriticalHessian
import TauCeti.Geometry.Manifold.MFDeriv.Inner
import TauCeti.Analysis.InnerProductSpace.SquaredDistance
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Calculus

/-!
# Hessians of squared norms

At an interior zero of a twice differentiable map from a finite-dimensional Riemannian manifold
into a real inner product space, the Hessian of its squared norm is twice the pullback inner
product.
This identifies the Hessian of squared Riemannian distance at the centre of a normal chart and
requires only a continuously differentiable metric on the source manifold.

On a finite-dimensional real inner product space with its flat metric, the Hessian of the squared
norm is twice the inner product at every point (`TauCeti.Manifold.hessian_norm_sq_model_space`).
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace Gradient

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {p : M}

variable [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- At an interior zero of a smooth vector-valued map on a finite-dimensional Riemannian manifold,
the Hessian of its squared norm is twice the pullback of the target inner product by its
differential. -/
theorem hessian_norm_sq_comp_of_eq_zero
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : M → F} (hf : ContMDiffAt I 𝓘(ℝ, F) 2 f p) (hp : I.IsInteriorPoint p) (hzero : f p = 0)
    (v w : TangentSpace I p) :
    hessian I (fun q ↦ ‖f q‖ ^ 2) p v w =
      2 * inner ℝ (mvfderiv I f p v) (mvfderiv I f p w) := by
  have hcrit := mvfderiv_norm_sq_comp_eq_zero_of_eq_zero (hf.mdifferentiableAt (by norm_num)) hzero
  have hs : ContMDiffAt I 𝓘(ℝ) 2 (fun q ↦ ‖f q‖ ^ 2) p :=
    (contDiff_norm_sq ℝ).contDiffAt.contMDiffAt.comp p hf
  rw [hessian_eq_criticalHessian hs hp hcrit]
  have hchart := hf.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hp
  have h := fderiv_fderiv_norm_sq_sub_comp_apply (a := (0 : F)) hchart v w
  simp only [sub_zero, Function.comp_apply, extChartAt_to_inv, hzero, inner_zero_left,
    add_zero] at h
  rw [criticalHessian_def, (hf.mdifferentiableAt (by norm_num)).mvfderiv,
    fderivWithin_of_mem_nhds (range_mem_nhds_isInteriorPoint hp)]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp]
  exact h

/-- On a finite-dimensional real inner product space with its flat metric, the Hessian of the
squared norm is twice the inner product: `Hess ‖·‖² = 2g`. -/
theorem hessian_norm_sq_model_space {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (x : F) (v w : TangentSpace 𝓘(ℝ, F) x) :
    hessian 𝓘(ℝ, F) (fun y : F ↦ ‖y‖ ^ 2) x v w = 2 * ⟪(v : F), (w : F)⟫ := by
  have hgrad : DifferentiableAt ℝ (∇ fun y : F ↦ ‖y‖ ^ 2) x :=
    ((contDiff_norm_sq ℝ (n := 2)).gradient_right (m := 1) (by norm_num)).differentiable
      one_ne_zero x
  rw [hessian_eq_iteratedFDeriv_model_space hgrad, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val, NormedSpace.fromTangentSpace_apply]
  exact fderiv_fderiv_norm_sq_apply x v w

end TauCeti.Manifold

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.CriticalHessian
import TauCeti.Geometry.Manifold.MFDeriv.Inner
import TauCeti.Analysis.InnerProductSpace.SquaredDistance

/-!
# Hessians of squared norms at zeros

At a zero of a twice differentiable map into a real inner product space, the Hessian of its
squared norm is twice the pullback inner product.
This identifies the Hessian of squared Riemannian distance at the centre of a normal chart and
requires only a continuously differentiable metric on the source manifold.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {p : M}

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- At a zero of a smooth vector-valued map, the Hessian of its squared norm is twice
the pullback of the target inner product by its differential. -/
theorem hessian_norm_sq_comp_of_eq_zero
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : M → F} (hf : ContMDiffAt I 𝓘(ℝ, F) 2 f p) (hzero : f p = 0)
    (v w : TangentSpace I p) :
    hessian I (fun q ↦ ‖f q‖ ^ 2) p v w =
      2 * inner ℝ (mvfderiv I f p v) (mvfderiv I f p w) := by
  have hcrit := mvfderiv_norm_sq_comp_eq_zero_of_eq_zero (hf.mdifferentiableAt (by norm_num)) hzero
  have hs : ContMDiffAt I 𝓘(ℝ) 2 (fun q ↦ ‖f q‖ ^ 2) p :=
    (contDiff_norm_sq ℝ).contDiffAt.contMDiffAt.comp p hf
  rw [hessian_eq_criticalHessian hs hcrit]
  have hchart := contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.1 hf
  have h := fderiv_fderiv_norm_sq_sub_comp_apply (a := (0 : F)) hchart v w
  simp only [sub_zero, Function.comp_apply, extChartAt_to_inv, hzero, inner_zero_left,
    add_zero] at h
  rw [criticalHessian_def, TauCeti.mvfderiv_eq_fderiv_comp_extChartAt_symm]
  exact h

end TauCeti.Manifold

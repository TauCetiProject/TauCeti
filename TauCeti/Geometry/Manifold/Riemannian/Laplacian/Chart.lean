/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram

/-!
# The Laplacian in a chart frame

The native scalar Laplacian is the contraction of Hessian coefficients with the inverse chart
Gram matrix. This formula does not require orthonormalizing the chart frame.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, Chapter 3.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section
open Bundle CovariantDerivative
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

open Riemannian.Tensor in
/-- The scalar Laplacian contracts the Hessian with the inverse Gram matrix. -/
theorem laplaceBeltrami_eq_sum_chartInvGramMatrix_hessian
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (α : M) {x : M} (hx : x ∈ (chartAt H α).source) (f : M → ℝ) :
    laplaceBeltrami I f x = ∑ i, ∑ j, chartInvGramMatrix (I := I) α x i j *
      hessian I f x (chartLocalFrame (I := I) α i x) (chartLocalFrame (I := I) α j x) := by
  rw [I.laplaceBeltrami_eq_metricTrace_hessianForm, metricTrace_eq_sum_chartInvGramMatrix α hx]
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, I.hessianForm_apply,
    smul_eq_mul]

end TauCeti.Manifold

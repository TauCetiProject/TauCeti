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
  let A := leviCivitaConnection I M (mgradient I f) x
  let B : LinearMap.BilinForm ℝ (TangentSpace I x) := ((innerSL ℝ).comp A).toLinearMap₁₂
  have hB (v w : TangentSpace I x) : B v w = hessian I f x v w := by
    rw [hessian_def]
    rfl
  have ht : TauCeti.bilinFormTrace B = laplaceBeltrami I f x := by
    rw [TauCeti.bilinFormTrace_eq_sum B (stdOrthonormalBasis ℝ (TangentSpace I x)),
      laplaceBeltrami_eq_sum_hessian I f x (stdOrthonormalBasis ℝ (TangentSpace I x))]
    simp only [hB]
  rw [← ht, bilinFormTrace_eq_sum_chartInvGramMatrix α hx B]
  simp only [hB]

end TauCeti.Manifold

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ExteriorSquare
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace

/-!
# Scalar curvature and the trace of the curvature operator

The curvature operator on bivectors uses the convention
`⟪Rop(u ∧ v), w ∧ z⟫ = ⟪R(u,v)z,w⟫`. Its trace is half the scalar curvature: the
Ricci/scalar contraction sums over all ordered pairs of tangent basis vectors, whereas the
orthonormal basis of the exterior square uses increasing pairs. Thus scalar curvature is twice
the sum of the curvature operator's eigenvalues, counted with multiplicity.

The trace identity needs metric compatibility but no torsion condition. The eigenvalue formula
uses vanishing torsion to obtain self-adjointness. Both identities include dimensions zero and
one, where the exterior square and scalar curvature vanish.

The construction reuses `CovariantDerivative.curvatureEndomorphism`, the existing Ricci/scalar
trace, and the ordered-wedge trace formula `OrthonormalBasis.sum_inner_ιMulti_two_eq_two_mul_trace`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 8
  (curvature operators and contractions of the Riemann curvature tensor).
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]
  (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov)

/-- Scalar curvature is twice the trace of the curvature endomorphism on bivectors.
Metric compatibility suffices; the connection may have torsion. -/
theorem scalarCurvature_eq_two_mul_trace_curvatureEndomorphism (x : M) :
    cov.scalarCurvature x =
      2 * LinearMap.trace ℝ (⋀[ℝ]^2 (TangentSpace I x))
        (cov.curvatureEndomorphism hcov x) := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [← b.sum_inner_ιMulti_two_eq_two_mul_trace,
    cov.scalarCurvature_eq_sum_inner_curvatureTensor x b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [cov.inner_curvatureEndomorphism_ιMulti]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, real_inner_comm]

/-- For a torsion-free metric connection, scalar curvature is twice the sum of the eigenvalues
of the self-adjoint curvature endomorphism, counted with their full multiplicities. -/
theorem scalarCurvature_eq_two_mul_sum_eigenvalues (ht : cov.torsion = 0) (x : M) :
    cov.scalarCurvature x = 2 * ∑ i,
      (cov.isSymmetric_curvatureEndomorphism hcov ht x).eigenvalues
        rfl i := by
  rw [cov.scalarCurvature_eq_two_mul_trace_curvatureEndomorphism hcov x,
    (cov.isSymmetric_curvatureEndomorphism hcov ht x).trace_eq_sum_eigenvalues rfl]
  simp

end CovariantDerivative

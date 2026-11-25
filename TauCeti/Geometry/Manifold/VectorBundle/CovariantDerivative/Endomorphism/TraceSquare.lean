/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Otis Chodosh
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Endomorphism.Hessian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian

/-!
# The Laplacian of an endomorphism's trace square

The scalar Laplacian of the trace is minus the trace of the rough Laplacian. For `tr(A²)`,
this gives the derivative-square trace and the pairing with the rough Laplacian. These identities
require no metric on the vector bundle and no metric compatibility of its connection. The metric
of the base determines the scalar Laplacian. Trace commutes with the rough Laplacian for
any tangent connection, without a regularity assumption on the base metric.

These identities build on an original local formalization by Otis Chodosh.
-/

public noncomputable section

open Bundle FiberBundle Filter Manifold
open scoped ContDiff Topology

namespace CovariantDerivative

open TauCeti.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {A B : Π x : M, V x →L[ℝ] V x}

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

/-- Fibrewise trace commutes with the rough Laplacian for any tangent connection.
No differentiability of the base metric is required. -/
theorem roughLaplacian_trace_endomorphism
    (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun z ↦ V z →L[ℝ] V z) y (A y)))
    (x : M) :
    (trivial (I := I) ℝ).roughLaplacian covT
        (fun y ↦ LinearMap.trace ℝ (V y) (A y).toLinearMap) x =
      LinearMap.trace ℝ (V x) (((cov.hom cov).roughLaplacian covT A x).toLinearMap) := by
  classical
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [roughLaplacian_eq_sum _ covT _ x b,
    (cov.hom cov).roughLaplacian_eq_sum covT A x b]
  simp only [cov.secondCovariantDerivative_trace_endomorphism covT hA x,
    ContinuousLinearMap.toLinearMap_neg, ContinuousLinearMap.toLinearMap_sum, map_neg, map_sum]

variable [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The scalar Laplacian commutes with fibrewise trace, with a minus sign for the
negative-trace convention of the rough Laplacian. -/
theorem laplaceBeltrami_trace_endomorphism
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun z ↦ V z →L[ℝ] V z) y (A y)))
    (x : M) :
    laplaceBeltrami I (fun y ↦ LinearMap.trace ℝ (V y) (A y).toLinearMap) x =
      -LinearMap.trace ℝ (V x)
        (((cov.hom cov).roughLaplacian (leviCivitaConnection I M) A x).toLinearMap) := by
  have h := cov.roughLaplacian_trace_endomorphism (leviCivitaConnection I M) hA x
  rw [roughLaplacian_trivial hA.trace_clm_bundle x] at h
  exact neg_eq_iff_eq_neg.mp h

/-- The scalar Laplacian of `tr(A²)` is twice the derivative-square trace minus twice the
trace pairing of `A` with its rough Laplacian. -/
theorem laplaceBeltrami_trace_comp_self
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun z ↦ V z →L[ℝ] V z) y (A y)))
    (x : M) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    laplaceBeltrami I
        (fun y ↦ LinearMap.trace ℝ (V y) ((A y).comp (A y)).toLinearMap) x =
      2 * (∑ i, LinearMap.trace ℝ (V x)
        ((cov.hom cov A x (b i)).comp (cov.hom cov A x (b i))).toLinearMap) -
      2 * LinearMap.trace ℝ (V x) ((A x).comp
        ((cov.hom cov).roughLaplacian (leviCivitaConnection I M) A x)).toLinearMap := by
  classical
  rw [laplaceBeltrami_eq_sum_hessian I _ x b,
    (cov.hom cov).roughLaplacian_eq_sum (leviCivitaConnection I M) A x b]
  simp_rw [cov.hessian_trace_comp_self hA x]
  simp only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_finsetSum,
    ContinuousLinearMap.toLinearMap_neg, ContinuousLinearMap.toLinearMap_sum,
    ContinuousLinearMap.toLinearMap_comp, map_neg, map_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end CovariantDerivative

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
of the base determines the scalar Laplacian and tangent connection.

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
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

/-- The scalar Laplacian commutes with fibrewise trace, with a minus sign for the
negative-trace convention of the rough Laplacian. -/
theorem laplaceBeltrami_trace_endomorphism
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun z ↦ V z →L[ℝ] V z) y (A y)))
    (x : M) :
    laplaceBeltrami I (fun y ↦ LinearMap.trace ℝ (V y) (A y).toLinearMap) x =
      -LinearMap.trace ℝ (V x)
        (((cov.hom cov).roughLaplacian (leviCivitaConnection I M) A x).toLinearMap) := by
  classical
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [laplaceBeltrami_eq_sum_hessian I _ x b,
    (cov.hom cov).roughLaplacian_eq_sum (leviCivitaConnection I M) A x b]
  simp only [cov.hessian_trace_endomorphism hA x, ContinuousLinearMap.toLinearMap_neg,
    ContinuousLinearMap.toLinearMap_sum, map_neg, map_sum, neg_neg]

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
  have : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  have hsum : (A x).toLinearMap.comp
      (∑ i, ((cov.hom cov).secondCovariantDerivative (leviCivitaConnection I M)
        A x (b i) (b i)).toLinearMap) =
      ∑ i, (A x).toLinearMap.comp
        (((cov.hom cov).secondCovariantDerivative (leviCivitaConnection I M)
          A x (b i) (b i)).toLinearMap) := by
    ext w
    simp
  rw [cov.laplaceBeltrami_trace_endomorphism (hA.clm_bundle_comp hA),
    (cov.hom cov).roughLaplacian_eq_sum (leviCivitaConnection I M) _ x b,
    (cov.hom cov).roughLaplacian_eq_sum (leviCivitaConnection I M) A x b]
  simp only [secondCovariantDerivative_comp cov cov cov (leviCivitaConnection I M) hA hA,
    ContinuousLinearMap.toLinearMap_neg, ContinuousLinearMap.toLinearMap_sum,
    ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.comp_neg, hsum, map_neg, map_sum, map_add, neg_neg]
  simp_rw [LinearMap.trace_comp_comm'
    (((cov.hom cov).secondCovariantDerivative (leviCivitaConnection I M)
      A x (b _) (b _)).toLinearMap) (A x).toLinearMap]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

end CovariantDerivative

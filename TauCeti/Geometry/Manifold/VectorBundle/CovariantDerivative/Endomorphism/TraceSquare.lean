/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Otis Chodosh
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Endomorphism
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The Hessian and Laplacian of an endomorphism's trace square

Covariant differentiation of a smooth endomorphism section commutes with its ordinary trace.
Combining this contraction rule with the product rule gives a pointwise formula for the
Laplacian of `tr(A²)`. These identities require no metric on the vector bundle and no metric
compatibility of its connection. The metric of the base determines the scalar Hessian,
Laplacian, and tangent connection used in the second covariant derivative.

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

/-- The scalar Hessian of the trace is the trace of the second covariant derivative. -/
theorem hessian_trace_endomorphism
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun z ↦ V z →L[ℝ] V z) y (A y)))
    (x : M) (u v : TangentSpace I x) :
    hessian I (fun y ↦ LinearMap.trace ℝ (V y) (A y).toLinearMap) x u v =
      LinearMap.trace ℝ (V x)
        (((cov.hom cov).secondCovariantDerivative (leviCivitaConnection I M)
          A x u v).toLinearMap) := by
  obtain ⟨Y, hY, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ v
  have hD := (cov.hom cov).contMDiff_apply hY hA
  have heq : (fun y ↦ mvfderiv I
      (fun z ↦ LinearMap.trace ℝ (V z) (A z).toLinearMap) y (Y y)) =
      fun y ↦ LinearMap.trace ℝ (V y) (cov.hom cov A y (Y y)).toLinearMap :=
    funext fun y ↦ cov.mvfderiv_trace_eq_trace_hom (hA.mdifferentiable (by simp) y) (Y y)
  have hh := hessian_apply_eq_mvfderiv_sub x ((hA.trace_clm_bundle x).of_le (by simp))
    (FiberBundle.extend E u) Y (hY.mdifferentiable (by simp) x)
  rw [FiberBundle.extend_apply_self, heq,
    cov.mvfderiv_trace_eq_trace_hom (hD.mdifferentiable (by simp) x),
    cov.mvfderiv_trace_eq_trace_hom (hA.mdifferentiable (by simp) x)] at hh
  rw [secondCovariantDerivative_apply (cov.hom cov) (leviCivitaConnection I M) hA x hY]
  simpa only [ContinuousLinearMap.toLinearMap_sub, map_sub] using hh

/-- The Hessian of a trace square is the sum of the derivative pairing and second-derivative
pairing. This is an ordinary trace identity, with no inner product on endomorphisms. -/
theorem hessian_trace_comp_self
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun z ↦ V z →L[ℝ] V z) y (A y)))
    (x : M) (u v : TangentSpace I x) :
    hessian I (fun y ↦ LinearMap.trace ℝ (V y) ((A y).comp (A y)).toLinearMap) x u v =
      2 * LinearMap.trace ℝ (V x)
        ((cov.hom cov A x u).comp (cov.hom cov A x v)).toLinearMap +
      2 * LinearMap.trace ℝ (V x) ((A x).comp
        ((cov.hom cov).secondCovariantDerivative (leviCivitaConnection I M)
          A x u v)).toLinearMap := by
  obtain ⟨Y, hY, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ v
  have hD := (cov.hom cov).contMDiff_apply hY hA
  have heq : (fun y ↦ mvfderiv I
      (fun z ↦ LinearMap.trace ℝ (V z) ((A z).comp (A z)).toLinearMap) y (Y y)) =
      (2 : ℝ) • (fun y ↦ LinearMap.trace ℝ (V y)
        ((A y).comp (cov.hom cov A y (Y y))).toLinearMap) := by
    funext y
    exact cov.mvfderiv_trace_comp_self (hA.mdifferentiable (by simp) y) (Y y)
  have hp : mvfderiv I (fun y ↦ LinearMap.trace ℝ (V y)
      ((A y).comp (cov.hom cov A y (Y y))).toLinearMap) x u =
      LinearMap.trace ℝ (V x)
        ((cov.hom cov A x u).comp (cov.hom cov A x (Y x))).toLinearMap +
      LinearMap.trace ℝ (V x)
        ((A x).comp (cov.hom cov (fun y ↦ cov.hom cov A y (Y y)) x u)).toLinearMap :=
    cov.mvfderiv_trace_comp cov (hD.mdifferentiable (by simp) x)
      (hA.mdifferentiable (by simp) x) u
  have hh := hessian_apply_eq_mvfderiv_sub x
    (((hA.clm_bundle_comp hA).trace_clm_bundle x).of_le (by simp))
    (FiberBundle.extend E u) Y (hY.mdifferentiable (by simp) x)
  rw [FiberBundle.extend_apply_self, heq, TauCeti.mvfderiv_const_smul_field,
    _root_.smul_apply, smul_eq_mul, hp,
    cov.mvfderiv_trace_comp_self (hA.mdifferentiable (by simp) x)] at hh
  rw [secondCovariantDerivative_apply (cov.hom cov) (leviCivitaConnection I M) hA x hY,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.toLinearMap_sub, map_sub]
  rw [hh]
  ring

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
  let T := fun i ↦ (cov.hom cov).secondCovariantDerivative (leviCivitaConnection I M)
    A x (b i) (b i)
  have hc : (A x).comp (∑ i, T i) = ∑ i, (A x).comp (T i) := by
    ext w
    simp
  have ht : LinearMap.trace ℝ (V x) ((A x).comp (∑ i, T i)).toLinearMap =
      ∑ i, LinearMap.trace ℝ (V x) ((A x).comp (T i)).toLinearMap := by
    rw [hc, ContinuousLinearMap.toLinearMap_sum, map_sum]
  dsimp only [T] at ht
  rw [(cov.hom cov).roughLaplacian_eq_sum (leviCivitaConnection I M) A x b,
    ContinuousLinearMap.comp_neg, ContinuousLinearMap.toLinearMap_neg, map_neg,
    laplaceBeltrami_eq_sum_hessian I _ x b]
  simp_rw [cov.hessian_trace_comp_self hA x]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ht]
  ring

end CovariantDerivative

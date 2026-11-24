/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Endomorphism
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trace
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian

/-!
# Differentiating traces of vector-valued bilinear tensors

Metric compatibility allows both metric contraction and endomorphism trace to commute with
the induced connection. The resulting identities identify a Palatini double contraction with
the scalar Laplace–Beltrami operator.

## References

* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, CUP (2006), §2.3.
* [Poincaré Conjecture](https://github.com/frenzymath/PoincareConjecture).
* [Lean evaluation submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public section

open Bundle FiberBundle CovariantDerivative TauCeti.Manifold
open scoped ContDiff Manifold Topology RealInnerProductSpace

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {C : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x}
  {x : M}

/-- Pair a vector-valued bilinear tensor with a vector field using the fibre metric. -/
private def lowerConnectionTensor
    (C : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (W : Π x : M, TangentSpace I x) (y : M) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I y) (TangentSpace I y) ℝ
    (innerSL ℝ (W y))).comp (C y)

omit [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- Evaluation of the lowered tensor is the fibre inner product. -/
private theorem lowerConnectionTensor_apply
    (W : Π x : M, TangentSpace I x) (y : M) (u v : TangentSpace I y) :
    lowerConnectionTensor C W y u v = ⟪W y, C y u v⟫ := rfl

/-- Covariantly differentiating a bilinear tensor paired with a vector field obeys the
product rule for the metric pairing. -/
private theorem deriv_lowerConnectionTensor
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (hC : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
      (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
      y (C y)) x)
    {W : Π x : M, TangentSpace I x} (hW : MDiffAt (T% W) x)
    (u v z : TangentSpace I x) :
    cov.derivBilinearTensor (lowerConnectionTensor C W) x u v z =
      ⟪W x, cov.hom (cov.hom cov) C x z u v⟫ + ⟪cov W x z, C x u v⟫ := by
  let U := extend E u
  let V := extend E v
  have hU : MDiffAt (T% U) x := mdifferentiableAt_extend I E u
  have hV : MDiffAt (T% V) x := mdifferentiableAt_extend I E v
  have hCU := hC.clm_bundle_apply hU
  have hCUV := hCU.clm_bundle_apply hV
  have hb : ∀ ⦃A B : Π y : M, TangentSpace I y⦄,
      MDiffAt (T% A) x → MDiffAt (T% B) x →
        MDiffAt (fun y ↦ lowerConnectionTensor C W y (A y) (B y)) x := by
    intro A B hA hB
    exact MDifferentiableAt.inner_bundle (IB := I) (F := E)
      (E := fun y : M ↦ TangentSpace I y) hW
      ((hC.clm_bundle_apply hA).clm_bundle_apply hB)
  have hp := hcov.mvfderiv_inner_eq (fun _ ↦ z) hW hCUV
  have h₁ := cov.hom_apply (cov.hom cov) hC hU z
  have h₂ := cov.hom_apply cov hCU hV z
  rw [← extend_apply_self E u, ← extend_apply_self E v,
    cov.derivBilinearTensor_apply hb hU hV]
  simp only [lowerConnectionTensor_apply] at hp ⊢
  rw [hp]
  have h₁' := congrArg (fun A ↦ A (V x)) h₁
  simp only [sub_apply] at h₁'
  rw [h₂] at h₁'
  simp only [U, V, extend_apply_self] at h₁' ⊢
  rw [h₁']
  simp only [inner_sub_right]
  ring

/-- The covariant derivative of a vector-valued bilinear tensor has zero metric trace
when the tensor itself has zero metric trace near the point. -/
private theorem sum_hom_self_eq_zero_of_mdifferentiable
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (hC : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
      (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
      y (C y)) x)
    (htrace : ∀ᶠ y in 𝓝 x, ∑ i, C y (stdOrthonormalBasis ℝ (TangentSpace I y) i)
      (stdOrthonormalBasis ℝ (TangentSpace I y) i) = 0)
    (z : TangentSpace I x) :
    ∑ i, cov.hom (cov.hom cov) C x z
      (stdOrthonormalBasis ℝ (TangentSpace I x) i)
      (stdOrthonormalBasis ℝ (TangentSpace I x) i) = 0 := by
  let e := stdOrthonormalBasis ℝ (TangentSpace I x)
  let q := ∑ i, cov.hom (cov.hom cov) C x z (e i) (e i)
  let W := extend E q
  have hW : MDiffAt (T% W) x := mdifferentiableAt_extend I E q
  have hb : ∀ ⦃A B : Π y : M, TangentSpace I y⦄,
      MDiffAt (T% A) x → MDiffAt (T% B) x →
        MDiffAt (fun y ↦ lowerConnectionTensor C W y (A y) (B y)) x := by
    intro A B hA hB
    exact MDifferentiableAt.inner_bundle (IB := I) (F := E)
      (E := fun y : M ↦ TangentSpace I y) hW
      ((hC.clm_bundle_apply hA).clm_bundle_apply hB)
  have hzero : (fun y ↦ LinearMap.BilinMap.metricTrace
      (ContinuousLinearMap.toLinearMap₁₂ (lowerConnectionTensor C W y))) =ᶠ[𝓝 x]
      fun _ ↦ 0 := by
    filter_upwards [htrace] with y hy
    rw [LinearMap.BilinMap.metricTrace_eq_sum _ (stdOrthonormalBasis ℝ (TangentSpace I y))]
    simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
      lowerConnectionTensor_apply]
    rw [← inner_sum, hy, inner_zero_right]
  have h := hcov.mvfderiv_metricTrace_apply_eq_sum hb e z
  rw [hzero.mvfderiv_eq] at h
  simp only [mvfderiv_const, zero_apply,
    deriv_lowerConnectionTensor hcov hC hW, Finset.sum_add_distrib,
    ← inner_sum] at h
  have htrace_x : ∑ i, C x (e i) (e i) = 0 := htrace.self_of_nhds
  rw [htrace_x, inner_zero_right, add_zero] at h
  -- The displayed orthonormal contraction is the vector `q` defined above.
  change q = 0
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  simpa only [W, extend_apply_self] using h.symm

/-- Covariant differentiation preserves a metric trace vanishing near `x`, including when
the tensor is not differentiable and the induced connection is totalized to zero. -/
theorem sum_hom_self_eq_zero
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (htrace : ∀ᶠ y in 𝓝 x, ∑ i, C y (stdOrthonormalBasis ℝ (TangentSpace I y) i)
      (stdOrthonormalBasis ℝ (TangentSpace I y) i) = 0)
    (z : TangentSpace I x) :
    ∑ i, cov.hom (cov.hom cov) C x z
      (stdOrthonormalBasis ℝ (TangentSpace I x) i)
      (stdOrthonormalBasis ℝ (TangentSpace I x) i) = 0 := by
  by_cases hC : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
      (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
      y (C y)) x
  · exact sum_hom_self_eq_zero_of_mdifferentiable hcov hC htrace z
  · simp [hom_eq_zero_of_not_mdifferentiableAt cov (cov.hom cov) hC]

/-- If the endomorphism trace of a bilinear tensor is minus the differential of `f` near `x`,
its differentiated endomorphism trace is minus the Hessian of `f`. Agreement with the
Levi-Civita connection is only required on differentiable fields at the point. -/
theorem trace_hom_eq_neg_hessian
    (hLC : ∀ ⦃U : Π y : M, TangentSpace I y⦄, MDiffAt (T% U) x →
      ∀ z : TangentSpace I x, cov U x z = leviCivitaConnection I M U x z)
    (hC : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
      (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
      y (C y)) x)
    {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (htrace : ∀ᶠ y in 𝓝 x, ∀ u, LinearMap.trace ℝ (TangentSpace I y) (C y u).toLinearMap =
      -mvfderiv I f y u)
    (z u : TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x)
      (cov.hom (cov.hom cov) C x z u).toLinearMap = -hessian I f x z u := by
  let U := extend E u
  have hU : MDiffAt (T% U) x := mdifferentiableAt_extend I E u
  have hCU := hC.clm_bundle_apply hU
  have h₁ := cov.hom_apply (cov.hom cov) hC hU z
  have h := congrArg
    (fun A : TangentSpace I x →L[ℝ] TangentSpace I x ↦
      LinearMap.trace ℝ (TangentSpace I x) A.toLinearMap) h₁
  simp only [ContinuousLinearMap.toLinearMap_sub, map_sub] at h
  rw [← cov.mvfderiv_trace_eq_trace_hom hCU z, htrace.self_of_nhds] at h
  have hfun : (fun y ↦ LinearMap.trace ℝ (TangentSpace I y) (C y (U y)).toLinearMap) =ᶠ[𝓝 x]
      fun y ↦ -mvfderiv I f y (U y) := htrace.mono fun y hy ↦ hy (U y)
  rw [hfun.mvfderiv_eq, mvfderiv_fun_neg] at h
  have hh := hessian_apply_eq_mvfderiv_sub x hf (fun _ ↦ z) U hU
  rw [hLC hU z] at h
  simp only [U, extend_apply_self, neg_apply] at h hh
  linarith

/-- A bilinear tensor with zero metric trace and endomorphism trace `-df` near `x` has
Palatini double contraction equal to the Laplace–Beltrami operator of `f`. -/
theorem sum_palatini_eq_laplaceBeltrami
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (hLC : ∀ ⦃U : Π y : M, TangentSpace I y⦄, MDiffAt (T% U) x →
      ∀ z : TangentSpace I x, cov U x z = leviCivitaConnection I M U x z)
    (hC : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
      (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
      y (C y)) x)
    {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hV : ∀ᶠ y in 𝓝 x, ∑ i, C y (stdOrthonormalBasis ℝ (TangentSpace I y) i)
      (stdOrthonormalBasis ℝ (TangentSpace I y) i) = 0)
    (hθ : ∀ᶠ y in 𝓝 x, ∀ u, LinearMap.trace ℝ (TangentSpace I y) (C y u).toLinearMap =
      -mvfderiv I f y u) :
    let e := stdOrthonormalBasis ℝ (TangentSpace I x)
    ∑ j, ∑ i, ⟪e i, cov.hom (cov.hom cov) C x (e i) (e j) (e j) -
      cov.hom (cov.hom cov) C x (e j) (e j) (e i)⟫ = laplaceBeltrami I f x := by
  let e := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hzero (i) : ∑ j, cov.hom (cov.hom cov) C x (e i) (e j) (e j) = 0 :=
    sum_hom_self_eq_zero hcov hV (e i)
  have hfirst : ∑ j, ∑ i, ⟪e i, cov.hom (cov.hom cov) C x (e i) (e j) (e j)⟫ = 0 := by
    rw [Finset.sum_comm]
    simp only [← inner_sum, hzero, inner_zero_right, Finset.sum_const_zero]
  have hsecond : ∑ j, ∑ i, ⟪e i, cov.hom (cov.hom cov) C x (e j) (e j) (e i)⟫ =
      -laplaceBeltrami I f x := by
    calc
      _ = ∑ j, -hessian I f x (e j) (e j) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simpa only [LinearMap.trace_eq_sum_inner _ e, ContinuousLinearMap.coe_coe] using
          trace_hom_eq_neg_hessian hLC hC hf hθ (e j) (e j)
      _ = _ := by rw [laplaceBeltrami_eq_sum_hessian I f x e, Finset.sum_neg_distrib]
  -- Expand the two traces in the orthonormal basis fixed above.
  change ∑ j, ∑ i, ⟪e i, cov.hom (cov.hom cov) C x (e i) (e j) (e j) -
    cov.hom (cov.hom cov) C x (e j) (e j) (e i)⟫ = _
  simp only [inner_sub_right, Finset.sum_sub_distrib, hfirst, hsecond]
  ring

end CovariantDerivative

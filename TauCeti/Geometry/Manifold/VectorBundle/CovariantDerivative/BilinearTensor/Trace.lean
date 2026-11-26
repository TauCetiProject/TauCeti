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
the induced connection. For a vector-valued bilinear tensor `C`, the metric trace `tr_g C` is a
vector field whose divergence is the corresponding double contraction of `∇C`, and when the
endomorphism trace `u ↦ tr (C(u, ·))` is a differential `df`, the double contraction of `∇C` against
it is the Laplacian of `f`. Together they evaluate the Palatini double contraction of `C`. When `C`
is the variation of a connection which is torsion-free at the point, this is the metric trace of the
first variation of the Ricci tensor; torsion of the base connection contributes a further term.

## Main results

* `CovariantDerivative.IsMetricCompatible.sum_inner_hom_hom_eq_divergence_metricTrace`: the
  divergence of `tr_g C` as a double contraction of `∇C`.
* `CovariantDerivative.trace_hom_eq_hessian`: the differentiated endomorphism trace of `C` is the
  Hessian of `f` when its endomorphism trace is `df`.
* `CovariantDerivative.IsMetricCompatible.sum_palatini_eq_divergence_sub_laplaceBeltrami`: the
  Palatini double contraction of `C` is `div (tr_g C) - Δ f`.

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

/-- The divergence of the metric trace `tr_g C` of a differentiable vector-valued bilinear tensor
`C` is the double contraction `∑ᵢ ⟪eᵢ, tr_g (∇_{eᵢ} C)⟫`: the metric trace commutes with the metric
connection. Agreement with the Levi-Civita connection is only required on differentiable fields
at the point. -/
theorem IsMetricCompatible.sum_inner_hom_hom_eq_divergence_metricTrace
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (hLC : ∀ ⦃U : Π y : M, TangentSpace I y⦄, MDiffAt (T% U) x →
      ∀ z : TangentSpace I x, cov U x z = leviCivitaConnection I M U x z)
    (hC : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
      (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
      y (C y)) x)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    ∑ j, ∑ i, ⟪e i, cov.hom (cov.hom cov) C x (e i) (e j) (e j)⟫ =
      divergence I
        (fun y ↦ LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (C y))) x := by
  rw [divergence_def, LinearMap.trace_eq_sum_inner _ e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ContinuousLinearMap.coe_coe, ← hLC hC.metricTrace,
    hcov.covariantDerivative_metricTrace cov hC, LinearMap.BilinMap.metricTrace_eq_sum _ e,
    inner_sum]
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]

/-- If the endomorphism trace of a bilinear tensor is the differential of `f` near `x`,
its differentiated endomorphism trace is the Hessian of `f`. Agreement with the
Levi-Civita connection is only required on differentiable fields at the point. -/
theorem trace_hom_eq_hessian
    (hLC : ∀ ⦃U : Π y : M, TangentSpace I y⦄, MDiffAt (T% U) x →
      ∀ z : TangentSpace I x, cov U x z = leviCivitaConnection I M U x z)
    (hC : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
      (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
      y (C y)) x)
    {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (htrace : ∀ᶠ y in 𝓝 x, ∀ u, LinearMap.trace ℝ (TangentSpace I y) (C y u).toLinearMap =
      mvfderiv I f y u)
    (z u : TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x)
      (cov.hom (cov.hom cov) C x z u).toLinearMap = hessian I f x z u := by
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
      fun y ↦ mvfderiv I f y (U y) := htrace.mono fun y hy ↦ hy (U y)
  rw [hfun.mvfderiv_eq] at h
  have hh := hessian_apply_eq_mvfderiv_sub x hf (fun _ ↦ z) U hU
  rw [hLC hU z] at h
  simp only [U, extend_apply_self] at h hh
  linarith

/-- **The contracted Palatini expression.** Let `C` be a differentiable vector-valued bilinear
tensor whose endomorphism trace `u ↦ tr (C(u, ·))` is the differential of `f` near `x`. Its Palatini
double contraction is the divergence of its metric trace `tr_g C` minus the Laplace–Beltrami
operator of `f`. The connection is assumed metric compatible and to agree with the Levi-Civita
connection on differentiable fields at `x`. -/
theorem IsMetricCompatible.sum_palatini_eq_divergence_sub_laplaceBeltrami
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (hLC : ∀ ⦃U : Π y : M, TangentSpace I y⦄, MDiffAt (T% U) x →
      ∀ z : TangentSpace I x, cov U x z = leviCivitaConnection I M U x z)
    (hC : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
      (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)
      y (C y)) x)
    {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hθ : ∀ᶠ y in 𝓝 x, ∀ u, LinearMap.trace ℝ (TangentSpace I y) (C y u).toLinearMap =
      mvfderiv I f y u)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    ∑ j, ∑ i, ⟪e i, cov.hom (cov.hom cov) C x (e i) (e j) (e j) -
      cov.hom (cov.hom cov) C x (e j) (e j) (e i)⟫ =
      divergence I
        (fun y ↦ LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (C y))) x -
        laplaceBeltrami I f x := by
  simp only [inner_sub_right, Finset.sum_sub_distrib]
  rw [hcov.sum_inner_hom_hom_eq_divergence_metricTrace hLC hC e,
    laplaceBeltrami_eq_sum_hessian I f x e]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simpa only [LinearMap.trace_eq_sum_inner _ e, ContinuousLinearMap.coe_coe] using
    trace_hom_eq_hessian hLC hC hf hθ (e j) (e j)

end CovariantDerivative

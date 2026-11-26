/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor.Divergence
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar.Trace
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.RicciVariation
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Trace
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor.Trace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Existence
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Family
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Regularity
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trace
import TauCeti.Geometry.Manifold.VectorBundle.Trivial
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The first variation of the scalar curvature of a family of metrics

Let `g` be a smooth family of metrics on `M` parametrized by a manifold `P`, let `c` be a parameter
curve which is `C²` at `t`, and write `g = g_{c t}`, `Ric` for its Ricci tensor, and
`h = δ_{c'(t)} g` for the first variation of the family in the direction of the velocity of `c`.
This file proves

`∂ₛ Scal(g_{c s}) = div (div h) - Δ (tr_g h) - ⟨h, Ric⟩` at `s = t`,

with `Δ = div ∘ grad`, for metrics which are positive near `t`. The divergence
`(div h)_j = ∇^i h_ij` is `CovariantDerivative.divBilinearTensor`, and `div (div h)` is the
Riemannian divergence of the vector field dual to it. The pairing is
`⟨h, Ric⟩ = ∑ᵢⱼ h(eᵢ, eⱼ) Ric(eᵢ, eⱼ)` in any orthonormal basis, or `tr (g⁻¹ h g⁻¹ Ric)` with
indices raised by the metric.

Scalar curvature is the trace `tr (g⁻¹ Ric)`. Differentiating the inverse metric produces
`-⟨h, Ric⟩`. Differentiating the Ricci tensor produces, by the Palatini identity, the double
contraction of `∇Γ'`, where `Γ'` is the variation of the Levi-Civita connection. By the first
variation formula of the connection, the metric trace of `Γ'` is dual to `div h - ½ d (tr_g h)` and
its endomorphism trace is `½ d (tr_g h)`, so this contraction is `div (div h) - Δ (tr_g h)`.

Along the variation `h = a g` by a constant `a`, as for a constant rescaling `φ(s) g₀`, the first
two terms vanish and the derivative is `-a Scal`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.hasDerivAt_scalarCurvature_of_hasDerivAt_ricciTensor`: the
  derivative of scalar curvature in terms of the derivatives of the metric and of the Ricci tensor
  at the point.

In the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetricFamily`:

* `contMDiff_metricTrace_variation` and `mvfderiv_metricTrace_variation`: the trace of the first
  variation against the installed metric is smooth, with derivative the trace of `∇h`.
* `metricTrace_deriv_difference_eq_rieszDual_divBilinearTensor_sub_mgradient` and
  `trace_deriv_difference_eq_mvfderiv`: the metric trace and the endomorphism trace of the variation
  of the Levi-Civita connection.
* `hasDerivAt_scalarCurvature`: the first variation of scalar curvature.
* `hasDerivAt_scalarCurvature_sum`: the same formula with `⟨h, Ric⟩` in an orthonormal basis.
* `hasDerivAt_scalarCurvature_of_derivBilinearTensor_eq_zero`: the first variation is `-⟨h, Ric⟩`
  where `h` is parallel.
* `hasDerivAt_scalarCurvature_of_variation_eq_mul_inner`: the first variation is `-a Scal` where
  `h` is parallel and equal to `a g` at the point.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.K, Theorem 1.174.
* B. Chow and D. Knopf, *The Ricci Flow: An Introduction*, AMS (2004), Chapter 3, Lemma 3.9.
* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, CUP (2006),
  Proposition 2.3.9.
-/

public section

open Bundle FiberBundle Filter Riemannian.Tensor
open scoped ContDiff Manifold Topology RealInnerProductSpace

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {cov : ℝ → CovariantDerivative I E (fun x : M ↦ TangentSpace I x)} {t : ℝ}
  [∀ s, CovariantDerivative.ContMDiffCovariantDerivative (cov s) ∞]

/-- **Differentiating scalar curvature.** Let `r s` be Riemannian metrics with smooth Levi-Civita
connections `∇ˢ` for `s` near `t`. If at the point `x` the metrics have derivative `h` at `t` and
their Ricci tensors have derivative `K`, then the scalar curvatures at `x` have derivative
`tr (g⁻¹ K) - tr (g⁻¹ h g⁻¹ Ric)` at `t`, with `g = r t`. -/
theorem hasDerivAt_scalarCurvature_of_hasDerivAt_ricciTensor
    {r : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)} {x : M}
    {h K : E →L[ℝ] E →L[ℝ] ℝ}
    (hcov : ∀ᶠ s in 𝓝 t, (r s).toNondegenerateMetric.IsLeviCivitaConnection (cov s))
    (hh : ∀ v w, HasDerivAt (fun s ↦ (r s).toNondegenerateMetric x v w) (h v w) t)
    (hK : ∀ v w : TangentSpace I x,
      HasDerivAt (fun s ↦ (cov s).ricciTensor x v w) (K v w) t) :
    HasDerivAt (fun s ↦ (r s).scalarCurvature x)
      (TauCeti.traceCLM ℝ E (((r t).toNondegenerateMetric x).inverse ∘L K) -
        TauCeti.traceCLM ℝ E ((((r t).toNondegenerateMetric x).inverse ∘L h) ∘L
          (((r t).toNondegenerateMetric x).inverse ∘L
            ((cov t).ricciTensor x).toContinuousBilinearMap))) t := by
  refine (TauCeti.Manifold.ContMDiffNondegenerateMetric.hasDerivAt_trace_inverse_comp
    (g := fun s ↦ (r s).toNondegenerateMetric) (x := x)
    (B := fun s ↦ ((cov s).ricciTensor x).toContinuousBilinearMap) hh hK).congr_of_eventuallyEq
    (hcov.mono fun s hs ↦ (r s).scalarCurvature_eq_trace_inverse_ricciTensor (cov s) hs x)

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (g : ContMDiffNondegenerateMetricFamily I M IP P) {c : ℝ → P}
  {cov : ℝ → CovariantDerivative I E (fun x : M ↦ TangentSpace I x)} {t : ℝ}

omit [T2Space M] [IsManifold IP 1 P]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Along a parameter curve, the members of the family have smooth Levi-Civita connections. -/
private theorem exists_isLeviCivitaConnection_comp (c : ℝ → P) :
    ∃ cov : ℝ → CovariantDerivative I E (fun x : M ↦ TangentSpace I x),
      (∀ s, (g.metric (c s)).IsLeviCivitaConnection (cov s)) ∧
        ∀ s, CovariantDerivative.ContMDiffCovariantDerivative (cov s) ∞ :=
  ⟨fun s ↦ (g.metric (c s)).leviCivitaConnection,
    fun s ↦ (g.metric (c s)).isLeviCivitaConnection_leviCivitaConnection,
    fun s ↦
      (g.metric (c s)).isLeviCivitaConnection_leviCivitaConnection.contMDiffCovariantDerivative
        le_rfl⟩

omit [T2Space M] in
/-- The trace of the first variation `h = δ_u g` against the installed metric is a smooth
function. This is the trace `tr_g h` against the family member `g.metric p` when that member is the
installed metric. -/
theorem contMDiff_metricTrace_variation (p : P) (u : TangentSpace IP p) :
    ContMDiff I 𝓘(ℝ) ∞ fun y : M ↦
      LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (g.variation p u y)) := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  exact (Bundle.Trivial.contMDiff_mk_iff.1 fun x ↦
    ContMDiffAt.metricTrace (V := Bundle.Trivial M ℝ) (g.contMDiff_variation p u x)).2

omit [T2Space M] in
/-- The derivative along `w` of the trace of the first variation `h = δ_u g` against the installed
metric, for a connection compatible with the installed metric, is `∑ᵢ (∇_w h)(eᵢ, eᵢ)`. The trace
is `tr_g h` against the family member `g.metric p` when that member is the installed metric. -/
theorem mvfderiv_metricTrace_variation {cov : CovariantDerivative I E (TangentSpace I)}
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (p : P) (u : TangentSpace IP p) (y : M) {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (TangentSpace I y)) (w : TangentSpace I y) :
    mvfderiv I (fun z : M ↦ LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂
        (g.variation p u z))) y w =
      ∑ i, cov.derivBilinearTensor (g.variation p u) y (e i) (e i) w :=
  hcov.mvfderiv_metricTrace_apply_eq_sum (fun _ _ hσ hτ ↦
    Bundle.Trivial.mdifferentiableAt_section_iff.1
      ((((g.contMDiff_variation p u y).mdifferentiableAt (by simp)).clm_bundle_apply
        hσ).clm_bundle_apply hτ)) e w

section LeviCivita

variable (hc : ContMDiffAt 𝓘(ℝ) IP 2 c t)
  (hcov : ∀ s, (g.metric (c s)).IsLeviCivitaConnection (cov s))
  (hg : ∀ y (u v : TangentSpace I y), g (c t, y) u v = inner ℝ u v)
include hc hcov hg

omit [T2Space M] in
/-- The metric trace of the variation `Γ'` of the Levi-Civita connection is dual to
`div h - ½ d (tr_g h)`. -/
theorem metricTrace_deriv_difference_eq_rieszDual_divBilinearTensor_sub_mgradient (y : M) :
    LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂
      (deriv (fun s ↦ (cov s).difference (cov t) y) t :
        TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y)) =
    rieszDual y ((cov t).divBilinearTensor (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1)) y) -
      mgradient I ((2⁻¹ : ℝ) • fun z : M ↦ LinearMap.BilinMap.metricTrace
        (ContinuousLinearMap.toLinearMap₁₂
          (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) z))) y := by
  let e := stdOrthonormalBasis ℝ (TangentSpace I y)
  refine ext_inner_right ℝ fun w ↦ ?_
  rw [LinearMap.BilinMap.metricTrace_eq_sum _ e, sum_inner, inner_sub_left, inner_rieszDual,
    mgradient_smul, Pi.smul_apply, real_inner_smul_left, inner_mgradient,
    g.mvfderiv_metricTrace_variation
      (g.isLeviCivitaConnection_of_apply_eq_inner (hcov t) hg).isMetricCompatible _ _ y e w,
    (cov t).divBilinearTensor_apply_eq_sum _ e, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h := g.two_mul_apply_deriv_difference_eq_derivBilinearTensor hc hcov y (e i) (e i) w
  rw [hg] at h
  rw [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]
  linarith

omit [T2Space M] in
/-- The endomorphism trace of the variation `Γ'` of the Levi-Civita connection is
`½ d (tr_g h)`. -/
theorem trace_deriv_difference_eq_mvfderiv (y : M) (u : TangentSpace I y) :
    LinearMap.trace ℝ (TangentSpace I y)
      (deriv (fun s ↦ (cov s).difference (cov t) y) t u :
        TangentSpace I y →L[ℝ] TangentSpace I y).toLinearMap =
      mvfderiv I ((2⁻¹ : ℝ) • fun z : M ↦ LinearMap.BilinMap.metricTrace
        (ContinuousLinearMap.toLinearMap₁₂
          (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) z))) y u := by
  let e := stdOrthonormalBasis ℝ (TangentSpace I y)
  refine Eq.trans ?_ (congrArg (fun L ↦ L u) (TauCeti.mvfderiv_const_smul
    ((g.contMDiff_metricTrace_variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) y).mdifferentiableAt
      (by simp)) (2⁻¹ : ℝ))).symm
  rw [LinearMap.trace_eq_sum_inner _ e, smul_apply, g.mvfderiv_metricTrace_variation
    (g.isLeviCivitaConnection_of_apply_eq_inner (hcov t) hg).isMetricCompatible _ _ y e u,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h := g.two_mul_apply_deriv_difference_eq_derivBilinearTensor hc hcov y u (e i) (e i)
  have hs := congrArg (fun L ↦ L (e i)) ((cov t).derivBilinearTensor_apply_comm
    (g.variation_apply_comm (c t) (mfderiv 𝓘(ℝ) IP c t 1)) (x := y) u (e i))
  rw [hg, real_inner_comm] at h
  rw [ContinuousLinearMap.coe_coe]
  linarith

omit [T2Space M] in
/-- The Palatini double contraction of the variation `Γ'` of the Levi-Civita connection is
`div (div h) - Δ (tr_g h)`. -/
private theorem sum_palatini_deriv_difference (x : M) {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    let C := fun y ↦ deriv (fun s ↦ (cov s).difference (cov t) y) t
    ∑ j, ∑ i, ⟪e i, (cov t).hom ((cov t).hom (cov t)) C x (e i) (e j) (e j) -
        (cov t).hom ((cov t).hom (cov t)) C x (e j) (e j) (e i)⟫ =
      divergence I (fun y ↦ rieszDual y
        ((cov t).divBilinearTensor (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1)) y)) x -
      laplaceBeltrami I (fun y ↦ LinearMap.BilinMap.metricTrace
        (ContinuousLinearMap.toLinearMap₁₂ (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) y))) x := by
  intro C
  set τ : M → ℝ := fun y ↦ LinearMap.BilinMap.metricTrace
    (ContinuousLinearMap.toLinearMap₁₂ (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) y))
  have hτ : ContMDiff I 𝓘(ℝ) 2 τ := (g.contMDiff_metricTrace_variation _ _).of_le (by simp)
  have hLC := g.isLeviCivitaConnection_of_apply_eq_inner (hcov t) hg
  have hC : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
      (E := fun y ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y) y (C y)) x :=
    (g.contMDiff_deriv_difference_of_isLeviCivitaConnection hc hcov x).mdifferentiableAt (by simp)
  have hτ' : ContMDiffAt I 𝓘(ℝ) 2 ((2⁻¹ : ℝ) • τ) x := contMDiffAt_const.mul (hτ x)
  have hX : (fun y ↦ rieszDual y
      ((cov t).divBilinearTensor (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1)) y)) =
      (fun y ↦ LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂ (C y))) +
        mgradient I ((2⁻¹ : ℝ) • τ) := by
    funext y
    rw [Pi.add_apply,
      g.metricTrace_deriv_difference_eq_rieszDual_divBilinearTensor_sub_mgradient hc hcov hg y,
      sub_add_cancel]
  rw [hLC.isMetricCompatible.sum_palatini_eq_divergence_sub_laplaceBeltrami
    (fun _ hU z ↦ congr($(g.apply_eq_leviCivitaConnection_of_apply_eq_inner (hcov t) hg hU) z))
    hC hτ'
    (.of_forall (g.trace_deriv_difference_eq_mvfderiv hc hcov hg)) e, hX,
    divergence_add I _ _ x hC.metricTrace (mdifferentiableAt_mgradient hτ'),
    ← laplaceBeltrami_def, laplaceBeltrami_smul I _ hτ]
  ring

variable [∀ s, CovariantDerivative.ContMDiffCovariantDerivative (cov s) ∞]

/-- The contraction of the first variation of the Ricci tensor with the inverse metric is
`div (div h) - Δ (tr_g h)`. -/
private theorem traceCLM_inverse_comp_eq (x : M) {K : E →L[ℝ] E →L[ℝ] ℝ}
    (hK : ∀ u v : TangentSpace I x, HasDerivAt (fun s ↦ (cov s).ricciTensor x u v) (K u v) t) :
    traceCLM ℝ E ((g.metric (c t) x).inverse ∘L K) =
      divergence I (fun y ↦ rieszDual y
        ((CovariantDerivative.leviCivitaConnection I M).divBilinearTensor
          (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1)) y)) x -
      laplaceBeltrami I (fun y ↦ LinearMap.BilinMap.metricTrace
        (ContinuousLinearMap.toLinearMap₁₂ (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) y))) x := by
  let e := stdOrthonormalBasis ℝ (TangentSpace I x)
  let Kx : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := K
  have hdiv (y : M) : (CovariantDerivative.leviCivitaConnection I M).divBilinearTensor
      (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1)) y =
      (cov t).divBilinearTensor (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1)) y :=
    CovariantDerivative.divBilinearTensor_congr _ _ fun _ hY ↦
      (g.apply_eq_leviCivitaConnection_of_apply_eq_inner (hcov t) hg hY).symm
  simp only [hdiv]
  rw [← g.sum_palatini_deriv_difference hc hcov hg x e]
  calc
    -- The tangent fibre and model give the same fixed-space contraction.
    _ = traceCLM ℝ (TangentSpace I x) ((g.metric (c t) x).inverse ∘L Kx) := rfl
    _ = LinearMap.BilinMap.metricTrace Kx.toBilinForm :=
      ContinuousLinearMap.traceCLM_inverse_comp_eq_metricTrace (g.metric (c t) x)
        (g.metric_apply_eq_inner_of_apply_eq_inner hg x) Kx
    _ = ∑ j, Kx (e j) (e j) := by
      simpa only [ContinuousLinearMap.toBilinForm_apply] using
        LinearMap.BilinMap.metricTrace_eq_sum Kx.toBilinForm e
    _ = _ := by
      refine Finset.sum_congr rfl fun j _ ↦ (hK (e j) (e j)).unique
        ((g.hasDerivAt_ricciTensor_sum_of_isLeviCivitaConnection hc hcov x e.toBasis
          (e j) (e j)).congr_deriv ?_)
      simp only [e.coe_toBasis, e.coe_toBasis_repr_apply, e.repr_apply_apply]

omit [IsManifold IP 1 P] in
/-- The derivative of scalar curvature along a parameter curve in terms of a derivative `K` of the
Ricci tensors at the point. -/
private theorem hasDerivAt_scalarCurvature_of_hasDerivAt_ricciTensor
    {r : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    (hr : ∀ᶠ s in 𝓝 t, g.metric (c s) = (r s).toNondegenerateMetric) (x : M)
    {K : E →L[ℝ] E →L[ℝ] ℝ}
    (hK : ∀ u v : TangentSpace I x, HasDerivAt (fun s ↦ (cov s).ricciTensor x u v) (K u v) t) :
    HasDerivAt (fun s ↦ (r s).scalarCurvature x)
      (traceCLM ℝ E ((g.metric (c t) x).inverse ∘L K) -
        traceCLM ℝ E (((g.metric (c t) x).inverse ∘L
          g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) x) ∘L ((g.metric (c t) x).inverse ∘L
            ((CovariantDerivative.leviCivitaConnection I M).ricciTensor
              x).toContinuousBilinearMap))) t := by
  have hh (v w : E) : HasDerivAt (fun s ↦ (r s).toNondegenerateMetric x v w)
      (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) x v w) t :=
    (g.hasDerivAt_apply_apply_comp (hc.mdifferentiableAt two_ne_zero) x v w).congr_of_eventuallyEq
      (hr.mono fun s hs ↦ by simp only [← hs, metric_apply])
  refine (ContMDiffRiemannianMetric.hasDerivAt_scalarCurvature_of_hasDerivAt_ricciTensor
    (hr.mono fun s hs ↦ hs ▸ hcov s) hh hK).congr_deriv ?_
  rw [← hr.self_of_nhds, (hcov t).ricciTensor_eq_ricciTensor_leviCivitaConnection
    (g.metric_apply_eq_inner_of_apply_eq_inner hg) x]
  -- Both sides read the tangent fibre as the model space.
  rfl

end LeviCivita

/-- **The first variation of scalar curvature.** Let `g` be a smooth family of metrics parametrized
by `P`, let `c` be a parameter curve which is `C²` at `t`, and suppose that `g_{c s}` is the
Riemannian metric `r s` for `s` near `t`. Write `h = δ_{c'(t)} g` for the first variation of `g` in
the direction of the velocity of `c`. If the installed fibre inner product is `g_{c t}`, then

`∂ₛ Scal(g_{c s}) = div (div h) - Δ (tr_g h) - tr (g⁻¹ h g⁻¹ Ric)` at `s = t`,

where `div (div h)` is the divergence of the vector field dual to `div h`. The last term is the
pairing `⟨h, Ric⟩`, expanded in an orthonormal basis in `hasDerivAt_scalarCurvature_sum`. -/
theorem hasDerivAt_scalarCurvature (hc : ContMDiffAt 𝓘(ℝ) IP 2 c t)
    {r : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    (hr : ∀ᶠ s in 𝓝 t, g.metric (c s) = (r s).toNondegenerateMetric)
    (hg : ∀ y (u v : TangentSpace I y), g (c t, y) u v = inner ℝ u v) (x : M) :
    HasDerivAt (fun s ↦ (r s).scalarCurvature x)
      (divergence I (fun y ↦ rieszDual y
          ((CovariantDerivative.leviCivitaConnection I M).divBilinearTensor
            (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1)) y)) x -
        laplaceBeltrami I (fun y ↦ LinearMap.BilinMap.metricTrace
          (ContinuousLinearMap.toLinearMap₁₂ (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) y))) x -
        traceCLM ℝ E (((g.metric (c t) x).inverse ∘L
          g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) x) ∘L ((g.metric (c t) x).inverse ∘L
            ((CovariantDerivative.leviCivitaConnection I M).ricciTensor
              x).toContinuousBilinearMap))) t := by
  obtain ⟨cov, hcov, _⟩ := g.exists_isLeviCivitaConnection_comp c
  let B (s : ℝ) : E →L[ℝ] E →L[ℝ] ℝ := ((cov s).ricciTensor x).toContinuousBilinearMap
  have hB : HasDerivAt (F := E →L[ℝ] E →L[ℝ] ℝ) B (deriv B t) t := by
    apply DifferentiableAt.hasDerivAt (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
    exact differentiableAt_clm_apply₂.mpr fun u v ↦
      (g.hasDerivAt_ricciTensor_of_isLeviCivitaConnection hc hcov x u v).differentiableAt
  have hK (u v : TangentSpace I x) :
      HasDerivAt (fun s ↦ (cov s).ricciTensor x u v) (deriv B t u v) t :=
    hasDerivAt_clm_apply₂.mp hB u v
  rw [← g.traceCLM_inverse_comp_eq hc hcov hg x hK]
  exact g.hasDerivAt_scalarCurvature_of_hasDerivAt_ricciTensor hc hcov hg hr x hK

/-- **The first variation of scalar curvature, in an orthonormal basis.** In the setting of
`hasDerivAt_scalarCurvature`, for every orthonormal basis `bᵢ` of `T_x M`,

`∂ₛ Scal(g_{c s}) = div (div h) - Δ (tr_g h) - ∑ᵢⱼ h(bᵢ, bⱼ) Ric(bᵢ, bⱼ)` at `s = t`. -/
theorem hasDerivAt_scalarCurvature_sum (hc : ContMDiffAt 𝓘(ℝ) IP 2 c t)
    {r : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    (hr : ∀ᶠ s in 𝓝 t, g.metric (c s) = (r s).toNondegenerateMetric)
    (hg : ∀ y (u v : TangentSpace I y), g (c t, y) u v = inner ℝ u v) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    HasDerivAt (fun s ↦ (r s).scalarCurvature x)
      (divergence I (fun y ↦ rieszDual y
          ((CovariantDerivative.leviCivitaConnection I M).divBilinearTensor
            (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1)) y)) x -
        laplaceBeltrami I (fun y ↦ LinearMap.BilinMap.metricTrace
          (ContinuousLinearMap.toLinearMap₁₂ (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) y))) x -
        ∑ i, ∑ j, g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) x (b i) (b j) *
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x (b i) (b j)) t := by
  refine (g.hasDerivAt_scalarCurvature hc hr hg x).congr_deriv (congrArg _ ?_)
  let h : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) x
  let Ric : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    ((CovariantDerivative.leviCivitaConnection I M).ricciTensor x).toContinuousBilinearMap
  let G : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := g.metric (c t) x
  have hG (u v : TangentSpace I x) : G u v = inner ℝ u v :=
    g.metric_apply_eq_inner_of_apply_eq_inner hg x u v
  have hinv : G.IsInvertible := (g.metric (c t)).isInvertible x
  -- The tangent fibre and model give the same contraction, a metric trace of `h ∘ g⁻¹ ∘ Ric`.
  calc
    _ = traceCLM ℝ (TangentSpace I x) (G.inverse ∘L (h ∘L (G.inverse ∘L Ric))) := rfl
    _ = ∑ i, h (G.inverse (Ric (b i))) (b i) := by
      rw [G.traceCLM_inverse_comp_eq_metricTrace hG, LinearMap.BilinMap.metricTrace_eq_sum _ b]
      simp only [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.comp_apply]
    _ = ∑ i, ∑ j, h (b i) (b j) * Ric (b i) (b j) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← b.sum_repr' (G.inverse (Ric (b i)))]
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [real_inner_comm, ← hG, hinv.self_apply_inverse, mul_comm]
      exact congrArg (· * _) (g.variation_apply_comm _ _ x (b j) (b i))

/-- **The first variation of scalar curvature along a parallel variation.** In the setting of
`hasDerivAt_scalarCurvature`, if the first variation `h` is parallel near `x`, then the derivative
at `t` of the scalar curvature at `x` is `-⟨h, Ric⟩ = -tr (g⁻¹ h g⁻¹ Ric)`. -/
theorem hasDerivAt_scalarCurvature_of_derivBilinearTensor_eq_zero
    (hc : ContMDiffAt 𝓘(ℝ) IP 2 c t)
    {r : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    (hr : ∀ᶠ s in 𝓝 t, g.metric (c s) = (r s).toNondegenerateMetric)
    (hg : ∀ y (u v : TangentSpace I y), g (c t, y) u v = inner ℝ u v) {x : M}
    (hh : ∀ᶠ y in 𝓝 x, (CovariantDerivative.leviCivitaConnection I M).derivBilinearTensor
      (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1)) y = 0) :
    HasDerivAt (fun s ↦ (r s).scalarCurvature x)
      (-traceCLM ℝ E (((g.metric (c t) x).inverse ∘L
          g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) x) ∘L ((g.metric (c t) x).inverse ∘L
            ((CovariantDerivative.leviCivitaConnection I M).ricciTensor
              x).toContinuousBilinearMap))) t := by
  obtain ⟨cov, hcov, _⟩ := g.exists_isLeviCivitaConnection_comp c
  have hK := g.hasDerivAt_ricciTensor_zero_of_derivBilinearTensor_eq_zero hc hcov
    (hh.mono fun y hy ↦ ((cov t).derivBilinearTensor_congr fun _ hY ↦
      g.apply_eq_leviCivitaConnection_of_apply_eq_inner (hcov t) hg hY).trans hy)
  -- The inverse metric, read on the model space, where `Ric'` vanishes.
  let A : (E →L[ℝ] ℝ) →L[ℝ] E := (g.metric (c t) x).inverse
  have hA : traceCLM ℝ E (A ∘L (0 : E →L[ℝ] E →L[ℝ] ℝ)) = 0 := by
    rw [ContinuousLinearMap.comp_zero, map_zero]
  exact (g.hasDerivAt_scalarCurvature_of_hasDerivAt_ricciTensor hc hcov hg hr x (K := 0)
    hK).congr_deriv ((congrArg (· - _) hA).trans (zero_sub _))

/-- **The first variation of scalar curvature along a constant rescaling.** In the setting of
`hasDerivAt_scalarCurvature`, if the first variation `h` is parallel near `x` and `h = a g` at `x`,
as for `g_{c s} = φ(s) g₀` with `a = φ'(t) / φ(t)`, then the derivative at `t` of the scalar
curvature at `x` is `-a Scal`. -/
theorem hasDerivAt_scalarCurvature_of_variation_eq_mul_inner
    (hc : ContMDiffAt 𝓘(ℝ) IP 2 c t)
    {r : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    (hr : ∀ᶠ s in 𝓝 t, g.metric (c s) = (r s).toNondegenerateMetric)
    (hg : ∀ y (u v : TangentSpace I y), g (c t, y) u v = inner ℝ u v) {x : M}
    (hh : ∀ᶠ y in 𝓝 x, (CovariantDerivative.leviCivitaConnection I M).derivBilinearTensor
      (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1)) y = 0) {a : ℝ}
    (hx : ∀ u v : TangentSpace I x,
      g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) x u v = a * inner ℝ u v) :
    HasDerivAt (fun s ↦ (r s).scalarCurvature x) (-a * (r t).scalarCurvature x) t := by
  refine (g.hasDerivAt_scalarCurvature_of_derivBilinearTensor_eq_zero hc hr hg hh).congr_deriv ?_
  have hrt := hr.self_of_nhds
  have hvar : g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) x = a • g.metric (c t) x := by
    ext u v
    rw [hx, smul_apply, smul_apply, smul_eq_mul, metric_apply, hg]
  have hLC : (r t).toNondegenerateMetric.IsLeviCivitaConnection
      (CovariantDerivative.leviCivitaConnection I M) :=
    hrt ▸ g.isLeviCivitaConnection_leviCivitaConnection_of_apply_eq_inner hg
  -- The metric and the raised Ricci tensor, read on the model space.
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.metric (c t) x
  let T : E →L[ℝ] E := G.inverse ∘L
    ((CovariantDerivative.leviCivitaConnection I M).ricciTensor x).toContinuousBilinearMap
  have hinv : G.IsInvertible := (g.metric (c t)).isInvertible x
  have key : -traceCLM ℝ E ((G.inverse ∘L (a • G)) ∘L T) = -a * traceCLM ℝ E T := by
    rw [ContinuousLinearMap.comp_smul, hinv.inverse_comp_self, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.id_comp, map_smul, smul_eq_mul, neg_mul]
  rw [(r t).scalarCurvature_eq_trace_inverse_ricciTensor _ hLC, ← hrt, hvar]
  exact key

end TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

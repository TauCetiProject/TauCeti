/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar.Trace
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.RicciVariation
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Trace
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor.Trace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor.SMul
import TauCeti.Topology.Algebra.Module.BilinearForm
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchi

/-!
# Scalar curvature evolution under Ricci flow

For a smooth family of nondegenerate metrics which are positive, let `∇ˢ` be native smooth
Levi-Civita connections and suppose the metric velocity at `t` is `-2 Ric`. This file derives

`∂ₜ R = ΔR + 2|Ric|²`

for the existing `Bundle.ContMDiffRiemannianMetric.scalarCurvature` and native scalar
Laplace–Beltrami operator. The reaction is first expressed intrinsically as the trace of the
square of Ricci with one index raised, then as a coefficient-square sum in any orthonormal basis.

The proof uses native metric and Levi-Civita variation, the Palatini identity and contracted
Bianchi. The metric trace of the connection velocity vanishes; its ordinary trace is `-dR`.
Differentiating those traces yields the scalar Laplacian. The moving inverse metric supplies
the quadratic reaction. The Ricci-flow equation is needed at `t` for all spatial points.

## References

* P. Topping, *Lectures on the Ricci Flow*, CUP (2006), Proposition 2.5.4, equation (2.5.5), p.42.
* [Poincaré Conjecture](https://github.com/frenzymath/PoincareConjecture).
* [Lean evaluation submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public section

open Bundle FiberBundle CovariantDerivative
open scoped ContDiff Manifold Topology RealInnerProductSpace

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
  {C : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x}
  (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov)
  (ht : cov.torsion = 0)

variable
  (hC : ∀ x u v w, inner ℝ (C x u v) w =
    -cov.derivRicciTensor x u w v - cov.derivRicciTensor x v w u +
      cov.derivRicciTensor x v u w)

include hcov ht hC

/-- The first contraction of the Ricci-flow connection velocity vanishes by twice
contracted Bianchi. This is the pointwise vector form of `tr C = 0`. -/
private theorem sum_C_self_eq_zero (x : M) :
    ∑ i, C x (stdOrthonormalBasis ℝ (TangentSpace I x) i)
      (stdOrthonormalBasis ℝ (TangentSpace I x) i) = 0 := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  let q : TangentSpace I x := ∑ i, C x (b i) (b i)
  have hinner (z : TangentSpace I x) : inner ℝ q z = 0 := by
    simp only [q, sum_inner]
    simp_rw [hC]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_neg_distrib]
    have hdiv := hcov.two_mul_sum_derivRicciTensor_eq_mvfderiv_scalarCurvature ht x b z
    have htr := hcov.sum_derivRicciTensor_self_eq_mvfderiv_scalarCurvature x b z
    linarith
  have hq : inner ℝ q q = 0 := hinner q
  exact inner_self_eq_zero.mp hq

/-- The endomorphism trace of the Ricci-flow connection velocity is minus the
scalar-curvature differential. -/
private theorem trace_C_eq_neg_mvfderiv_scalarCurvature (x : M)
    (u : TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x) (C x u).toLinearMap =
      -mvfderiv I cov.scalarCurvature x u := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [LinearMap.trace_eq_sum_inner _ b]
  -- Expand the endomorphism trace in the fixed orthonormal basis.
  change (∑ i, inner ℝ (b i) (C x u (b i))) = _
  have hp (i) : inner ℝ (b i) (C x u (b i)) =
      -cov.derivRicciTensor x (b i) (b i) u := by
    rw [real_inner_comm, hC]
    have hs := congrArg (fun L ↦ L (b i))
      (hcov.derivRicciTensor_comm ht x u (b i))
    rw [hs]
    ring
  simp_rw [hp]
  rw [Finset.sum_neg_distrib,
    hcov.sum_derivRicciTensor_self_eq_mvfderiv_scalarCurvature x b u]

end TauCeti.Manifold

namespace TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (g : ContMDiffNondegenerateMetricFamily I M 𝓘(ℝ) ℝ)
  {cov : ℝ → CovariantDerivative I E (TangentSpace I : M → Type _)} {t : ℝ}
  [∀ s, CovariantDerivative.ContMDiffCovariantDerivative (cov s) ∞]

/-- The native first metric variation is `-2 Ric` when the metric evaluations satisfy
Ricci flow at the time under consideration. -/
private theorem variation_eq_neg_two_ricciTensor
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t) :
    g.variation t 1 = (-2 : ℝ) • fun y ↦ (cov t).ricciTensor y |>.toContinuousBilinearMap := by
  funext y
  ext u v
  have hn := g.hasDerivAt_apply_apply_comp (c := id) (t := t) mdifferentiableAt_id y u v
  simpa using hn.unique (hflow y u v)

/-- The actual Levi-Civita connection velocity under Ricci flow is given by the three
covariant derivatives of Ricci in the Koszul variation formula. -/
private theorem apply_deriv_difference_eq_neg_derivRicciTensor
    (hcov : ∀ s, (g.metric s).IsLeviCivitaConnection (cov s))
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t)
    (y : M) (u v w : TangentSpace I y) :
    g (t, y) (deriv (fun s ↦ (cov s).difference (cov t) y) t u v) w =
      -(cov t).derivRicciTensor y u w v - (cov t).derivRicciTensor y v w u +
        (cov t).derivRicciTensor y v u w := by
  have hh := g.variation_eq_neg_two_ricciTensor hflow
  have heq := g.two_mul_apply_deriv_difference_eq_derivBilinearTensor
    (c := id) (t := t) contMDiffAt_id hcov y u v w
  simp only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq] at heq
  rw [hh] at heq
  have hs (a b c : TangentSpace I y) :=
    (cov t).derivBilinearTensor_const_smul
      (b := fun z ↦ ((cov t).ricciTensor z).toContinuousBilinearMap) (x := y)
      (-2) a b c
  rw [hs, hs, hs] at heq
  rw [← CovariantDerivative.derivRicciTensor_def] at heq
  linarith

end TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

namespace TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (g : ContMDiffNondegenerateMetricFamily I M 𝓘(ℝ) ℝ)
  {cov : ℝ → CovariantDerivative I E (TangentSpace I : M → Type _)} {t : ℝ}
  [∀ s, CovariantDerivative.ContMDiffCovariantDerivative (cov s) ∞]

/-- The native Palatini double contraction is the scalar Laplacian under Ricci flow. -/
private theorem palatini_deriv_difference_eq_laplaceBeltrami
    (hcov : ∀ s, (g.metric s).IsLeviCivitaConnection (cov s))
    (hg : ∀ y (u v : TangentSpace I y), g (t, y) u v = inner ℝ u v)
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t)
    (x : M) :
    let e := stdOrthonormalBasis ℝ (TangentSpace I x)
    let C := fun y ↦ deriv (fun s ↦ (cov s).difference (cov t) y) t
    ∑ j, ∑ i, inner ℝ (e i)
      ((cov t).hom ((cov t).hom (cov t)) C x (e i) (e j) (e j) -
        (cov t).hom ((cov t).hom (cov t)) C x (e j) (e j) (e i)) =
      laplaceBeltrami I (cov t).scalarCurvature x := by
  let C : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y :=
    fun y ↦ deriv (fun s ↦ (cov s).difference (cov t) y) t
  have hC := g.contMDiff_deriv_difference_of_isLeviCivitaConnection
    (c := id) (t := t) contMDiffAt_id hcov
  have hLC := ((g.metric t).isLeviCivitaConnection_iff_of_apply_eq_inner
      (fun y u v ↦ by simpa only [metric_apply] using hg y u v)).mp (hcov t)
  have hpair (y : M) (u v w : TangentSpace I y) :
      inner ℝ (C y u v) w = -(cov t).derivRicciTensor y u w v -
        (cov t).derivRicciTensor y v w u + (cov t).derivRicciTensor y v u w := by
    rw [← hg]
    exact g.apply_deriv_difference_eq_neg_derivRicciTensor hcov hflow y u v w
  have hcanonical : ∀ ⦃U : Π y : M, TangentSpace I y⦄, MDiffAt (T% U) x →
      ∀ z : TangentSpace I x, cov t U x z = leviCivitaConnection I M U x z := by
    intro U hU z
    exact (hcov t).uniqueness
      (((g.metric t).isLeviCivitaConnection_iff_of_apply_eq_inner
      (fun y u v ↦ by simpa only [metric_apply] using hg y u v)).mpr
        (isLeviCivitaConnection_leviCivitaConnection I)) hU z
  exact sum_palatini_eq_laplaceBeltrami hLC.isMetricCompatible hcanonical
    (hC.mdifferentiableAt (by simp))
    (((cov t).contMDiff_scalarCurvature x).of_le (by simp))
    (Filter.Eventually.of_forall (sum_C_self_eq_zero hLC.isMetricCompatible hLC.torsion hpair))
    (Filter.Eventually.of_forall
      (trace_C_eq_neg_mvfderiv_scalarCurvature hLC.isMetricCompatible hLC.torsion hpair))

/-- The inverse-metric trace of the actual Ricci derivative is the scalar Laplacian. -/
private theorem traceCLM_inverse_deriv_ricciTensor_eq_laplaceBeltrami
    (hcov : ∀ s, (g.metric s).IsLeviCivitaConnection (cov s))
    (hg : ∀ y (u v : TangentSpace I y), g (t, y) u v = inner ℝ u v)
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t)
    (x : M) :
    traceCLM ℝ E ((g.metric t x).inverse ∘L
      deriv (fun s ↦ ((cov s).ricciTensor x).toContinuousBilinearMap) t) =
      laplaceBeltrami I (cov t).scalarCurvature x := by
  let e := stdOrthonormalBasis ℝ (TangentSpace I x)
  let C := fun y ↦ deriv (fun s ↦ (cov s).difference (cov t) y) t
  let B : ℝ → E →L[ℝ] E →L[ℝ] ℝ :=
    fun s ↦ ((cov s).ricciTensor x).toContinuousBilinearMap
  let Kx : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := deriv B t
  have hB : HasDerivAt (F := E →L[ℝ] E →L[ℝ] ℝ) B (deriv B t) t := by
    apply DifferentiableAt.hasDerivAt (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
    exact differentiableAt_clm_apply₂.mpr fun u v ↦
      (g.hasDerivAt_ricciTensor_of_isLeviCivitaConnection
        (c := id) (t := t) contMDiffAt_id hcov x u v).differentiableAt
  have hK (u v : TangentSpace I x) := (hasDerivAt_clm_apply₂.mp hB u v).unique
    (g.hasDerivAt_ricciTensor_of_isLeviCivitaConnection
      (c := id) (t := t) contMDiffAt_id hcov x u v)
  calc
    -- The tangent fibre and model give the same fixed-space contraction.
    _ = traceCLM ℝ (TangentSpace I x) ((g.metric t x).inverse ∘L Kx) := rfl
    _ = LinearMap.BilinMap.metricTrace Kx.toBilinForm :=
      ContinuousLinearMap.traceCLM_inverse_comp_eq_metricTrace (g.metric t x)
        (fun u v ↦ by simpa only [metric_apply] using hg x u v) Kx
    _ = ∑ j, Kx (e j) (e j) := LinearMap.BilinMap.metricTrace_eq_sum _ e
    _ = ∑ j, ∑ i, inner ℝ (e i)
        ((cov t).hom ((cov t).hom (cov t)) C x (e i) (e j) (e j) -
          (cov t).hom ((cov t).hom (cov t)) C x (e j) (e j) (e i)) := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hdiag : Kx (e j) (e j) = _ := hK (e j) (e j)
      rw [hdiag,
        LinearMap.trace_eq_sum_inner _ e, LinearMap.trace_eq_sum_inner _ e]
      rw [← Finset.sum_sub_distrib]
      simp only [inner_sub_right]
      rfl
    _ = _ := g.palatini_deriv_difference_eq_laplaceBeltrami hcov hg hflow x

end TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

namespace TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (g : ContMDiffNondegenerateMetricFamily I M 𝓘(ℝ) ℝ)
  {cov : ℝ → CovariantDerivative I E (TangentSpace I : M → Type _)} {t : ℝ}
  [∀ s, CovariantDerivative.ContMDiffCovariantDerivative (cov s) ∞]

/-- Differentiating the actual inverse-metric Ricci trace gives the scalar Laplacian
and twice the trace of the square of Ricci with one index raised. -/
private theorem hasDerivAt_trace_ricciTensor_of_ricciFlow
    (hcov : ∀ s, (g.metric s).IsLeviCivitaConnection (cov s))
    (hg : ∀ y (u v : TangentSpace I y), g (t, y) u v = inner ℝ u v)
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t)
    (x : M) :
    HasDerivAt (fun s ↦ traceCLM ℝ E
      ((g.metric s x).inverse ∘L ((cov s).ricciTensor x).toContinuousBilinearMap))
      (laplaceBeltrami I (cov t).scalarCurvature x + 2 * traceCLM ℝ E
        (((g.metric t x).inverse ∘L ((cov t).ricciTensor x).toContinuousBilinearMap) ∘L
          ((g.metric t x).inverse ∘L ((cov t).ricciTensor x).toContinuousBilinearMap))) t := by
  let B : ℝ → E →L[ℝ] E →L[ℝ] ℝ :=
    fun s ↦ ((cov s).ricciTensor x).toContinuousBilinearMap
  let K : E →L[ℝ] E →L[ℝ] ℝ := deriv B t
  let A : (E →L[ℝ] ℝ) →L[ℝ] E := (g.metric t x).inverse
  have hB : HasDerivAt (F := E →L[ℝ] E →L[ℝ] ℝ) B (deriv B t) t := by
    apply DifferentiableAt.hasDerivAt (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
    exact differentiableAt_clm_apply₂.mpr fun u v ↦
      (g.hasDerivAt_ricciTensor_of_isLeviCivitaConnection
        (c := id) (t := t) contMDiffAt_id hcov x u v).differentiableAt
  have htr : traceCLM ℝ E (A ∘L K) = laplaceBeltrami I (cov t).scalarCurvature x :=
    g.traceCLM_inverse_deriv_ricciTensor_eq_laplaceBeltrami hcov hg hflow x
  have hcomp : ((A ∘L (((-2 : ℝ) • B t) ∘L A)) ∘L B t) =
      (-2 : ℝ) • ((A ∘L B t) ∘L (A ∘L B t)) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul]
  have hd := ContMDiffNondegenerateMetric.hasDerivAt_trace_inverse_comp
    (g := g.metric) (x := x) (B := B) (h := (-2 : ℝ) • B t) (K := K)
    (fun u v ↦ by
      have hm : HasDerivAt (fun s ↦ g.metric s x u v)
          (-2 * (cov t).ricciTensor x u v) t := by
        simpa only [metric_apply] using hflow x u v
      refine hm.congr_deriv ?_
      -- Evaluate the scaled form on model vectors before identifying the native Ricci value.
      change -2 * (cov t).ricciTensor x u v = -2 * B t u v
      exact congrArg (fun z : ℝ ↦ -2 * z)
        (LinearMap.toContinuousBilinearMap_apply ((cov t).ricciTensor x) u v).symm)
    (hasDerivAt_clm_apply₂.mp hB)
  refine hd.congr_deriv ?_
  -- Every fixed-fibre operation is read on the model before rewriting the compositions.
  change traceCLM ℝ E (A ∘L K) -
    traceCLM ℝ E ((A ∘L (((-2 : ℝ) • B t) ∘L A)) ∘L B t) =
      laplaceBeltrami I (cov t).scalarCurvature x +
        2 * traceCLM ℝ E ((A ∘L B t) ∘L (A ∘L B t))
  rw [htr, hcomp, map_smul, smul_eq_mul]
  ring

/-- **Scalar curvature evolution under Ricci flow.** For a smooth family of native metrics
with metric velocity `-2 Ric` at `t`, the existing scalar curvature has derivative
`ΔR + 2 tr((Ric♯)²)`. The installed fibre inner product is the metric at `t`.
The following orthonormal-basis formula identifies the reaction trace with `|Ric|²`. -/
theorem hasDerivAt_scalarCurvature_of_ricciFlow
    (r : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hr : ∀ s, g.metric s = (r s).toNondegenerateMetric)
    (hcov : ∀ s, (g.metric s).IsLeviCivitaConnection (cov s))
    (hg : ∀ y (u v : TangentSpace I y), g (t, y) u v = inner ℝ u v)
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t)
    (x : M) :
    HasDerivAt (fun s ↦ (r s).scalarCurvature x)
      (laplaceBeltrami I (r t).scalarCurvature x + 2 * traceCLM ℝ E
        (((g.metric t x).inverse ∘L ((cov t).ricciTensor x).toContinuousBilinearMap) ∘L
          ((g.metric t x).inverse ∘L ((cov t).ricciTensor x).toContinuousBilinearMap))) t := by
  have hscalar (s : ℝ) (y : M) : (r s).scalarCurvature y = traceCLM ℝ E
      ((g.metric s y).inverse ∘L ((cov s).ricciTensor y).toContinuousBilinearMap) := by
    have hrcov : (r s).toNondegenerateMetric.IsLeviCivitaConnection (cov s) := by
      rw [← hr s]
      exact hcov s
    rw [(r s).scalarCurvature_eq_trace_inverse_ricciTensor (cov s) hrcov y, hr s]
  have hcurv : (r t).scalarCurvature = (cov t).scalarCurvature := by
    funext y
    rw [hscalar]
    -- Trace is independent of reading the fixed tangent fibre as its model space.
    change traceCLM ℝ (TangentSpace I y)
      ((g.metric t y).inverse ∘L ((cov t).ricciTensor y).toContinuousBilinearMap) = _
    rw [ContinuousLinearMap.traceCLM_inverse_comp_eq_metricTrace (g.metric t y)
      (fun u v ↦ by simpa only [metric_apply] using hg y u v),
      LinearMap.BilinForm.toBilinForm_toContinuousBilinearMap,
      CovariantDerivative.scalarCurvature_apply]
  have hd := g.hasDerivAt_trace_ricciTensor_of_ricciFlow hcov hg hflow x
  rw [← hcurv] at hd
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s ↦ hscalar s x)

/-- **Scalar curvature evolution in any orthonormal basis.** Under the Ricci-flow metric
equation at `t`, the derivative of the actual scalar curvature is `ΔR + 2|Ric|²`,
where `|Ric|² = ∑ i j, Ric(bᵢ,bⱼ)²` in any orthonormal basis of the metric at `t`. -/
theorem hasDerivAt_scalarCurvature_sum_of_ricciFlow
    (r : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hr : ∀ s, g.metric s = (r s).toNondegenerateMetric)
    (hcov : ∀ s, (g.metric s).IsLeviCivitaConnection (cov s))
    (hg : ∀ y (u v : TangentSpace I y), g (t, y) u v = inner ℝ u v)
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t)
    (x : M) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    HasDerivAt (fun s ↦ (r s).scalarCurvature x)
      (laplaceBeltrami I (r t).scalarCurvature x +
        2 * ∑ i, ∑ j, ((cov t).ricciTensor x (b i) (b j)) ^ 2) t := by
  have hLC := ((g.metric t).isLeviCivitaConnection_iff_of_apply_eq_inner
      (fun y u v ↦ by simpa only [metric_apply] using hg y u v)).mp (hcov t)
  have hsq := ContinuousLinearMap.traceCLM_inverse_comp_self_eq_sum_sq (g.metric t x)
        (fun u v ↦ by simpa only [metric_apply] using hg x u v)
    ((cov t).ricciTensor x).toContinuousBilinearMap
    (fun u v ↦ CovariantDerivative.IsMetricCompatible.ricciTensor_comm (cov := cov t)
      hLC.isMetricCompatible hLC.torsion x u v) b
  have hd := g.hasDerivAt_scalarCurvature_of_ricciFlow r hr hcov hg hflow x
  refine hd.congr_deriv ?_
  exact congrArg (fun z ↦ laplaceBeltrami I (r t).scalarCurvature x + 2 * z) hsq

end TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.ScalarVariation
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchi
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Scalar curvature evolution under Ricci flow

For a smooth family of nondegenerate metrics which are positive, let `∇ˢ` be native smooth
Levi-Civita connections and suppose the metric velocity at `t` is `-2 Ric`. This file derives

`∂ₜ R = ΔR + 2|Ric|²`

for the existing `Bundle.ContMDiffRiemannianMetric.scalarCurvature` and native scalar
Laplace–Beltrami operator. The reaction is first expressed intrinsically as the trace of the
square of Ricci with one index raised, then as a coefficient-square sum in any orthonormal basis.

The proof specializes the first variation of scalar curvature
`∂ₜ R = div (div h) - Δ (tr_g h) - ⟨h, Ric⟩`
(`TauCeti.Manifold.ContMDiffNondegenerateMetricFamily.hasDerivAt_scalarCurvature`) to `h = -2 Ric`.
By contracted Bianchi `div (div h) = -ΔR`, and `-Δ (tr_g h) = 2ΔR`; the pairing with Ricci supplies
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

namespace TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (g : ContMDiffNondegenerateMetricFamily I M 𝓘(ℝ) ℝ)
  {cov : ℝ → CovariantDerivative I E (TangentSpace I : M → Type _)} {t : ℝ}
  [∀ s, CovariantDerivative.ContMDiffCovariantDerivative (cov s) ∞]

/-- For the metric velocity `h = -2 Ric`, contracted Bianchi gives `div (div h) = -Δ Scal`. -/
private theorem divergence_rieszDual_divBilinearTensor_neg_two_ricciTensor (x : M) :
    divergence I (fun y ↦ Riemannian.Tensor.rieszDual y
      ((leviCivitaConnection I M).divBilinearTensor ((-2 : ℝ) • fun z ↦
        ((leviCivitaConnection I M).ricciTensor z).toContinuousBilinearMap) y)) x =
      -laplaceBeltrami I (leviCivitaConnection I M).scalarCurvature x := by
  have hLC := isLeviCivitaConnection_leviCivitaConnection (M := M) I
  have hS : ContMDiff I 𝓘(ℝ) 2 (leviCivitaConnection I M).scalarCurvature :=
    (leviCivitaConnection I M).contMDiff_scalarCurvature.of_le (by simp)
  have hfield : (fun y ↦ Riemannian.Tensor.rieszDual y
      ((leviCivitaConnection I M).divBilinearTensor ((-2 : ℝ) • fun z ↦
        ((leviCivitaConnection I M).ricciTensor z).toContinuousBilinearMap) y)) =
      mgradient I ((-1 : ℝ) • (leviCivitaConnection I M).scalarCurvature) := by
    funext y
    rw [mgradient_smul, Pi.smul_apply, mgradient_def,
      ← hLC.isMetricCompatible.two_smul_divBilinearTensor_ricciTensor_eq_mvfderiv_scalarCurvature
        hLC.torsion y,
      ← map_smul, divBilinearTensor_const_smul, smul_smul]
    norm_num
  rw [hfield, ← laplaceBeltrami_def, laplaceBeltrami_smul I _ hS, neg_one_mul]

/-- For the metric velocity `h = -2 Ric`, `Δ (tr_g h) = -2 Δ Scal`. -/
private theorem laplaceBeltrami_metricTrace_neg_two_ricciTensor (x : M) :
    laplaceBeltrami I (fun y ↦ LinearMap.BilinMap.metricTrace (ContinuousLinearMap.toLinearMap₁₂
      (((-2 : ℝ) • fun z ↦
        ((leviCivitaConnection I M).ricciTensor z).toContinuousBilinearMap) y))) x =
      -2 * laplaceBeltrami I (leviCivitaConnection I M).scalarCurvature x := by
  have hS : ContMDiff I 𝓘(ℝ) 2 (leviCivitaConnection I M).scalarCurvature :=
    (leviCivitaConnection I M).contMDiff_scalarCurvature.of_le (by simp)
  rw [← laplaceBeltrami_smul I _ hS]
  congr 1
  funext y
  let e := stdOrthonormalBasis ℝ (TangentSpace I y)
  rw [LinearMap.BilinMap.metricTrace_eq_sum _ e, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    (leviCivitaConnection I M).scalarCurvature_eq_sum y e, Finset.mul_sum]
  simp

/-- The first metric variation is `-2 Ric` when the metric evaluations satisfy Ricci flow at the
time under consideration. -/
private theorem variation_eq_neg_two_ricciTensor
    (hcov : (g.metric t).IsLeviCivitaConnection (cov t))
    (hg : ∀ y (u v : TangentSpace I y), g (t, y) u v = inner ℝ u v)
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t) :
    g.variation t 1 = (-2 : ℝ) • fun y ↦
      ((leviCivitaConnection I M).ricciTensor y).toContinuousBilinearMap := by
  funext y
  ext u v
  have hn := (g.hasDerivAt_apply_apply_comp (c := id) (t := t) mdifferentiableAt_id y u v).unique
    (hflow y u v)
  rw [hcov.ricciTensor_eq_ricciTensor_leviCivitaConnection
    (fun y u v ↦ by simpa only [metric_apply] using hg y u v) y] at hn
  simpa using hn

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
  have hd := g.hasDerivAt_scalarCurvature (c := id) (t := t) contMDiffAt_id (.of_forall hr) hg x
  simp only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq,
    g.variation_eq_neg_two_ricciTensor (hcov t) hg hflow] at hd
  rw [divergence_rieszDual_divBilinearTensor_neg_two_ricciTensor,
    laplaceBeltrami_metricTrace_neg_two_ricciTensor] at hd
  have hLC : (r t).toNondegenerateMetric.IsLeviCivitaConnection (leviCivitaConnection I M) :=
    hr t ▸ g.isLeviCivitaConnection_leviCivitaConnection_of_apply_eq_inner hg
  have hscal : (r t).scalarCurvature = (leviCivitaConnection I M).scalarCurvature := by
    funext y
    rw [(r t).scalarCurvature_eq_trace_inverse_ricciTensor _ hLC, ← hr t]
    -- Trace is independent of reading the fixed tangent fibre as its model space.
    change traceCLM ℝ (TangentSpace I y) ((g.metric t y).inverse ∘L
      ((leviCivitaConnection I M).ricciTensor y).toContinuousBilinearMap) = _
    rw [ContinuousLinearMap.traceCLM_inverse_comp_eq_metricTrace (g.metric t y)
      (fun u v ↦ by simpa only [metric_apply] using hg y u v),
      LinearMap.BilinForm.toBilinForm_toContinuousBilinearMap, scalarCurvature_apply]
  -- The inverse metric and the Ricci tensor, read on the model space.
  let A : (E →L[ℝ] ℝ) →L[ℝ] E := (g.metric t x).inverse
  let Ric : E →L[ℝ] E →L[ℝ] ℝ :=
    ((leviCivitaConnection I M).ricciTensor x).toContinuousBilinearMap
  have htr : traceCLM ℝ E ((A ∘L ((-2 : ℝ) • Ric)) ∘L (A ∘L Ric)) =
      -2 * traceCLM ℝ E ((A ∘L Ric) ∘L (A ∘L Ric)) := by
    rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, map_smul, smul_eq_mul]
  rw [(hcov t).ricciTensor_eq_ricciTensor_leviCivitaConnection
    (fun y u v ↦ by simpa only [metric_apply] using hg y u v) x, hscal]
  have harith (L T : ℝ) : -L - -2 * L - -2 * T = L + 2 * T := by ring
  exact hd.congr_deriv ((congrArg (_ - ·) htr).trans (harith _ _))

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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci.SecondDerivative
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci.Contraction
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Family
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Basic
public import TauCeti.Geometry.RicciFlow.ConnectionVariation
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Family
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.RicciVariation
import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Trace
import TauCeti.Analysis.InnerProductSpace.Trace.Inverse
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# The Ricci tensor evolution equation

For a smooth family of native metrics with velocity `-2 Ric`, this file derives the
fixed-input Ricci evolution equation from metric and connection variation and contracted
Bianchi. The heat term is the negative of the native positive rough Laplacian on covariant
bilinear forms. The reaction is the curvature–Ricci contraction minus the square of Ricci.

All time derivatives are derivatives of the native metric and curvature tensors. No tensor
evolution equation or curvature-reaction service is assumed.

## References

* P. Topping, *Lectures on the Ricci Flow*, CUP (2006), Proposition 2.5.4.
* [Poincaré Conjecture](https://github.com/frenzymath/PoincareConjecture).
* [Lean evaluation submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public noncomputable section

open Bundle FiberBundle CovariantDerivative
open scoped ContDiff Manifold Topology RealInnerProductSpace

namespace TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (g : ContMDiffNondegenerateMetricFamily I M 𝓘(ℝ) ℝ)
  {cov : ℝ → CovariantDerivative I E (TangentSpace I : M → Type _)} {t : ℝ}
  [∀ s, CovariantDerivative.ContMDiffCovariantDerivative (cov s) ∞]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The pointwise Ricci-flow equation is the metric derivative in fixed model coordinates. -/
private theorem hasDerivAt_metric_apply_of_ricciFlow
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t)
    (x : M) (a b : E) :
    HasDerivAt (fun s ↦ g.metric s x a b)
      (((-2 : ℝ) • ((cov t).ricciTensor x).toContinuousBilinearMap) a b) t := by
  have hm : HasDerivAt (fun s ↦ g.metric s x a b)
      (-2 * (cov t).ricciTensor x a b) t := by
    simpa only [metric_apply] using hflow x a b
  refine hm.congr_deriv ?_
  -- The scaled form uses the model norm; its evaluations agree with the tangent form.
  change -2 * (cov t).ricciTensor x a b =
    -2 * ((cov t).ricciTensor x).toContinuousBilinearMap a b
  exact congrArg (fun q : ℝ ↦ -2 * q)
    (LinearMap.toContinuousBilinearMap_apply ((cov t).ricciTensor x) a b).symm

/-- The spatial derivative of the actual Ricci-flow connection velocity is the
corresponding combination of native second Ricci derivatives. -/
private theorem inner_hom_deriv_difference_of_ricciFlow
    (hcov : ∀ s, (g.metric s).IsLeviCivitaConnection (cov s))
    (hg : ∀ y (u v : TangentSpace I y), g (t, y) u v = inner ℝ u v)
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t)
    (x : M) (a u v w : TangentSpace I x) :
    let B := fun y ↦ ((cov t).ricciTensor y).toContinuousBilinearMap
    let H := (cov t).bilinear.secondCovariantDerivative (cov t) B x
    let C := fun y ↦ deriv (fun s ↦ (cov s).difference (cov t) y) t
    inner ℝ ((cov t).hom ((cov t).hom (cov t)) C x a u v) w =
      -H a v u w - H a u v w + H a w v u := by
  let B := fun y ↦ ((cov t).ricciTensor y).toContinuousBilinearMap
  let C := fun y ↦ deriv (fun s ↦ (cov s).difference (cov t) y) t
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) y (B y)) :=
    (cov t).contMDiff_ricciTensor
  have hC := g.contMDiff_deriv_difference_of_isLeviCivitaConnection
    (c := id) (t := t) contMDiffAt_id hcov
  have hLC := g.isLeviCivitaConnection_of_apply_eq_inner (hcov t) hg
  have hKB (y : M) (a b c : TangentSpace I y) :
      (cov t).bilinear B y c a b = (cov t).derivRicciTensor y a b c :=
    (cov t).bilinear_ricciTensor_apply (hB.mdifferentiableAt (by simp)) c a b
  have hpair (y : M) (a b c : TangentSpace I y) :
      inner ℝ (C y a b) c = -(cov t).bilinear B y b a c -
        (cov t).bilinear B y a b c + (cov t).bilinear B y c a b := by
    rw [← hg]
    rw [g.apply_deriv_difference_eq_neg_derivRicciTensor hcov hflow]
    simp_rw [hKB]
    rw [hLC.isMetricCompatible.derivRicciTensor_comm hLC.torsion y b a]
  have hh := hLC.isMetricCompatible.inner_hom_hom_eq_secondCovariantDerivative_bilinear
    hB hC hpair x a u v w
  rw [hLC.isMetricCompatible.secondCovariantDerivative_ricciTensor_comm
    hLC.torsion x a w u v] at hh
  exact hh

/-- The actual metric-lowered curvature tensor under Ricci flow has the six second Ricci
derivatives of the connection-variation formula and the correction from the moving metric.
The four tangent inputs are fixed in time. -/
theorem hasDerivAt_apply_curvatureTensor_of_ricciFlow
    (hcov : ∀ s, (g.metric s).IsLeviCivitaConnection (cov s))
    (hg : ∀ y (u v : TangentSpace I y), g (t, y) u v = inner ℝ u v)
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t)
    (x : M) (u v w z : TangentSpace I x) :
    let B := fun y ↦ ((cov t).ricciTensor y).toContinuousBilinearMap
    let H := (cov t).bilinear.secondCovariantDerivative (cov t) B x
    HasDerivAt (fun s ↦ g (s, x) ((cov s).curvatureTensor x u v w) z)
      (-2 * (cov t).ricciTensor x ((cov t).curvatureTensor x u v w) z -
        H u v w z - H u w v z + H u z v w +
          H v u w z + H v w u z - H v z u w) t := by
  let B := fun y ↦ ((cov t).ricciTensor y).toContinuousBilinearMap
  let C := fun y ↦ deriv (fun s ↦ (cov s).difference (cov t) y) t
  have hDu := g.inner_hom_deriv_difference_of_ricciFlow hcov hg hflow x u w v z
  have hDv := g.inner_hom_deriv_difference_of_ricciFlow hcov hg hflow x v w u z
  have hBR (a b : TangentSpace I x) : B x a b = (cov t).ricciTensor x a b :=
    LinearMap.toContinuousBilinearMap_apply _ a b
  have hR := g.hasDerivAt_curvatureTensor_of_isLeviCivitaConnection
    (c := id) (t := t) contMDiffAt_id hcov x u v w
  have hG : HasDerivAt (fun s ↦ g (s, x)) ((-2 : ℝ) • B x) t := by
    apply hasDerivAt_clm_apply₂.mpr
    have h := g.hasDerivAt_metric_apply_of_ricciFlow hflow x
    simp only [metric_apply] at h
    convert! h using 1
  let G : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦ g (s, x)
  let X : ℝ → E := fun s ↦ (cov s).curvatureTensor x u v w
  let dX : E := (cov t).hom ((cov t).hom (cov t)) C x u w v -
    (cov t).hom ((cov t).hom (cov t)) C x v w u
  have hX : HasDerivAt X dX t := hR
  let R : E →L[ℝ] E →L[ℝ] ℝ := B x
  let dG : E →L[ℝ] E →L[ℝ] ℝ := (-2 : ℝ) • R
  have hG' : HasDerivAt G dG t := hG
  have hdG (a b : E) : dG a b = -2 * R a b := by
    simp only [dG, smul_apply, smul_eq_mul]
  let zE : E := z
  have hd := (hG'.clm_apply hX).clm_apply (hasDerivAt_const t zE)
  refine hd.congr_deriv ?_
  -- Normalize the fixed-space bilinear product before comparing the metric at `t`
  -- with the Riemannian fibre metric; their norm instances do not coincide syntactically.
  simp only [add_apply, map_zero, add_zero]
  rw [hdG]
  have hRX : R (X t) zE = (cov t).ricciTensor x (X t) z := hBR (X t) z
  rw [hRX]
  have hmetric : G t dX zE = @inner ℝ (TangentSpace I x) _ dX z := hg x dX z
  rw [hmetric]
  dsimp only [X, dX]
  rw [inner_sub_left]
  linarith only [hDu, hDv]

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- A Riemannian presentation of one native metric slice gives symmetry of its actual Ricci.
The metric and Levi-Civita hypotheses are required only at this slice. -/
private theorem ricciTensor_comm_of_riemannianMetric
    (s : ℝ) (r : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hr : g.metric s = r.toNondegenerateMetric)
    (hcov : (g.metric s).IsLeviCivitaConnection (cov s))
    (x : M) (u v : TangentSpace I x) :
    (cov s).ricciTensor x u v = (cov s).ricciTensor x v u := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨r.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _) := inferInstance
  have hg := g.apply_eq_inner_of_riemannianMetric r hr
  have hLC := g.isLeviCivitaConnection_of_apply_eq_inner hcov hg
  exact IsMetricCompatible.ricciTensor_comm (cov := cov s)
    hLC.isMetricCompatible hLC.torsion x u v

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Ricci curvature is the inverse-metric contraction of the actual lowered curvature.
The equality also fixes the slot order used when differentiating this contraction. -/
private theorem ricciTensor_eq_trace_inverse_apply_curvatureTensor
    (s : ℝ) (r : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hr : g.metric s = r.toNondegenerateMetric)
    (hcov : (g.metric s).IsLeviCivitaConnection (cov s))
    (x : M) (u v : TangentSpace I x) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ a c : TangentSpace I x,
      B a c = g (s, x) ((cov s).curvatureTensor x u a c) v) :
    (cov s).ricciTensor x u v = traceCLM ℝ E ((g.metric s x).inverse ∘L B) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨r.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _) := inferInstance
  have hgs := g.apply_eq_inner_of_riemannianMetric r hr
  have hLC := g.isLeviCivitaConnection_of_apply_eq_inner hcov hgs
  let e := stdOrthonormalBasis ℝ (TangentSpace I x)
  let Bs : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := B
  have hBs (a c : TangentSpace I x) :
      Bs a c = g (s, x) ((cov s).curvatureTensor x u a c) v := hB a c
  suffices h : (cov s).ricciTensor x u v =
      traceCLM ℝ (TangentSpace I x) ((g.metric s x).inverse ∘L Bs) by
    exact h.trans (ContinuousLinearMap.traceCLM_model_eq_tangentSpace (I := I) _ x).symm
  rw [ContinuousLinearMap.traceCLM_inverse_comp_eq_metricTrace _
    (fun a c ↦ by simpa only [metric_apply] using hgs x a c),
    LinearMap.BilinMap.metricTrace_eq_sum _ e]
  exact (hLC.isMetricCompatible.sum_inner_curvatureTensor_self_eq_ricciTensor
    hLC.torsion x e u v).symm.trans
      (Finset.sum_congr rfl fun i _ ↦ by
        rw [← hgs, ← hBs]
        exact (ContinuousLinearMap.toBilinForm_apply Bs (e i) (e i)).symm)

/-- The mixed inverse-metric trace in Ricci variation is the curvature–Ricci contraction.
No derivative symmetry is used in this fixed-time algebraic identity. -/
private theorem trace_inverse_ricci_apply_curvatureTensor_eq_sum
    (hcov : (g.metric t).IsLeviCivitaConnection (cov t))
    (hg : ∀ y (a c : TangentSpace I y), g (t, y) a c = inner ℝ a c)
    (x : M) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (u v : TangentSpace I x) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ a c : TangentSpace I x,
      B a c = g (t, x) ((cov t).curvatureTensor x u a c) v) :
    traceCLM ℝ E (((g.metric t x).inverse ∘L
      ((cov t).ricciTensor x).toContinuousBilinearMap) ∘L ((g.metric t x).inverse ∘L B)) =
      ∑ i, ∑ j, (cov t).ricciTensor x (b i) (b j) *
        inner ℝ ((cov t).curvatureTensor x u (b i) (b j)) v := by
  let R : E →L[ℝ] E →L[ℝ] ℝ := ((cov t).ricciTensor x).toContinuousBilinearMap
  let A : (E →L[ℝ] ℝ) →L[ℝ] E := (g.metric t x).inverse
  have hLC := g.isLeviCivitaConnection_of_apply_eq_inner hcov hg
  have hmix : traceCLM ℝ E ((A ∘L R) ∘L (A ∘L B)) =
      ∑ i, ∑ j, B (b i) (b j) * R (b j) (b i) := by
    -- Trace uses only the underlying linear map; replacing the model norm by the
    -- installed tangent norm leaves that linear map unchanged.
    calc
      _ = traceCLM ℝ (TangentSpace I x)
          (((g.metric t x).inverse ∘L R) ∘L ((g.metric t x).inverse ∘L B)) :=
        ContinuousLinearMap.traceCLM_model_eq_tangentSpace (I := I) _ x
      _ = _ := ContinuousLinearMap.traceCLM_inverse_comp_inverse_comp_eq_sum_mul (g.metric t x)
        (fun a c ↦ by simpa only [metric_apply] using hg x a c) R (B) b
  have hcoeff : (∑ i, ∑ j, B (b i) (b j) * R (b j) (b i)) =
      ∑ i, ∑ j, (cov t).ricciTensor x (b i) (b j) *
        inner ℝ ((cov t).curvatureTensor x u (b i) (b j)) v := by
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    have hRij : R (b j) (b i) = (cov t).ricciTensor x (b j) (b i) :=
      by
        -- Ricci's continuous form uses the tangent norm, while `R` uses the fixed model norm.
        change ((cov t).ricciTensor x).toContinuousBilinearMap (b j) (b i) = _
        exact LinearMap.toContinuousBilinearMap_apply ((cov t).ricciTensor x) (b j) (b i)
    rw [hB, hg, hRij,
      IsMetricCompatible.ricciTensor_comm (cov := cov t)
        hLC.isMetricCompatible hLC.torsion x (b j) (b i)]
    exact mul_comm _ _
  exact hmix.trans hcoeff

/-- Differentiating the actual lowered curvature as a continuous bilinear form differentiates
Ricci by the native inverse-metric product rule. -/
private theorem hasDerivAt_ricciTensor_of_bilinear_apply_curvatureTensor
    (r : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hr : ∀ s, g.metric s = (r s).toNondegenerateMetric)
    (hcov : ∀ s, (g.metric s).IsLeviCivitaConnection (cov s))
    (hg : ∀ y (u v : TangentSpace I y), g (t, y) u v = inner ℝ u v)
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t)
    (x : M) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (u v : TangentSpace I x) (B : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (K : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ s (a c : TangentSpace I x),
      B s a c = g (s, x) ((cov s).curvatureTensor x u a c) v)
    (hK : HasDerivAt B K t) :
    HasDerivAt (fun s ↦ (cov s).ricciTensor x u v)
      ((∑ i, K (b i) (b i)) + 2 * ∑ i, ∑ j,
        (cov t).ricciTensor x (b i) (b j) *
          inner ℝ ((cov t).curvatureTensor x u (b i) (b j)) v) t := by
  have htrace (s : ℝ) : (cov s).ricciTensor x u v =
      traceCLM ℝ E ((g.metric s x).inverse ∘L B s) :=
    g.ricciTensor_eq_trace_inverse_apply_curvatureTensor s (r s) (hr s) (hcov s)
      x u v (B s) (hB s)
  let R : E →L[ℝ] E →L[ℝ] ℝ := ((cov t).ricciTensor x).toContinuousBilinearMap
  let A : (E →L[ℝ] ℝ) →L[ℝ] E := (g.metric t x).inverse
  let Kx : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := K
  have htr : traceCLM ℝ E (A ∘L K) = ∑ i, K (b i) (b i) := by
    -- Trace uses only the underlying linear map; replacing the model norm by the
    -- installed tangent norm leaves that linear map unchanged.
    calc
      _ = traceCLM ℝ (TangentSpace I x)
          ((g.metric t x).inverse ∘L Kx) :=
        ContinuousLinearMap.traceCLM_model_eq_tangentSpace (I := I) _ x
      _ = _ := by
        rw [ContinuousLinearMap.traceCLM_inverse_comp_eq_metricTrace (g.metric t x)
          (fun a c ↦ by simpa only [metric_apply] using hg x a c),
          LinearMap.BilinMap.metricTrace_eq_sum _ b]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        exact ContinuousLinearMap.toBilinForm_apply Kx (b i) (b i)
  have hmix : traceCLM ℝ E ((A ∘L R) ∘L (A ∘L B t)) =
      ∑ i, ∑ j, (cov t).ricciTensor x (b i) (b j) *
        inner ℝ ((cov t).curvatureTensor x u (b i) (b j)) v :=
    g.trace_inverse_ricci_apply_curvatureTensor_eq_sum (hcov t) hg x b u v (B t) (hB t)
  have hd := ContMDiffNondegenerateMetric.hasDerivAt_trace_inverse_comp
    (g := g.metric) (x := x) (B := B) (h := (-2 : ℝ) • R) (K := K)
    (g.hasDerivAt_metric_apply_of_ricciFlow hflow x)
    (hasDerivAt_clm_apply₂.mp hK)
  have hcomp : ((A ∘L (((-2 : ℝ) • R) ∘L A)) ∘L B t) =
      (-2 : ℝ) • ((A ∘L R) ∘L (A ∘L B t)) := by
    ext a
    simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul]
  refine (hd.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall htrace)
  -- The inverse-metric derivative uses the model norm. Read the fixed-fibre compositions
  -- with that same norm before applying the intrinsic contraction laws.
  change traceCLM ℝ E (A ∘L K) -
    traceCLM ℝ E ((A ∘L (((-2 : ℝ) • R) ∘L A)) ∘L B t) = _
  rw [hcomp, map_smul, smul_eq_mul, htr, hmix]
  ring

/-- Contracting derivatives of the actual lowered curvature differentiates native Ricci.
The inverse metric contributes twice the Ricci–curvature contraction. -/
private theorem hasDerivAt_ricciTensor_of_apply_curvatureTensor
    (r : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hr : ∀ s, g.metric s = (r s).toNondegenerateMetric)
    (hcov : ∀ s, (g.metric s).IsLeviCivitaConnection (cov s))
    (hg : ∀ y (u v : TangentSpace I y), g (t, y) u v = inner ℝ u v)
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t)
    (x : M) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (u v : TangentSpace I x) (K : TangentSpace I x → TangentSpace I x → ℝ)
    (hK : ∀ a c, HasDerivAt (fun s ↦ g (s, x) ((cov s).curvatureTensor x u a c) v)
      (K a c) t) :
    HasDerivAt (fun s ↦ (cov s).ricciTensor x u v)
      ((∑ i, K (b i) (b i)) + 2 * ∑ i, ∑ j,
        (cov t).ricciTensor x (b i) (b j) *
          inner ℝ ((cov t).curvatureTensor x u (b i) (b j)) v) t := by
  let B : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦
    (((cov s).curvatureTensor x u).compr₂
      (((g (s, x)).flip v).toLinearMap)).toContinuousBilinearMap
  have hB (s : ℝ) (a c : TangentSpace I x) :
      B s a c = g (s, x) ((cov s).curvatureTensor x u a c) v := by
    exact LinearMap.toContinuousBilinearMap_apply _ a c
  have hBD : HasDerivAt B (deriv B t) t := by
    apply DifferentiableAt.hasDerivAt (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
    apply differentiableAt_clm_apply₂.mpr
    intro a c
    exact ((hK a c).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s ↦ hB s a c)).differentiableAt
  have hKD (a c : TangentSpace I x) : deriv B t a c = K a c :=
    (hasDerivAt_clm_apply₂.mp hBD a c).unique
      ((hK a c).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s ↦ hB s a c))
  have hd := g.hasDerivAt_ricciTensor_of_bilinear_apply_curvatureTensor
    r hr hcov hg hflow x b u v B (deriv B t) hB hBD
  simpa only [hKD] using hd

/-- The contraction of the six second Ricci terms in curvature variation is the
Ricci heat trace and an antisymmetric residual. Contracted Bianchi cancels the scalar Hessian.
This identity contains no time evolution assumption. -/
private theorem sum_secondCovariantDerivative_ricciTensor_curvatureTensor_eq
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [ContMDiffCovariantDerivative cov ∞]
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (a c : TangentSpace I x) :
    let B := fun y ↦ (cov.ricciTensor y).toContinuousBilinearMap
    let H := cov.bilinear.secondCovariantDerivative cov B x
    (∑ i, (-2 * cov.ricciTensor x (cov.curvatureTensor x a (b i) (b i)) c -
      H a (b i) (b i) c - H a (b i) (b i) c + H a c (b i) (b i) +
        H (b i) a (b i) c + H (b i) (b i) a c - H (b i) c a (b i))) =
      -2 * (∑ i, cov.ricciTensor x a (b i) * cov.ricciTensor x (b i) c) +
        (∑ i, H (b i) a (b i) c) + (∑ i, H (b i) (b i) a c) -
          ∑ i, H (b i) c (b i) a := by
  let B := fun y ↦ (cov.ricciTensor y).toContinuousBilinearMap
  let H := cov.bilinear.secondCovariantDerivative cov B x
  let Q (a c : TangentSpace I x) := ∑ i, cov.ricciTensor x a (b i) * cov.ricciTensor x (b i) c
  let C (a c : TangentSpace I x) := ∑ i, H (b i) a (b i) c
  let L (a c : TangentSpace I x) := ∑ i, H (b i) (b i) a c
  let V (a p c q : TangentSpace I x) := -2 * cov.ricciTensor x (cov.curvatureTensor x a p q) c -
    H a p q c - H a q p c + H a c p q + H p a q c + H p q a c - H p c a q
  have hHsym (a c p q : TangentSpace I x) : H a c p q = H a c q p :=
    hcov.secondCovariantDerivative_ricciTensor_comm ht x a c p q
  have hmetric (a c : TangentSpace I x) :
      (∑ i, cov.ricciTensor x (cov.curvatureTensor x a (b i) (b i)) c) = Q a c :=
    hcov.sum_bilinear_curvatureTensor_self_eq_sum_mul
      ht x b (cov.ricciTensor x) a c
  have hdiv (a c : TangentSpace I x) :
      (∑ i, H a (b i) (b i) c) = (1 / 2 : ℝ) * hessian I cov.scalarCurvature x a c := by
    have hh := hcov.two_mul_sum_secondCovariantDerivative_ricciTensor_eq_hessian
      ht x b a c
    linarith
  have htrace (a c : TangentSpace I x) :
      (∑ i, H a c (b i) (b i)) = hessian I cov.scalarCurvature x a c :=
    hcov.sum_secondCovariantDerivative_ricciTensor_self_eq_hessian
      ht x b a c
  have hV (a c : TangentSpace I x) (i : ι) :
      V a (b i) c (b i) =
        -2 * cov.ricciTensor x (cov.curvatureTensor x a (b i) (b i)) c -
          2 * H a (b i) (b i) c + H a c (b i) (b i) +
            H (b i) a (b i) c + H (b i) (b i) a c - H (b i) c (b i) a := by
    dsimp only [V]
    rw [hHsym (b i) c a (b i)]
    ring
  have hsum : (∑ i, V a (b i) c (b i)) = -2 * Q a c + C a c + L a c - C c a := by
    simp only [hV, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hmetric, hdiv, htrace]
    dsimp only [C, L]
    ring
  -- `V` records exactly the six summands in the displayed contraction.
  simpa only [V, H, B] using hsum

/-- The actual curvature variation and differentiated Bianchi produce Ricci evolution
with the remaining antisymmetric second-derivative trace still displayed. -/
private theorem hasDerivAt_ricciTensor_of_ricciFlow_with_antisymmetric_trace
    (r : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hr : ∀ s, g.metric s = (r s).toNondegenerateMetric)
    (hcov : ∀ s, (g.metric s).IsLeviCivitaConnection (cov s))
    (hg : ∀ y (u v : TangentSpace I y), g (t, y) u v = inner ℝ u v)
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t)
    (x : M) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (u v : TangentSpace I x) :
    let B := fun y ↦ ((cov t).ricciTensor y).toContinuousBilinearMap
    let H := (cov t).bilinear.secondCovariantDerivative (cov t) B x
    HasDerivAt (fun s ↦ (cov s).ricciTensor x u v)
      (2 * (∑ i, ∑ j, (cov t).ricciTensor x (b i) (b j) *
          inner ℝ ((cov t).curvatureTensor x u (b i) (b j)) v) -
        2 * (∑ i, (cov t).ricciTensor x u (b i) * (cov t).ricciTensor x (b i) v) +
        (∑ i, H (b i) (b i) u v) + (∑ i, H (b i) u (b i) v) -
          ∑ i, H (b i) v (b i) u) t := by
  let B := fun y ↦ ((cov t).ricciTensor y).toContinuousBilinearMap
  let H := (cov t).bilinear.secondCovariantDerivative (cov t) B x
  let V (a b c d : TangentSpace I x) :=
    -2 * (cov t).ricciTensor x ((cov t).curvatureTensor x a b d) c -
      H a b d c - H a d b c + H a c b d + H b a d c + H b d a c - H b c a d
  have hd := g.hasDerivAt_ricciTensor_of_apply_curvatureTensor r hr hcov hg hflow x b u v
    (fun p q ↦ V u p v q)
    (fun p q ↦ g.hasDerivAt_apply_curvatureTensor_of_ricciFlow hcov hg hflow x u p q v)
  have hLC := g.isLeviCivitaConnection_of_apply_eq_inner (hcov t) hg
  have hh := sum_secondCovariantDerivative_ricciTensor_curvatureTensor_eq
    hLC.isMetricCompatible hLC.torsion x b u v
  refine hd.congr_deriv ?_
  dsimp only [V]
  linarith

/-- **The native Ricci tensor evolution equation.** The metric velocity is `-2 Ric` and
the four fixed-time tensors use the installed metric at `t`. The heat generator is the
negative of the native positive rough Laplacian on covariant bilinear forms. The two
quadratic contractions are written in an arbitrary orthonormal basis. -/
theorem hasDerivAt_ricciTensor_of_ricciFlow
    (hcov : ∀ s, (g.metric s).IsLeviCivitaConnection (cov s))
    (hg : ∀ y (u v : TangentSpace I y), g (t, y) u v = inner ℝ u v)
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t)
    (x : M) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (u v : TangentSpace I x) :
    HasDerivAt (fun s ↦ (cov s).ricciTensor x u v)
      (-((cov t).bilinear.roughLaplacian (cov t)
          (fun y ↦ ((cov t).ricciTensor y).toContinuousBilinearMap) x) u v +
        2 * (∑ i, ∑ j, (cov t).ricciTensor x (b i) (b j) *
          inner ℝ ((cov t).curvatureTensor x u (b i) (b j)) v) -
        2 * ∑ i, (cov t).ricciTensor x u (b i) * (cov t).ricciTensor x (b i) v) t := by
  obtain ⟨r, hr⟩ := g.exists_riemannianMetric_of_pos t
    (fun y v hv ↦ by rw [hg]; exact real_inner_self_pos.mpr hv)
  let B := fun y ↦ ((cov t).ricciTensor y).toContinuousBilinearMap
  let H := (cov t).bilinear.secondCovariantDerivative (cov t) B x
  let S (a c : TangentSpace I x) := ∑ i, ∑ j,
    (cov t).ricciTensor x (b i) (b j) *
      inner ℝ ((cov t).curvatureTensor x a (b i) (b j)) c
  let Q (a c : TangentSpace I x) :=
    ∑ i, (cov t).ricciTensor x a (b i) * (cov t).ricciTensor x (b i) c
  let C (a c : TangentSpace I x) := ∑ i, H (b i) a (b i) c
  let L (a c : TangentSpace I x) := ∑ i, H (b i) (b i) a c
  let d (a c : TangentSpace I x) := 2 * S a c - 2 * Q a c +
    L a c + C a c - C c a
  have hLC := g.isLeviCivitaConnection_of_apply_eq_inner (hcov t) hg
  have hHsym (a c p q : TangentSpace I x) : H a c p q = H a c q p :=
    hLC.isMetricCompatible.secondCovariantDerivative_ricciTensor_comm
      hLC.torsion x a c p q
  have hd (a c : TangentSpace I x) :
      HasDerivAt (fun s ↦ (cov s).ricciTensor x a c) (d a c) t :=
    g.hasDerivAt_ricciTensor_of_ricciFlow_with_antisymmetric_trace
      r hr hcov hg hflow x b a c
  have hLsym (a c : TangentSpace I x) : L a c = L c a :=
    Finset.sum_congr rfl fun i _ ↦ hHsym (b i) (b i) a c
  have hQsym (a c : TangentSpace I x) : Q a c = Q c a :=
    hLC.isMetricCompatible.sum_ricciTensor_mul_comm hLC.torsion x b a c
  have hSsym (a c : TangentSpace I x) : S a c = S c a :=
    hLC.isMetricCompatible.sum_mul_inner_curvatureTensor_comm
      hLC.torsion x b ((cov t).ricciTensor x)
      (IsMetricCompatible.ricciTensor_comm (cov := cov t)
        hLC.isMetricCompatible hLC.torsion x) a c
  have hdsym (a c : TangentSpace I x) : d a c = d c a :=
    (hd a c).unique ((hd c a).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s ↦
      g.ricciTensor_comm_of_riemannianMetric s (r s) (hr s) (hcov s) x a c))
  have hevol : d u v = 2 * S u v - 2 * Q u v + L u v := by
    have he := hdsym v u
    dsimp only [d] at he ⊢
    rw [hSsym v u, hQsym v u, hLsym v u] at he
    linarith
  have hheat : -((cov t).bilinear.roughLaplacian (cov t) B x) u v = L u v := by
    rw [roughLaplacian_eq_sum _ _ _ x b]
    simp only [neg_apply, sum_apply, neg_neg]
    -- `L` is precisely this basis trace of the second derivative `H` of `B`.
    rfl
  refine (hd u v).congr_deriv ?_
  rw [hevol, hheat]
  ring

end TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

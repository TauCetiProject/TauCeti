/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.RicciFlow.ReducedAction.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Variation
import TauCeti.Analysis.Calculus.BumpFunction.IntervalIntegral
import TauCeti.Geometry.Manifold.MFDeriv.Chart.SmoothVariation

/-!
# Stationary reduced actions and the intrinsic Euler equation

A curve is stationary for the regularized reduced action when the action has derivative zero
along every actual smooth variation with fixed endpoints. On a manifold without boundary,
stationarity is equivalent to the pointwise native equation
`g(V, D_s α') + 4s Ric(V, α') - 2s² dScal(V) = 0` at every interior time
`s ∈ uIoo a b` and for every tangent vector `V` at `γ s`.
The metric and scalar curvature are jointly `C¹` along the central curve, and the forward Ricci
equation is an actual derivative of the metric paired with each tangent direction and velocity.

The converse variational argument constructs chart bump variations. Continuity of the pairing
is obtained from the moving-metric integration-by-parts calculation, so no regularity of an
unspecified Euler source is assumed. The same characterization holds for the backward actions
of the curves composed with square root, including initial square time zero. For `n ≥ 2`,
a `Cⁿ` minimizer among `Cⁿ` curves is stationary even on manifolds with boundary;
on a boundaryless manifold, it consequently satisfies the intrinsic equation.

The localization by chart bump variations adapts
`TauCeti.Manifold.IsEnergyCritical.isGeodesicCurveOn`.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemma 6.4 and equation 6.5.
* The reduced-action development in `frenzymath/lean-eval-submissions` and
  `frenzymath/PoincareConjecture`.
-/

public section

open Bundle CovariantDerivative Filter Metric MeasureTheory Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {γ : ℝ → M} {a b T : ℝ} {n : ℕ∞}

variable (I) in
/-- A `C^n` curve is stationary for the regularized reduced action when every actual `C^n`
variation with fixed endpoints has action derivative zero. Regularity of the central curve is
included, since a nonsmooth curve may admit no such variations. -/
structure IsRegularizedReducedActionStationary (n : ℕ∞)
    (g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (T : ℝ) (γ : ℝ → M) (a b : ℝ) : Prop where
  /-- The central curve is `C^n` along the compact parameter interval. -/
  contMDiffAt : ∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ s
  /-- The derivative of the actual action vanishes along every fixed-endpoint variation. -/
  hasDerivAt : ∀ {F : ℝ → ℝ → M}, F 0 = γ → IsFixedEndpointVariation I n F a b →
    HasDerivAt (fun u ↦ regularizedReducedAction I g T (F u) a b) 0 0

/-- Regularized stationarity consists of central-curve regularity and zero action derivative
along every fixed-endpoint variation. -/
theorem isRegularizedReducedActionStationary_def :
    IsRegularizedReducedActionStationary I n g T γ a b ↔
      (∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ s) ∧
      (∀ {F : ℝ → ℝ → M}, F 0 = γ → IsFixedEndpointVariation I n F a b →
        HasDerivAt (fun u ↦ regularizedReducedAction I g T (F u) a b) 0 0) :=
  ⟨fun h ↦ ⟨h.contMDiffAt, h.hasDerivAt⟩, fun h ↦ ⟨h.1, h.2⟩⟩

variable
  (hg : ∀ s ∈ uIcc a b,
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2 ((g p.1).inner p.2)) (T - s ^ 2, γ s))
  (hR : ∀ s ∈ uIcc a b,
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (fun p : ℝ × M ↦ (g p.1).scalarCurvature p.2) (T - s ^ 2, γ s))
  (hflow : ∀ s ∈ uIcc a b, ∀ V : TangentSpace I (γ s),
    HasDerivAt (fun r ↦ (g r).inner (γ s) V (curveVelocity I γ s))
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g (T - s ^ 2)).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor (γ s) V (curveVelocity I γ s))) (T - s ^ 2))

include hg hR in
/-- Along any actual fixed-endpoint variation of a stationary curve, the intrinsic Euler pairing
has zero integral and is continuous. Both conclusions follow from the first variation. -/
private theorem IsRegularizedReducedActionStationary.integral_eulerPairing_eq_zero_and_continuousOn
    (h : IsRegularizedReducedActionStationary I n g T γ a b) (hn : 2 ≤ n)
    {F : ℝ → ℝ → M} (hF0 : F 0 = γ) (hF : IsFixedEndpointVariation I n F a b)
    (hflowF : ∀ s ∈ uIcc a b,
      HasDerivAt (fun r ↦ (g r).inner (F 0 s) (variationField I F s)
        (curveVelocity I (F 0) s))
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g (T - s ^ 2)).toRiemannianMetric⟩;
          (leviCivitaConnection I M).ricciTensor (F 0 s) (variationField I F s)
            (curveVelocity I (F 0) s))) (T - s ^ 2)) :
    (∫ s in a..b, regularizedReducedEulerCovector I g T γ s (variationField I F s)) = 0 ∧
      ContinuousOn (fun s ↦ regularizedReducedEulerCovector I g T γ s
        (variationField I F s)) (uIcc a b) := by
  subst hF0
  have hF₂ := hF.of_le (WithTop.coe_le_coe.mpr hn)
  constructor
  · have hd := hF₂.hasDerivAt_regularizedReducedAction hg hR hflowF
    have hz := hd.unique (h.hasDerivAt rfl hF)
    simpa only [neg_eq_zero] using hz
  · exact continuousOn_regularizedReducedAction_eulerPairing hF₂.contMDiffAt hg hR hflowF

include hg hR in
/-- A stationary regularized reduced action has zero weak Euler pairing integral for every
actual fixed-endpoint variation, including on manifolds with boundary. -/
theorem IsRegularizedReducedActionStationary.integral_eulerPairing_eq_zero
    (h : IsRegularizedReducedActionStationary I n g T γ a b) (hn : 2 ≤ n)
    {F : ℝ → ℝ → M} (hF0 : F 0 = γ) (hF : IsFixedEndpointVariation I n F a b)
    (hflowF : ∀ s ∈ uIcc a b,
      HasDerivAt (fun r ↦ (g r).inner (F 0 s) (variationField I F s)
        (curveVelocity I (F 0) s))
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g (T - s ^ 2)).toRiemannianMetric⟩;
          (leviCivitaConnection I M).ricciTensor (F 0 s) (variationField I F s)
            (curveVelocity I (F 0) s))) (T - s ^ 2)) :
    (∫ s in a..b, regularizedReducedEulerCovector I g T γ s (variationField I F s)) = 0 :=
  (h.integral_eulerPairing_eq_zero_and_continuousOn hg hR hn hF0 hF hflowF).1

variable {x₀ : M} {J : Set ℝ} {φ : ℝ → ℝ} {e : E}

/-- A chart bump variation tests the intrinsic Euler covector on the corresponding coordinate
vector field, multiplied by its scalar profile. -/
private theorem reducedEulerCovector_variationField_chartVariation [I.Boundaryless]
    (hJ : ∀ s ∈ J, γ s ∈ (extChartAt I x₀).source)
    (hφJ : Function.support φ ⊆ J) (s : ℝ) :
    regularizedReducedEulerCovector I g T γ s
        (variationField I (chartVariation I γ x₀ J φ e) s) =
      φ s * regularizedReducedEulerCovector I g T γ s
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ s) e) := by
  rw [variationField_chartVariation_of_support_subset hJ hφJ, map_smul, smul_eq_mul]

include hg hR hflow in
/-- The actual chart variations of a stationary reduced action give all localized scalar tests
of its native Euler covector, together with continuity of those tests. -/
private theorem IsRegularizedReducedActionStationary.integral_mul_eulerPairing_eq_zero
    [I.Boundaryless] (h : IsRegularizedReducedActionStationary I n g T γ a b) (hn : 2 ≤ n)
    (hJo : IsOpen J) (hJab : J ⊆ uIoo a b)
    (hJ : ∀ s ∈ J, γ s ∈ (extChartAt I x₀).source) (hφ : ContDiff ℝ n φ)
    (hφJ : tsupport φ ⊆ J) (e : E) :
    (∫ s in a..b, φ s * regularizedReducedEulerCovector I g T γ s
      ((trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ s) e)) = 0 ∧
      ContinuousOn (fun s ↦ φ s * regularizedReducedEulerCovector I g T γ s
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ s) e)) (uIcc a b) := by
  have hF : IsFixedEndpointVariation I n (chartVariation I γ x₀ J φ e) a b :=
    isFixedEndpointVariation_chartVariation hJo hJab hJ hφ hφJ h.contMDiffAt
  have hpt := reducedEulerCovector_variationField_chartVariation (g := g) (T := T)
    (e := e) hJ ((subset_tsupport φ).trans hφJ)
  have hF0 := chartVariation_zero (φ := φ) (e := e) hJ
  have hflowF (F : ℝ → ℝ → M) (hF0 : F 0 = γ) : ∀ s ∈ uIcc a b,
      HasDerivAt (fun r ↦ (g r).inner (F 0 s) (variationField I F s)
        (curveVelocity I (F 0) s))
        (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g (T - s ^ 2)).toRiemannianMetric⟩;
          (leviCivitaConnection I M).ricciTensor (F 0 s) (variationField I F s)
            (curveVelocity I (F 0) s))) (T - s ^ 2) := by
    subst hF0
    exact fun s hs ↦ hflow s hs (variationField I F s)
  simpa only [hpt] using h.integral_eulerPairing_eq_zero_and_continuousOn hg hR hn hF0 hF
    (hflowF _ hF0)

include hg hR hflow in
/-- Stationarity under actual fixed-endpoint curve variations forces the pointwise intrinsic
reduced Euler equation at every interior time and in every tangent direction. -/
theorem IsRegularizedReducedActionStationary.eulerCovector_eq_zero [I.Boundaryless]
    (h : IsRegularizedReducedActionStationary I n g T γ a b) (hn : 2 ≤ n) :
    ∀ s ∈ uIoo a b, regularizedReducedEulerCovector I g T γ s = 0 := by
  intro s₀ hs₀
  ext W
  by_contra hW
  let η := regularizedReducedEulerCovector I g T γ
  let e : E := (trivializationAt E (TangentSpace I) (γ s₀)).continuousLinearMapAt ℝ (γ s₀)
    ((η s₀ W) • W)
  let f : ℝ → ℝ := fun s ↦ η s
    ((trivializationAt E (TangentSpace I) (γ s₀)).symmL ℝ (γ s) e)
  have hf₀ : 0 < f s₀ := by
    simpa only [f, e, Trivialization.symmL_continuousLinearMapAt _
      (FiberBundle.mem_baseSet_trivializationAt' (γ s₀)), map_smul, smul_eq_mul, ← sq]
      using sq_pos_of_ne_zero hW
  obtain ⟨δ, hδ, hδJ⟩ := Metric.mem_nhds_iff.mp (inter_mem (isOpen_Ioo.mem_nhds hs₀)
    ((h.contMDiffAt s₀ (uIoo_subset_uIcc_self hs₀)).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) (γ s₀)).mem_nhds (mem_extChartAt_source (γ s₀)))))
  have hJab : ball s₀ δ ⊆ uIoo a b := fun s hs ↦ (hδJ hs).1
  have hJ : ∀ s ∈ ball s₀ δ, γ s ∈ (extChartAt I (γ s₀)).source := fun s hs ↦ (hδJ hs).2
  have hbump : ∀ {c : ℝ} (φ : ContDiffBump c), tsupport φ ⊆ ball s₀ δ →
      (∫ s in a..b, φ s * f s) = 0 ∧ ContinuousOn (fun s ↦ φ s * f s) (uIcc a b) :=
    fun φ hφ ↦ h.integral_mul_eulerPairing_eq_zero hg hR hflow hn isOpen_ball hJab hJ
      φ.contDiff hφ e
  apply hf₀.ne'
  refine TauCeti.eq_zero_of_intervalIntegral_contDiffBump_mul_eq_zero (hs₀.1.trans hs₀.2)
    (Ioo_subset_Icc_self hs₀) hδ (fun φ hφ ↦ (hbump φ hφ).2) fun φ hφ ↦ ?_
  have hint := (hbump φ (hφ.trans inter_subset_left)).1
  rcases le_total a b with hab | hab
  · rwa [inf_of_le_left hab, sup_of_le_right hab]
  · rwa [inf_of_le_right hab, sup_of_le_left hab, intervalIntegral.integral_symm, neg_eq_zero]

include hg hR hflow in
/-- A regular curve satisfying the intrinsic Euler equation is stationary for the actual
regularized reduced action. This implication permits manifolds with boundary. -/
theorem isRegularizedReducedActionStationary_of_eulerCovector_eq_zero
    (hn : 2 ≤ n) (hγ : ∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ s)
    (hEL : ∀ s ∈ uIoo a b, regularizedReducedEulerCovector I g T γ s = 0) :
    IsRegularizedReducedActionStationary I n g T γ a b := by
  refine ⟨hγ, fun {F} hF0 hF ↦ ?_⟩
  subst hF0
  have hpair := fun s hs ↦ hflow s hs (variationField I F s)
  refine ((hF.of_le (WithTop.coe_le_coe.mpr hn)).hasDerivAt_regularizedReducedAction
    hg hR hpair).congr_deriv ?_
  have hz : (∫ s in a..b, regularizedReducedEulerCovector I g T (F 0) s
      (variationField I F s)) = 0 := by
    refine (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [hEL s hs, LinearMap.zero_apply]
  simpa only [neg_eq_zero] using hz

include hg hR hflow in
/-- The variational characterization of the intrinsic reduced Euler equation. The condition on
the right is the concrete covector formed from the native metric, connection and curvature. -/
theorem isRegularizedReducedActionStationary_iff_eulerCovector_eq_zero [I.Boundaryless]
    (hn : 2 ≤ n) (hγ : ∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ s) :
    IsRegularizedReducedActionStationary I n g T γ a b ↔
      ∀ s ∈ uIoo a b, regularizedReducedEulerCovector I g T γ s = 0 :=
  ⟨fun h ↦ h.eulerCovector_eq_zero hg hR hflow hn,
    isRegularizedReducedActionStationary_of_eulerCovector_eq_zero hg hR hflow hn hγ⟩

/-- For nonnegative ordered square times, stationarity of the regularized action is equivalent
to stationarity of the actual backward action along the square-root-reparametrized variations.
The endpoint at square time zero is allowed. -/
theorem isRegularizedReducedActionStationary_iff_backwardReducedAction_comp_sqrt_stationary
    (ha : 0 ≤ a) (hab : a ≤ b) (hn : 1 ≤ n)
    (hγ : ∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ s) :
    IsRegularizedReducedActionStationary I n g T γ a b ↔
      ∀ (F : ℝ → ℝ → M), F 0 = γ → IsFixedEndpointVariation I n F a b →
        HasDerivAt (fun u ↦ backwardReducedAction I g T (F u ∘ Real.sqrt)
          (a ^ 2) (b ^ 2)) 0 0 := by
  have heq (F : ℝ → ℝ → M) (hF : IsFixedEndpointVariation I n F a b) :
      (fun u ↦ backwardReducedAction I g T (F u ∘ Real.sqrt) (a ^ 2) (b ^ 2)) =ᶠ[𝓝 0]
        fun u ↦ regularizedReducedAction I g T (F u) a b := by
    exact eventuallyEq_backwardReducedAction_comp_sqrt ha hab
      (fun s hs ↦ (hF.contMDiffAt s hs).of_le (WithTop.coe_le_coe.mpr hn))
  constructor
  · intro h F hF0 hF
    exact (h.hasDerivAt hF0 hF).congr_of_eventuallyEq (heq F hF)
  · intro h
    exact ⟨hγ, fun {F} hF0 hF ↦
      (h F hF0 hF).congr_of_eventuallyEq (heq F hF).symm⟩

include hg hR hflow in
/-- The actual backward action is stationary under every square-time smooth fixed-endpoint
variation exactly when the native reduced Euler covector vanishes at every interior square time.
This includes intervals whose initial backward time is zero. -/
theorem backwardReducedAction_comp_sqrt_stationary_iff_eulerCovector_eq_zero [I.Boundaryless]
    (ha : 0 ≤ a) (hab : a ≤ b) (hn : 2 ≤ n)
    (hγ : ∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ s) :
    (∀ (F : ℝ → ℝ → M), F 0 = γ → IsFixedEndpointVariation I n F a b →
      HasDerivAt (fun u ↦ backwardReducedAction I g T (F u ∘ Real.sqrt)
        (a ^ 2) (b ^ 2)) 0 0) ↔
      ∀ s ∈ uIoo a b, regularizedReducedEulerCovector I g T γ s = 0 := by
  rw [← isRegularizedReducedActionStationary_iff_backwardReducedAction_comp_sqrt_stationary ha hab
    (one_le_two.trans hn) hγ]
  exact isRegularizedReducedActionStationary_iff_eulerCovector_eq_zero hg hR hflow hn hγ

include hg hR hflow in
/-- At a smooth minimizer, each smooth localization of a variation field has zero Euler
pairing integral. The localized representative has smooth nearby slices. -/
private theorem integral_mul_eulerPairing_eq_zero_of_smooth_minimizing
    {F : ℝ → ℝ → M} (hF0 : F 0 = γ) (hF : IsFixedEndpointVariation I ∞ F a b)
    (hmin : ∀ α : ℝ → M,
      (∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ α s) → α a = γ a → α b = γ b →
      regularizedReducedAction I g T γ a b ≤ regularizedReducedAction I g T α a b)
    {K : Set ℝ} (hJo : IsOpen J) (hK : IsCompact K) (hJK : J ⊆ K) (hKab : K ⊆ uIoo a b)
    (hchart : ∀ s ∈ K, γ s ∈ (extChartAt I x₀).source) (hφ : ContDiff ℝ ∞ φ)
    (hφJ : tsupport φ ⊆ J) :
    (∫ s in a..b, φ s * regularizedReducedEulerCovector I g T γ s (variationField I F s)) =
      0 := by
  subst hF0
  obtain ⟨G, hG0, hG, hsmooth, hV⟩ :=
    hF.exists_localized_smooth_slices hJo hK hJK hKab hchart hφ hφJ
  have hlocal : IsLocalMin (fun u ↦ regularizedReducedAction I g T (G u) a b) 0 := by
    filter_upwards [hsmooth, hG.eventually_apply_left, hG.eventually_apply_right]
      with u hu ha hb
    simpa only [hG0] using hmin (G u) hu (ha.trans (congrFun hG0 a)) (hb.trans (congrFun hG0 b))
  rw [← hG0] at hflow
  have hzero := (hG.of_le (m := 2) (by simp))
    |>.integral_eq_zero_of_isLocalMin_regularizedReducedAction
      (by simpa only [hG0] using hg) (by simpa only [hG0] using hR)
      (fun s hs ↦ hflow s hs (variationField I G s)) hlocal
  refine (intervalIntegral.integral_congr_uIoo ?_).trans hzero
  intro s hs
  simp only [hV s (uIoo_subset_uIcc_self hs)]
  have hcentral := congrArg
    (fun β ↦ regularizedReducedEulerCovector I g T β s (φ s • variationField I F s)) hG0
  rw [hcentral, map_smul, smul_eq_mul]

include hg hR hflow in
/-- The interior pairing of a smooth minimizing curve with any smooth variation field
vanishes by testing against bumps in a chart about each interior point. -/
private theorem eulerPairing_eq_zero_of_smooth_minimizing
    {F : ℝ → ℝ → M} (hF0 : F 0 = γ) (hF : IsFixedEndpointVariation I ∞ F a b)
    (hmin : ∀ α : ℝ → M,
      (∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ α s) → α a = γ a → α b = γ b →
      regularizedReducedAction I g T γ a b ≤ regularizedReducedAction I g T α a b)
    {s₀ : ℝ} (hs₀ : s₀ ∈ uIoo a b) :
    regularizedReducedEulerCovector I g T γ s₀ (variationField I F s₀) = 0 := by
  subst hF0
  let f := fun s ↦ regularizedReducedEulerCovector I g T (F 0) s (variationField I F s)
  have hc : ContinuousOn f (uIcc a b) :=
    continuousOn_regularizedReducedAction_eulerPairing (hF.of_le (m := 2) (by simp)).contMDiffAt
      hg hR fun s hs ↦ hflow s hs (variationField I F s)
  have hγ := (hF.contMDiffAt_apply_zero (uIoo_subset_uIcc_self hs₀)).continuousAt
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (isOpen_Ioo.mem_nhds hs₀)
    (hγ.preimage_mem_nhds ((isOpen_extChartAt_source (I := I) (F 0 s₀)).mem_nhds
      (mem_extChartAt_source (F 0 s₀)))))
  have hsub : closedBall s₀ (δ / 2) ⊆ uIoo a b ∩ (F 0) ⁻¹' (extChartAt I (F 0 s₀)).source :=
    (closedBall_subset_ball (by linarith)).trans hδsub
  refine TauCeti.eq_zero_of_intervalIntegral_contDiffBump_mul_eq_zero (hs₀.1.trans hs₀.2)
    (Ioo_subset_Icc_self hs₀) (half_pos hδ) (fun φ _ ↦ φ.continuous.continuousOn.mul hc)
    fun φ hφ ↦ ?_
  have hint := integral_mul_eulerPairing_eq_zero_of_smooth_minimizing hg hR hflow rfl hF hmin
    isOpen_ball (isCompact_closedBall s₀ (δ / 2)) ball_subset_closedBall
    (fun _ hs ↦ (hsub hs).1) (fun _ hs ↦ (hsub hs).2)
    φ.contDiff (hφ.trans inter_subset_left)
  rcases le_total a b with hab | hab
  · rwa [inf_of_le_left hab, sup_of_le_right hab]
  · rwa [inf_of_le_right hab, sup_of_le_left hab, intervalIntegral.integral_symm, neg_eq_zero]

include hg hR hflow in
/-- A finite-order minimizing curve is stationary because sufficiently small variations
have all nearby slices in the competitor class. -/
private theorem isRegularizedReducedActionStationary_of_minimizing_fin
    {k : ℕ} (hk : 2 ≤ k)
    (hγ : ∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I k γ s)
    (hmin : ∀ α : ℝ → M,
      (∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I k α s) → α a = γ a → α b = γ b →
      regularizedReducedAction I g T γ a b ≤ regularizedReducedAction I g T α a b) :
    IsRegularizedReducedActionStationary I (k : ℕ∞) g T γ a b := by
  refine ⟨hγ, fun {F} hF0 hF ↦ ?_⟩
  subst hF0
  obtain ⟨U, O, hU, hO, h0, hK, hFO⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn (n := (k : ℕ∞ω))
      isCompact_uIcc (by simp) hF.contMDiffAt
  have hlocal : IsLocalMin (fun u ↦ regularizedReducedAction I g T (F u) a b) 0 := by
    filter_upwards [hU.mem_nhds h0, hF.eventually_apply_left,
      hF.eventually_apply_right] with u hu hleft hright
    exact hmin (F u) (fun s hs ↦
      (hFO.contMDiffAt ((hU.prod hO).mem_nhds ⟨hu, hK hs⟩)).comp s
        (contDiff_prodMk_right u).contMDiff.contMDiffAt) hleft hright
  have hF₂ := hF.of_le (m := 2) (WithTop.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hk))
  have hderiv := hF₂.hasDerivAt_regularizedReducedAction
    hg hR (fun s hs ↦ hflow s hs (variationField I F s))
  exact hderiv.congr_deriv (hlocal.hasDerivAt_eq_zero hderiv)

include hg hR hflow in
/-- A `Cⁿ` minimizer of the actual regularized reduced action among `Cⁿ` curves with its
endpoints is stationary, also on manifolds with boundary and for `n = ∞`. -/
theorem isRegularizedReducedActionStationary_of_minimizing
    (hn : 2 ≤ n) (hγ : ∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ s)
    (hmin : ∀ α : ℝ → M,
      (∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n α s) → α a = γ a → α b = γ b →
      regularizedReducedAction I g T γ a b ≤ regularizedReducedAction I g T α a b) :
    IsRegularizedReducedActionStationary I n g T γ a b := by
  induction n using ENat.recTopCoe with
  | top =>
    refine ⟨hγ, fun {F} hF0 hF ↦ ?_⟩
    subst hF0
    have hd := (hF.of_le (m := 2) (by simp)).hasDerivAt_regularizedReducedAction
      hg hR (fun s hs ↦ hflow s hs (variationField I F s))
    have hzero : (∫ s in a..b, regularizedReducedEulerCovector I g T (F 0) s
        (variationField I F s)) = 0 :=
      (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun s hs ↦
        eulerPairing_eq_zero_of_smooth_minimizing hg hR hflow rfl hF hmin hs).trans
        intervalIntegral.integral_zero
    simpa only [hzero, neg_zero] using hd
  | coe k =>
    exact isRegularizedReducedActionStationary_of_minimizing_fin hg hR hflow
      (by exact_mod_cast hn) hγ hmin

include hg hR hflow in
/-- A `Cⁿ` minimizer satisfies the intrinsic reduced Euler equation at every interior time on
a boundaryless manifold. Its stationarity itself does not require boundarylessness. -/
theorem regularizedReducedEulerCovector_eq_zero_of_minimizing [I.Boundaryless]
    (hn : 2 ≤ n)
    (hγ : ∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ s)
    (hmin : ∀ α : ℝ → M,
      (∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n α s) → α a = γ a → α b = γ b →
      regularizedReducedAction I g T γ a b ≤ regularizedReducedAction I g T α a b) :
    ∀ s ∈ uIoo a b, regularizedReducedEulerCovector I g T γ s = 0 :=
  (isRegularizedReducedActionStationary_of_minimizing hg hR hflow hn hγ hmin)
    |>.eulerCovector_eq_zero hg hR hflow hn

include hg hR hflow in
/-- A `Cⁿ` square-time curve minimizing the actual backward action is stationary for the
regularized action, including on manifolds with boundary and at initial square time zero. -/
theorem isRegularizedReducedActionStationary_of_minimizing_backwardReducedAction_comp_sqrt
    (ha : 0 ≤ a) (hab : a ≤ b) (hn : 2 ≤ n)
    (hγ : ∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ s)
    (hmin : ∀ α : ℝ → M,
      (∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n α s) → α a = γ a → α b = γ b →
      backwardReducedAction I g T (γ ∘ Real.sqrt) (a ^ 2) (b ^ 2) ≤
        backwardReducedAction I g T (α ∘ Real.sqrt) (a ^ 2) (b ^ 2)) :
    IsRegularizedReducedActionStationary I n g T γ a b := by
  apply isRegularizedReducedActionStationary_of_minimizing hg hR hflow hn hγ
  intro α hα hαa hαb
  have hmd {β : ℝ → M}
      (hβ : ∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n β s) :
      ∀ s ∈ Ioo a b, MDifferentiableAt 𝓘(ℝ, ℝ) I β s := by
    intro s hs
    exact ((hβ s (by rw [uIcc_of_le hab]; exact ⟨hs.1.le, hs.2.le⟩)).of_le
      (WithTop.coe_le_coe.mpr (one_le_two.trans hn))).mdifferentiableAt one_ne_zero
  rw [← backwardReducedAction_comp_sqrt ha hab (hmd hγ),
    ← backwardReducedAction_comp_sqrt ha hab (hmd hα)]
  exact hmin α hα hαa hαb

include hg hR hflow in
/-- A `Cⁿ` square-time curve minimizing the actual backward reduced action among `Cⁿ`
square-time competitors with its endpoints satisfies the intrinsic reduced Euler equation
on a boundaryless manifold. Initial square time zero is permitted. -/
theorem regularizedReducedEulerCovector_eq_zero_of_minimizing_backwardReducedAction_comp_sqrt
    [I.Boundaryless] (ha : 0 ≤ a) (hab : a ≤ b) (hn : 2 ≤ n)
    (hγ : ∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ s)
    (hmin : ∀ α : ℝ → M,
      (∀ s ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n α s) → α a = γ a → α b = γ b →
      backwardReducedAction I g T (γ ∘ Real.sqrt) (a ^ 2) (b ^ 2) ≤
        backwardReducedAction I g T (α ∘ Real.sqrt) (a ^ 2) (b ^ 2)) :
    ∀ s ∈ uIoo a b, regularizedReducedEulerCovector I g T γ s = 0 :=
  (isRegularizedReducedActionStationary_of_minimizing_backwardReducedAction_comp_sqrt
    hg hR hflow ha hab hn hγ hmin).eulerCovector_eq_zero hg hR hflow hn

end TauCeti.Manifold

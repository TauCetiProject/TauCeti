/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# Dominated convergence away from one point

This file packages the common application of dominated convergence in which a parameterized
family is controlled and converges pointwise away from one exceptional point. When that point has
measure zero, the pointwise hypotheses supply the almost-everywhere hypotheses of the dominated
convergence theorem. It also records the convergence of integrals against cutoffs
which equal one on a closed ball and are supported in shrinking larger balls, and against cutoffs
which equal one on balls exhausting a normed space, the vanishing of the integral of an
integrable function outside growing balls, as well as convergence after removing a shrinking
neighbourhood of zero from an integrable function vanishing at zero, and the convergence
of interval integrals `∫ Φ(t, y_i(t)) dt` of a continuous function along maps `y_i` which converge
pointwise, with `Φ` bounded along them or with values in a compact set, or along continuous paths
which converge uniformly, and of `∫ Φ_i(t, y_i(t)) dt` for uniformly converging `Φ_i` along maps
`y_i` which converge uniformly to a constant. An interval integral `∫ t in a..b, f x t` also
depends continuously on `x ∈ s` as soon as `f` is jointly continuous on `s ×ˢ uIcc a b`, including
at boundary points of `s` (such as the endpoints of a closed interval), where Mathlib's
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` would require continuity
on the whole space.

## Main declarations

* `TauCeti.tendsto_integral_mul_of_dominated_away`: dominated convergence for a family multiplied
  by a fixed weight, with domination and convergence away from a null point.
* `TauCeti.tendsto_integral_smul_of_cutoff`: integrals against cutoffs equal to one on
  `closedBall x r` and vanishing off `ball x (r + h)` tend to the integral over `closedBall x r` as
  `h → 0⁺`.
* `TauCeti.tendsto_integral_smul_of_eq_one_ball`: integrals against `[0, 1]`-valued cutoffs equal
  to one on `ball 0 (R i)` with `R i → ∞` tend to the integral over the whole space.
* `TauCeti.tendsto_setIntegral_compl_ball`: the integral of an integrable function outside
  `ball x R` tends to zero as `R → ∞`.
* `TauCeti.tendsto_integral_abs_gt`: removing a shrinking neighbourhood of zero recovers the
  integral of an integrable function vanishing at zero.
* `TauCeti.tendsto_intervalIntegral_comp_of_tendsto_of_norm_le`,
  `TauCeti.tendsto_intervalIntegral_comp_of_tendsto`: for continuous `Φ`, the integrals
  `∫_{t₁}^{t₂} Φ(t, y_i(t)) dt` converge when the `y_i` converge pointwise and `Φ` is bounded
  along them, for instance when they stay in a compact set.
* `TauCeti.tendsto_intervalIntegral_comp_of_continuousOn`: the same for bounded `Φ` along
  `u ∘ y_i`, where `u` is continuous on a set containing the values of the `y_i`.
* `TauCeti.tendsto_intervalIntegral_comp_of_tendstoUniformlyOn`: the integrals
  `∫_{t₁}^{t₂} Φ i t (y i t) dt` tend to `∫_{t₁}^{t₂} Φ₀ t x dt` when the `Φ i` converge uniformly
  near `x` to `Φ₀`, continuous along `uIcc t₁ t₂ ×ˢ {x}`, and the `y i` converge uniformly to the
  constant `x`.
* `TauCeti.continuousOn_parametric_intervalIntegral_of_continuousOn`: an interval integral of a
  function continuous on `s ×ˢ uIcc a b` is continuous in the parameter on `s`.
* `TauCeti.tendsto_setIntegral_preimage_Ioo_zero`: integrals of an integrable function over the
  shells `{0 < w < η k}` tend to `0` as `η k` tends to `0`.
* `TendstoUniformlyOn.tendsto_intervalIntegral_comp`: if `F i → f` uniformly on `[[a, b]]`, then
  `∫ g(t, F i t) dt → ∫ g(t, f t) dt` over `a..b` for every jointly continuous `g`.
* `MeasureTheory.IntegrableOn.tendsto_integral_sdiff_closedBall_nhdsGT`: excising a shrinking
  closed ball around a point `ξ` that is null for `μ.restrict Δ` recovers `∫ z in Δ, h z ∂μ` as
  `ε → 0⁺`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Topology Set Metric Function

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- An a.e. limit along a countably generated filter of functions that are eventually
a.e.-strongly measurable is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_of_tendsto_ae_of_eventually {ι β : Type*} [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] (l : Filter ι) [l.NeBot] [l.IsCountablyGenerated]
    {f : ι → α → β} {g : α → β} (hf : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ)
    (lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ f i x) l (𝓝 (g x))) : AEStronglyMeasurable g μ := by
  obtain ⟨u, hu⟩ := exists_seq_tendsto l
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually hf)
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n ↦ f (u (n + N)))
    (fun n ↦ hN _ (Nat.le_add_left N n)) ?_
  filter_upwards [lim] with x hx
  exact hx.comp (hu.comp (tendsto_add_atTop_nat N))

/-- **Dominated convergence away from one point.** Suppose `K i` is eventually a.e.-strongly
measurable, and `K i` is eventually dominated by `K₀` and converges to it away from a point
`x₀` with `μ {x₀} = 0`. If `K₀ * w` is integrable, then the integrals of `K i * w` converge to the
integral of `K₀ * w`. No measurability hypothesis on `w` is needed.

The exceptional point is useful for regularizations of singular kernels. The statement is for an
arbitrary countably generated filter and an arbitrary measure space.
-/
theorem tendsto_integral_mul_of_dominated_away {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {x₀ : α} (hx₀ : μ {x₀} = 0) {K : ι → α → ℝ} {K₀ w : α → ℝ}
    (hK : ∀ᶠ i in l, AEStronglyMeasurable (K i) μ)
    (hint : Integrable (fun x ↦ K₀ x * w x) μ)
    (hle : ∀ᶠ i in l, ∀ x ≠ x₀, |K i x| ≤ |K₀ x|)
    (hlim : ∀ x ≠ x₀, Tendsto (fun i ↦ K i x) l (𝓝 (K₀ x))) :
    Tendsto (fun i ↦ ∫ x, K i x * w x ∂μ) l (𝓝 (∫ x, K₀ x * w x ∂μ)) := by
  have hae : ∀ᵐ x ∂μ, x ≠ x₀ := compl_mem_ae_iff.2 hx₀
  rcases eq_or_neBot l with rfl | hl
  · exact tendsto_bot
  -- The limit `K₀` is a.e.-strongly measurable, being an a.e. limit along a sequence.
  have hK₀ : AEStronglyMeasurable K₀ μ :=
    aestronglyMeasurable_of_tendsto_ae_of_eventually l hK
      (by filter_upwards [hae] with x hx using hlim x hx)
  -- Where `K₀ = 0` the family vanishes, so `K i * w = K i * (K₀ * w / K₀)` a.e.
  have hmeas : ∀ᶠ i in l, AEStronglyMeasurable (fun x ↦ K i x * w x) μ := by
    filter_upwards [hK, hle] with i hi hle'
    refine (hi.mul (hint.aemeasurable.div hK₀.aemeasurable).aestronglyMeasurable).congr ?_
    filter_upwards [hae] with x hx
    by_cases h0 : K₀ x = 0
    · have : K i x = 0 := abs_nonpos_iff.1 (by simpa [h0] using hle' x hx)
      simp [this]
    · simp only [Pi.mul_apply, Pi.div_apply]
      rw [mul_div_cancel_left₀ _ h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖K₀ x * w x‖)
    hmeas ?_ hint.norm ?_
  · filter_upwards [hle] with i hi
    filter_upwards [hae] with x hx
    simp only [norm_mul, Real.norm_eq_abs]
    gcongr ?_ * _
    exact hi x hx
  · filter_upwards [hae] with x hx
    exact (hlim x hx).mul_const _

/-- Removing a shrinking neighbourhood of zero recovers the integral of an integrable
function vanishing at zero. The measure may charge zero, and the cutoff parameter approaches
zero from either side. -/
theorem tendsto_integral_abs_gt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure ℝ} {f : ℝ → E} (hf : Integrable f μ) (hf₀ : f 0 = 0) :
    Tendsto (fun ε : ℝ ↦ ∫ x in {x : ℝ | ε < |x|}, f x ∂μ) (𝓝 0)
      (𝓝 (∫ x, f x ∂μ)) := by
  have hs (ε : ℝ) : MeasurableSet {x : ℝ | ε < |x|} := by measurability
  simp_rw [← integral_indicator (hs _)]
  refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖)
    (.of_forall fun ε ↦ hf.aestronglyMeasurable.indicator (hs ε))
    (.of_forall fun ε ↦ ae_of_all _ fun x ↦ norm_indicator_le_norm_self _ _) hf.norm ?_
  apply ae_of_all
  intro x
  by_cases hx : x = 0
  · simp [hx, hf₀, indicator_apply]
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_nhds (abs_pos.mpr hx)] with ε hε
    simp only [indicator_apply, mem_ofPred_eq, ite_eq_left hε]

/-- **Dominated convergence for shrinking cutoffs.** Let `f : α → E` be measurable, and let the
cutoffs `ψ h : E → ℝ`, for `h > 0`, be measurable with absolute value at most one, equal to one
on `closedBall x r` and vanishing off `ball x (r + h)`. If `g` is integrable on
`f ⁻¹' closedBall x (r + δ)` for some `δ > 0`, then the integrals of `ψ h (f y) • g y` tend to the
integral of `g` over `f ⁻¹' closedBall x r` as `h → 0⁺`. -/
theorem tendsto_integral_smul_of_cutoff {E G : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : α → E}
    (hf : Measurable f) {g : α → G} {x : E} {r δ : ℝ}
    (hδ : 0 < δ) (hint : IntegrableOn g (f ⁻¹' closedBall x (r + δ)) μ)
    {ψ : ℝ → E → ℝ} (hψm : ∀ h, 0 < h → Measurable (ψ h))
    (hψle : ∀ h, 0 < h → ∀ y, |ψ h y| ≤ 1)
    (hψ1 : ∀ h, 0 < h → EqOn (ψ h) 1 (closedBall x r))
    (hψR : ∀ h, 0 < h → support (ψ h) ⊆ ball x (r + h)) :
    Tendsto (fun h => ∫ y, ψ h (f y) • g y ∂μ) (𝓝[>] 0)
      (𝓝 (∫ y in f ⁻¹' closedBall x r, g y ∂μ)) := by
  have hψ0 (h : ℝ) (hh : 0 < h) : ∀ y ∉ ball x (r + h), ψ h y = 0 :=
    support_subset_iff'.1 (hψR h hh)
  rw [← integral_indicator (measurableSet_closedBall.preimage hf)]
  refine tendsto_integral_filter_of_dominated_convergence
    ((f ⁻¹' closedBall x (r + δ)).indicator fun y => ‖g y‖) ?_ ?_
    (IntegrableOn.integrable_indicator hint.norm (measurableSet_closedBall.preimage hf)) ?_
  · filter_upwards [Ioc_mem_nhdsGT hδ] with h hh
    have hψS : ∀ y ∉ f ⁻¹' closedBall x (r + δ), ψ h (f y) = 0 := fun y hy =>
      hψ0 h hh.1 (f y) fun h' => hy (ball_subset_closedBall
        (ball_subset_ball (by linarith [hh.2]) h'))
    have hind : (fun y => ψ h (f y) • g y) =
        (f ⁻¹' closedBall x (r + δ)).indicator fun y => ψ h (f y) • g y :=
      (indicator_eq_self.2 fun y hy => by_contra fun hy' => hy (by rw [hψS y hy', zero_smul])).symm
    rw [hind, aestronglyMeasurable_indicator_iff (measurableSet_closedBall.preimage hf)]
    exact ((hψm h hh.1).comp hf).aestronglyMeasurable.smul hint.aestronglyMeasurable
  -- The cutoffs are bounded by one and vanish off `closedBall x (r + δ)` once `h ≤ δ`.
  · filter_upwards [Ioc_mem_nhdsGT hδ] with h hh
    refine .of_forall fun y => ?_
    by_cases hy : f y ∈ closedBall x (r + δ)
    · rw [indicator_of_mem (mem_preimage.2 hy), norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hψle h hh.1 _)
    · rw [indicator_of_notMem (mt mem_preimage.1 hy),
        hψ0 h hh.1 (f y) fun h' => hy (ball_subset_closedBall
          (ball_subset_ball (by linarith [hh.2]) h')), zero_smul, norm_zero]
  -- Pointwise, the cutoffs tend to the indicator of `closedBall x r`.
  · refine .of_forall fun y => tendsto_const_nhds.congr' ?_
    by_cases hy : f y ∈ closedBall x r
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simp [indicator_of_mem (mem_preimage.2 hy), hψ1 h hh hy]
    · filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 (not_le.1 hy))] with h hh
      simp [indicator_of_notMem (mt mem_preimage.1 hy),
        hψ0 h hh.1 (f y) fun h' => (mem_ball.1 h').not_ge (by linarith [hh.2])]

/-- **Integrals against cutoffs exhaust the space.** If the cutoffs `χ i` take values in `[0, 1]`
and equal `1` on `ball 0 (R i)` with `R i → ∞`, then `∫ χ i • f → ∫ f` for integrable `f`. -/
theorem tendsto_integral_smul_of_eq_one_ball {E F : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {χ : ι → E → ℝ} {R : ι → ℝ} {μ : Measure E}
    (hR : Tendsto R l atTop) (hχm : ∀ i, AEStronglyMeasurable (χ i) μ)
    (hχ1 : ∀ i x, ‖x‖ < R i → χ i x = 1) (hχI : ∀ i x, χ i x ∈ Set.Icc (0 : ℝ) 1)
    {f : E → F} (hf : Integrable f μ) :
    Tendsto (fun i ↦ ∫ x, χ i x • f x ∂μ) l (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖)
    (.of_forall fun i ↦ (hχm i).smul hf.aestronglyMeasurable)
    (.of_forall fun i ↦ .of_forall fun x ↦ ?_) hf.norm (.of_forall fun x ↦ ?_)
  · rw [norm_smul, Real.norm_of_nonneg (hχI i x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχI i x).2
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hR.eventually_gt_atTop ‖x‖] with i hi
    rw [hχ1 i x hi, one_smul]

/-- **Tails of an integral vanish.** For integrable `g`, the integral of `g` outside `ball x R`
tends to `0` as `R → ∞`. -/
theorem tendsto_setIntegral_compl_ball {X F : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure X}
    {g : X → F} (hg : Integrable g μ) (x : X) :
    Tendsto (fun R : ℝ ↦ ∫ y in (ball x R)ᶜ, g y ∂μ) atTop (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone (μ := μ) (f := g) (s := fun R : ℝ ↦ (ball x R)ᶜ)
    (fun _ ↦ measurableSet_ball.compl) (fun _ _ hRS ↦ compl_subset_compl.2 (ball_subset_ball hRS))
    ⟨0, hg.integrableOn⟩
  have hempty : ⋂ R : ℝ, (ball x R)ᶜ = ∅ :=
    eq_empty_of_forall_notMem fun y hy ↦ (mem_compl_iff _ _).1 (mem_iInter.1 hy (dist y x + 1))
      (mem_ball.2 (lt_add_one _))
  rwa [hempty, Measure.restrict_empty, integral_zero_measure] at h

/-- **Dominated convergence for bounded continuous functions of converging maps.** Let
`Φ : ℝ × V → E` be continuous, and let the maps `y i : ℝ → V` be eventually continuous on
`uIoc t₁ t₂`, with `‖Φ(t, y i t)‖ ≤ C` there. If the `y i` converge pointwise on `uIoc t₁ t₂` to
`x`, then `∫_{t₁}^{t₂} Φ(t, y i t) dt` tends to `∫_{t₁}^{t₂} Φ(t, x t) dt`. -/
theorem tendsto_intervalIntegral_comp_of_tendsto_of_norm_le {ι V E : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [TopologicalSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ × V → E} (hΦ : Continuous Φ) {y : ι → ℝ → V} {x : ℝ → V} {t₁ t₂ C : ℝ}
    (hy : ∀ᶠ i in l, ContinuousOn (y i) (uIoc t₁ t₂))
    (hC : ∀ᶠ i in l, ∀ t ∈ uIoc t₁ t₂, ‖Φ (t, y i t)‖ ≤ C)
    (hyx : ∀ t ∈ uIoc t₁ t₂, Tendsto (fun i ↦ y i t) l (𝓝 (x t))) :
    Tendsto (fun i ↦ ∫ t in t₁..t₂, Φ (t, y i t)) l (𝓝 (∫ t in t₁..t₂, Φ (t, x t))) :=
  intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C)
    (hy.mono fun _ hi ↦ (hΦ.comp_continuousOn (continuousOn_id.prodMk hi)).aestronglyMeasurable
      measurableSet_uIoc)
    (hC.mono fun _ hi ↦ Eventually.of_forall hi) intervalIntegrable_const
    (Eventually.of_forall fun t ht ↦ (hΦ.tendsto (t, x t)).comp
      (tendsto_const_nhds.prodMk_nhds (hyx t ht)))

/-- **Dominated convergence for bounded continuous functions along a map continuous on a set.**
Let `Φ : ℝ × V → E` be continuous and bounded by `C`, and let `u : X → V` be continuous on `S`. If
the maps `y i : ℝ → X` are eventually continuous on `uIoc t₁ t₂` with values there in `S`, and the
`u ∘ y i` converge pointwise on `uIoc t₁ t₂` to `x`, then `∫_{t₁}^{t₂} Φ(t, u(y i t)) dt` tends to
`∫_{t₁}^{t₂} Φ(t, x t) dt`. -/
theorem tendsto_intervalIntegral_comp_of_continuousOn {ι X V E : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [TopologicalSpace X] [TopologicalSpace V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Φ : ℝ × V → E} (hΦ : Continuous Φ) {C : ℝ} (hC : ∀ p, ‖Φ p‖ ≤ C)
    {u : X → V} {S : Set X} (hu : ContinuousOn u S) {y : ι → ℝ → X} {x : ℝ → V} {t₁ t₂ : ℝ}
    (hy : ∀ᶠ i in l, ContinuousOn (y i) (uIoc t₁ t₂))
    (hyS : ∀ᶠ i in l, MapsTo (y i) (uIoc t₁ t₂) S)
    (hyx : ∀ t ∈ uIoc t₁ t₂, Tendsto (fun i ↦ u (y i t)) l (𝓝 (x t))) :
    Tendsto (fun i ↦ ∫ t in t₁..t₂, Φ (t, u (y i t))) l (𝓝 (∫ t in t₁..t₂, Φ (t, x t))) :=
  tendsto_intervalIntegral_comp_of_tendsto_of_norm_le hΦ
    ((hy.and hyS).mono fun _ hi ↦ hu.comp hi.1 hi.2) (Eventually.of_forall fun _ _ _ ↦ hC _) hyx

/-- **Dominated convergence for continuous functions of converging maps.** Let `Φ : ℝ × V → E`
be continuous, and let the maps `y i : ℝ → V` be continuous on `[t₁, t₂]` with values there in a
compact set `K`. If the `y i` converge pointwise on `[t₁, t₂]` to `x`, then
`∫_{t₁}^{t₂} Φ(t, y i t) dt` tends to `∫_{t₁}^{t₂} Φ(t, x t) dt`. -/
theorem tendsto_intervalIntegral_comp_of_tendsto {ι V E : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [TopologicalSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ × V → E} (hΦ : Continuous Φ) {K : Set V} (hK : IsCompact K) {y : ι → ℝ → V}
    {x : ℝ → V} {t₁ t₂ : ℝ} (hy : ∀ i, ContinuousOn (y i) (uIcc t₁ t₂))
    (hyK : ∀ i, ∀ t ∈ uIcc t₁ t₂, y i t ∈ K)
    (hyx : ∀ t ∈ uIcc t₁ t₂, Tendsto (fun i ↦ y i t) l (𝓝 (x t))) :
    Tendsto (fun i ↦ ∫ t in t₁..t₂, Φ (t, y i t)) l (𝓝 (∫ t in t₁..t₂, Φ (t, x t))) := by
  obtain ⟨C, hC⟩ := (isCompact_uIcc.prod hK).exists_bound_of_continuousOn hΦ.continuousOn
  exact tendsto_intervalIntegral_comp_of_tendsto_of_norm_le hΦ
    (Eventually.of_forall fun i ↦ (hy i).mono uIoc_subset_uIcc)
    (Eventually.of_forall fun i t ht ↦
      hC _ ⟨uIoc_subset_uIcc ht, hyK i t (uIoc_subset_uIcc ht)⟩)
    fun t ht ↦ hyx t (uIoc_subset_uIcc ht)

/-- **Integrals along maps converging to a point, for uniformly converging integrands.** Let the
functions `Φ i : ℝ → V → E` converge uniformly on `uIcc t₁ t₂ ×ˢ U` to `Φ₀` for some
neighbourhood `U` of `x`, where `Φ₀` is jointly continuous at the points `(t, x)` with
`t ∈ uIcc t₁ t₂`. If the maps `y i : ℝ → V` converge uniformly on `uIcc t₁ t₂` to the constant
map at `x`, in the sense that they eventually take values in any given neighbourhood of `x` there,
then `∫_{t₁}^{t₂} Φ i t (y i t) dt` tends to `∫_{t₁}^{t₂} Φ₀ t x dt`, provided the integrands are
eventually integrable. No continuity of the `Φ i` or the `y i` is assumed, and the filter need not
be countably generated. -/
theorem tendsto_intervalIntegral_comp_of_tendstoUniformlyOn {ι V E : Type*} [TopologicalSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {l : Filter ι} {Φ : ι → ℝ → V → E} {Φ₀ : ℝ → V → E} {y : ι → ℝ → V} {x : V} {t₁ t₂ : ℝ}
    {U : Set V} (hU : U ∈ 𝓝 x) (hcont : ∀ t ∈ uIcc t₁ t₂, ContinuousAt (uncurry Φ₀) (t, x))
    (hunif : TendstoUniformlyOn (fun i ↦ uncurry (Φ i)) (uncurry Φ₀) l (uIcc t₁ t₂ ×ˢ U))
    (hint : ∀ᶠ i in l, IntervalIntegrable (fun t ↦ Φ i t (y i t)) μ t₁ t₂)
    (hy : ∀ U ∈ 𝓝 x, ∀ᶠ i in l, ∀ t ∈ uIcc t₁ t₂, y i t ∈ U) :
    Tendsto (fun i ↦ ∫ t in t₁..t₂, Φ i t (y i t) ∂μ) l (𝓝 (∫ t in t₁..t₂, Φ₀ t x ∂μ)) := by
  have hcx : ∀ t ∈ uIcc t₁ t₂, ContinuousAt (fun t ↦ Φ₀ t x) t := fun t ht ↦
    (hcont t ht).comp (f := fun s ↦ (s, x)) (continuousAt_id.prodMk continuousAt_const)
  have hint₀ : IntervalIntegrable (fun t ↦ Φ₀ t x) μ t₁ t₂ :=
    ContinuousOn.intervalIntegrable fun t ht ↦ (hcx t ht).continuousWithinAt
  -- The integrands converge uniformly on `uIcc t₁ t₂` to `t ↦ Φ₀ t x`.
  have hunif' : TendstoUniformlyOn (fun i t ↦ Φ i t (y i t) - Φ₀ t x) 0 l (uIcc t₁ t₂) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    -- Near `x`, uniformly in `t ∈ uIcc t₁ t₂`, the limit is within `ε / 2` of its value at `x`,
    -- by compactness of `uIcc t₁ t₂`.
    have hnear : ∀ᶠ z in 𝓝 x, ∀ t ∈ uIcc t₁ t₂, dist (Φ₀ t z) (Φ₀ t x) < ε / 2 :=
      isCompact_uIcc.eventually_forall_of_forall_eventually fun t ht ↦ by
        have h₁ : ContinuousAt (uncurry Φ₀ ∘ fun z : V × ℝ ↦ (z.2, z.1)) (x, t) :=
          (hcont t ht).comp_of_eq (continuousAt_snd.prodMk continuousAt_fst) rfl
        have h₂ : ContinuousAt ((fun s ↦ Φ₀ s x) ∘ Prod.snd) (x, t) :=
          (hcx t ht).comp_of_eq continuousAt_snd rfl
        have h : ContinuousAt (fun z : V × ℝ ↦ Φ₀ z.2 z.1 - Φ₀ z.2 x) (x, t) := h₁.sub h₂
        filter_upwards [h.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 2))]
          with z hz
        simpa [dist_eq_norm, sub_self] using hz
    filter_upwards [hy _ hnear, hy _ hU,
      Metric.tendstoUniformlyOn_iff.1 hunif (ε / 2) (by positivity)] with i hi hiU hu t ht
    have h1 := hu (t, y i t) ⟨ht, hiU t ht⟩
    have h2 := hi t ht t ht
    simp only [uncurry_apply_pair] at h1
    rw [Pi.zero_apply, dist_zero_left, ← dist_eq_norm]
    linarith [dist_triangle (Φ i t (y i t)) (Φ₀ t (y i t)) (Φ₀ t x),
      dist_comm (Φ₀ t (y i t)) (Φ i t (y i t))]
  refine tendsto_sub_nhds_zero_iff.1
    ((hunif'.tendsto_intervalIntegral_nhds_zero (μ := μ)).congr' ?_)
  filter_upwards [hint] with i hi
  exact intervalIntegral.integral_sub hi hint₀

/-- If `f` is continuous on `s ×ˢ uIcc a b`, then the interval integral `∫ t in a..b, f x t ∂μ`
is continuous in `x` on `s`. Only the values of `f` on `s ×ˢ uIcc a b` matter, so this applies
for instance on a closed rectangle `[a', b'] ×ˢ [a, b]`, up to its boundary. -/
theorem continuousOn_parametric_intervalIntegral_of_continuousOn {X E : Type*}
    [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure ℝ}
    [IsLocallyFiniteMeasure μ] {f : X → ℝ → E} {s : Set X} {a b : ℝ}
    (hf : ContinuousOn (uncurry f) (s ×ˢ uIcc a b)) :
    ContinuousOn (fun x ↦ ∫ t in a..b, f x t ∂μ) s := by
  intro x₀ hx₀
  have hint : ∀ x ∈ s, IntervalIntegrable (f x) μ a b := fun x hx ↦
    (hf.comp (Continuous.prodMk_right x).continuousOn fun _ ht ↦ ⟨hx, ht⟩).intervalIntegrable
  have hU : TendstoUniformlyOn (fun x t ↦ f x t - f x₀ t) 0 (𝓝[s] x₀) (uIcc a b) := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
    obtain ⟨v, hv, hvf⟩ := isCompact_uIcc.mem_uniformity_of_prod hf hx₀
      (Metric.dist_mem_uniformity hε)
    filter_upwards [hv] with x hx t ht
    simpa [dist_eq_norm, norm_sub_rev] using hvf x hx t ht
  refine tendsto_sub_nhds_zero_iff.mp ((hU.tendsto_intervalIntegral_nhds_zero (μ := μ)).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact intervalIntegral.integral_sub (hint x hx) (hint x₀ hx₀)

/-- **Integrals over shrinking shells vanish.** If `w` is measurable and `η k` tends to `0`,
then the integral of an integrable `f` over the shells `{0 < w < η k}` tends to `0`, by dominated
convergence: the indicator of the `k`th shell tends to `0` at every point. -/
theorem tendsto_setIntegral_preimage_Ioo_zero {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure α} {f : α → F} (hf : Integrable f μ)
    {w : α → ℝ} (hw : Measurable w) {η : ℕ → ℝ} (hηlim : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun k ↦ ∫ x in w ⁻¹' Ioo 0 (η k), f x ∂μ) atTop (𝓝 0) := by
  have hmeas (k : ℕ) : MeasurableSet (w ⁻¹' Ioo 0 (η k)) := hw measurableSet_Ioo
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun x ↦ ‖f x‖)
    (F := fun k x ↦ (w ⁻¹' Ioo 0 (η k)).indicator f x) (f := fun _ ↦ (0 : F))
    (fun k ↦ hf.aestronglyMeasurable.indicator (hmeas k)) hf.norm
    (fun k ↦ .of_forall fun x ↦ norm_indicator_le_norm_self f x) (.of_forall fun x ↦ ?_)
  · simpa only [integral_indicator (hmeas _), integral_zero] using h
  · by_cases hx : 0 < w x
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hηlim.eventually (gt_mem_nhds hx)] with k hk
      exact (indicator_of_notMem (show x ∉ w ⁻¹' Ioo 0 (η k) from fun h' => h'.2.not_gt hk) f).symm
    · refine tendsto_const_nhds.congr fun k => ?_
      exact (indicator_of_notMem (show x ∉ w ⁻¹' Ioo 0 (η k) from fun h' => hx h'.1) f).symm

end TauCeti

open Filter MeasureTheory Topology Set Function Interval in
/-- **Integrals along uniformly convergent paths.** If continuous paths `F i` converge uniformly on
`[[a, b]]` to `f`, then for every jointly continuous integrand `g`, the integrals of
`t ↦ g t (F i t)` over `a..b` converge to the integral of `t ↦ g t (f t)`. -/
theorem TendstoUniformlyOn.tendsto_intervalIntegral_comp {ι β E : Type*} [UniformSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {l : Filter ι} [l.IsCountablyGenerated] {F : ι → ℝ → β} {f : ℝ → β} {g : ℝ → β → E}
    {a b : ℝ} (hg : Continuous (uncurry g)) (hF : ∀ᶠ i in l, ContinuousOn (F i) [[a, b]])
    (h : TendstoUniformlyOn F f l [[a, b]]) :
    Tendsto (fun i ↦ ∫ t in a..b, g t (F i t) ∂μ) l (𝓝 (∫ t in a..b, g t (f t) ∂μ)) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  refine tendsto_intervalIntegral_of_continuousOn
    (hF.mono fun _ hi ↦ hg.comp_continuousOn (continuousOn_id.prodMk hi)) ?_
  exact (isCompact_uIcc.image_of_continuousOn
    (continuousOn_id.prodMk (h.continuousOn hF.frequently)))
    |>.comp_tendstoUniformlyOn (g := uncurry g) (fun _ _ ↦ hg.continuousAt)
      ((TauCeti.tendstoUniformlyOn_const id l _).prodMk_same h)

open Filter MeasureTheory Topology Set Metric in
/-- Excising a shrinking closed ball around a point `ξ` with `(μ.restrict Δ) {ξ} = 0` recovers the
set integral over `Δ` as the radius tends to `0⁺`. -/
theorem MeasureTheory.IntegrableOn.tendsto_integral_sdiff_closedBall_nhdsGT {X E : Type*}
    [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X} {Δ : Set X} {h : X → E}
    (hh : IntegrableOn h Δ μ) {ξ : X} (hξ : (μ.restrict Δ) {ξ} = 0) :
    Tendsto (fun ε ↦ ∫ z in Δ \ closedBall ξ ε, h z ∂μ) (𝓝[>] 0) (𝓝 (∫ z in Δ, h z ∂μ)) := by
  have hcov : AECover (μ.restrict Δ) (𝓝[>] (0 : ℝ)) (fun ε ↦ (closedBall ξ ε)ᶜ) :=
    ⟨by filter_upwards [compl_mem_ae_iff.mpr hξ] with z hz
        filter_upwards [Ioo_mem_nhdsGT (dist_pos.mpr hz)] with ε hε
        simpa [mem_closedBall] using hε.2,
     fun _ ↦ isClosed_closedBall.measurableSet.compl⟩
  simpa only [Measure.restrict_restrict isClosed_closedBall.measurableSet.compl,
    Set.inter_comm, ← Set.sdiff_eq] using hcov.integral_tendsto_of_countably_generated hh


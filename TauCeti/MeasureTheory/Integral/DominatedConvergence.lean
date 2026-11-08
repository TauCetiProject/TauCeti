/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Dominated convergence away from one point

This file packages the common application of dominated convergence in which a parameterized
family is controlled and converges pointwise away from one exceptional point. When that point has
measure zero, the pointwise hypotheses supply the almost-everywhere hypotheses of the dominated
convergence theorem. It also records the convergence of integrals against cutoffs
which equal one on a closed ball and are supported in shrinking larger balls, and against cutoffs
which equal one on balls exhausting a normed space, as well as convergence after removing a
shrinking neighbourhood of zero from an integrable function vanishing at zero, and the convergence
of interval integrals `∫ Φ(t, y_i(t)) dt` of a continuous function along maps `y_i` with values in
a compact set which converge pointwise.

## Main declarations

* `TauCeti.tendsto_integral_mul_of_dominated_away`: dominated convergence for a family multiplied
  by a fixed weight, with domination and convergence away from a null point.
* `TauCeti.tendsto_integral_smul_of_cutoff`: integrals against cutoffs equal to one on
  `closedBall x r` and vanishing off `ball x (r + h)` tend to the integral over `closedBall x r` as
  `h → 0⁺`.
* `TauCeti.tendsto_integral_smul_of_eq_one_ball`: integrals against `[0, 1]`-valued cutoffs equal
  to one on `ball 0 (R i)` with `R i → ∞` tend to the integral over the whole space.
* `TauCeti.tendsto_integral_abs_gt`: removing a shrinking neighbourhood of zero recovers the
  integral of an integrable function vanishing at zero.
* `TauCeti.tendsto_intervalIntegral_comp_of_tendsto`: for continuous `Φ`, the integrals
  `∫_{t₁}^{t₂} Φ(t, y_i(t)) dt` converge when the `y_i` stay in a compact set and converge
  pointwise.
* `TauCeti.tendsto_setIntegral_preimage_Ioo_zero`: integrals of an integrable function over the
  shells `{0 < w < η k}` tend to `0` as `η k` tends to `0`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Topology Set Metric Function

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Dominated convergence away from one point.** Suppose `K i` is eventually a.e.-strongly
measurable, and `K i` is eventually dominated by `K₀` and converges to it away from a point
`x₀` with `μ {x₀} = 0`. If `K₀ * w` is integrable, then the integrals of `K i * w` converge to the
integral of `K₀ * w`. The weight `w` needs no measurability hypothesis: `K₀` is an a.e. limit of
measurable functions, and `K i * w` agrees a.e. with `K i * (K₀ * w / K₀)`, because `K i`
vanishes where `K₀` does.

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
  have hK₀ : AEStronglyMeasurable K₀ μ := by
    obtain ⟨u, hu⟩ := exists_seq_tendsto l
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually hK)
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n ↦ K (u (n + N)))
      (fun n ↦ hN _ (Nat.le_add_left N n)) ?_
    filter_upwards [hae] with x hx
    exact (hlim x hx).comp (hu.comp (tendsto_add_atTop_nat N))
  -- Where `K₀ = 0` the family vanishes, so `K i * w = K i * (K₀ * w / K₀)` a.e.
  have hmeas : ∀ᶠ i in l, AEStronglyMeasurable (fun x ↦ K i x * w x) μ := by
    filter_upwards [hK, hle] with i hi hle'
    refine (hi.mul (hint.aemeasurable.div hK₀.aemeasurable).aestronglyMeasurable).congr ?_
    filter_upwards [hae] with x hx
    by_cases h0 : K₀ x = 0
    · have : K i x = 0 := abs_nonpos_iff.1 (by simpa [h0] using hle' x hx)
      simp [this]
    · change K i x * (K₀ x * w x / K₀ x) = K i x * w x
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
        (f ⁻¹' closedBall x (r + δ)).indicator fun y => ψ h (f y) • g y := by
      ext y
      by_cases hy : y ∈ f ⁻¹' closedBall x (r + δ)
      · rw [indicator_of_mem hy]
      · rw [indicator_of_notMem hy, hψS y hy, zero_smul]
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
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C)
    (Eventually.of_forall fun i ↦ ?_)
    (Eventually.of_forall fun i ↦ Eventually.of_forall fun t ht ↦
      hC _ ⟨uIoc_subset_uIcc ht, hyK i t (uIoc_subset_uIcc ht)⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht ↦ (hΦ.tendsto (t, x t)).comp
      (tendsto_const_nhds.prodMk_nhds (hyx t (uIoc_subset_uIcc ht))))
  exact ((hΦ.comp_continuousOn (continuousOn_id.prodMk (hy i))).aestronglyMeasurable
    measurableSet_uIcc).mono_measure (Measure.restrict_mono uIoc_subset_uIcc le_rfl)

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

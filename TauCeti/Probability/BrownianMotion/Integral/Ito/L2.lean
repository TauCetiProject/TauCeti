/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.Probability.BrownianMotion.Integral.Restriction
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy

/-!
# The L² Brownian Itô integral process

For a Brownian-integrable predictable integrand `H` (`TauCeti.BrownianIntegrable`) and a filtered
pre-Brownian motion `W`, any process satisfying `TauCeti.Probability.IsItoIntegral ℱ P W H I`
agrees almost surely at every time `t` with the finite-horizon predictable L² Brownian integral
`hW.l2Integral t` (`ae_eq_l2Integral_of_isItoIntegral`). This yields mean zero
(`integral_eq_zero_of_isItoIntegral`), the bilinear cross-isometry
(`integral_mul_of_isItoIntegral`), increment `L²` isometry (`eLpNorm_l2Integral_sub_of_le`), and
`L²`-continuity of the finite-horizon integral curve `t ↦ hW.l2Integral t ...`
(`continuous_l2Integral`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal Topology InnerProductSpace

namespace TauCeti.Probability.IsFilteredPreBrownianReal

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- The `L²(P)` distance between an elementary Brownian integral and `hW.l2Integral t` of a
`BrownianIntegrable` integrand equals the time-product `L²` distance between their integrands. -/
theorem eLpNorm_simpleGains_sub_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (t : ℝ≥0) :
    eLpNorm (fun ω ↦ Finance.simpleGains τ n a W t ω -
        hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) ω) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure t).prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hK : MemLp (Function.uncurry (Finance.simpleHolding τ n a)) 2 (ℱ.predictableMeasure P t) :=
    Finance.memLp_simpleHolding_predictableMeasure ha ha₂ t
  exact (eLpNorm_congr_ae ((hW.coeFn_l2Integral_simpleHolding hτ ha t hK).symm.mono
    fun ω hω ↦ by simp only [Pi.sub_apply, hω])).trans
    (hW.eLpNorm_l2Integral_sub t (Finance.isStronglyPredictable_simpleHolding ha)
      hH.isStronglyPredictable hK (hH.memLp_predictableMeasure t))

/-- For a `BrownianIntegrable` integrand, every Itô integral agrees almost surely at every time `t`
with the finite-horizon predictable L² Brownian integral `hW.l2Integral t`. Neither Brownian path
continuity nor progressive measurability of `I` is required. -/
theorem ae_eq_l2Integral_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (t : ℝ≥0) :
    I t =ᵐ[P] hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hKlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  exact hI.ae_eq_of_tendstoInMeasure hW (fun k ↦ (hτ k).monotoneOn) ha
    (tendsto_measure_le_lintegral_enorm_sq_sub
      (fun k ↦ Finance.isStronglyPredictable_simpleHolding (ha k))
      (fun _ ↦ hH.isStronglyPredictable) (hKlim t))
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      ((hKlim t).congr fun k ↦ (hW.eLpNorm_simpleGains_sub_l2Integral (hτ k).monotoneOn (ha k)
        (Finance.memLp_of_bound_stronglyMeasurable (ha k) (hb k)) hH t).symm))

/-- Increment `L²` isometry for the finite-horizon L² Brownian integral: for `s ≤ t`, the `L²(P)`
distance between `hW.l2Integral t` and `hW.l2Integral s` of a `BrownianIntegrable` integrand
equals the `L²` norm of the integrand on `(s, t] × Ω`. -/
theorem eLpNorm_l2Integral_sub_of_le (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) {s t : ℝ≥0} (hst : s ≤ t) :
    eLpNorm ((hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) :
          Ω → ℝ) -
        (hW.l2Integral s ((hH.memLp_predictableMeasure s).toLp (Function.uncurry H)) : Ω → ℝ))
      2 P = eLpNorm (Function.uncurry H) 2 (((timeMeasure t).restrict (Ioc s t)).prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let ft := (hH.memLp_predictableMeasure t).toLp (Function.uncurry H)
  let fs := (hH.memLp_predictableMeasure s).toLp (Function.uncurry H)
  let fsExt := ℱ.predictableMeasureExtendLp P ℝ hst fs
  let k : ℝ≥0 × Ω → ℝ := (Ioc s t ×ˢ (univ : Set Ω)).indicator (Function.uncurry H)
  have hk_pred : StronglyMeasurable[ℱ.predictable] k :=
    hH.isStronglyPredictable.indicator (measurableSet_predictable_Ioc_prod s t MeasurableSet.univ)
  have hmk : MemLp k 2 (ℱ.predictableMeasure P t) :=
    (hH.memLp_predictableMeasure t).indicator
      (measurableSet_predictable_Ioc_prod (𝓕 := ℱ) s t MeasurableSet.univ).nullMeasurableSet
  have hdiff : ft - fsExt = hmk.toLp k := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub ft fsExt, (hH.memLp_predictableMeasure t).coeFn_toLp,
      ℱ.coeFn_predictableMeasureExtendLp_of_ae_eq P (𝕜 := ℝ) hst
        (hH.memLp_predictableMeasure s).coeFn_toLp,
      hmk.coeFn_toLp, ℱ.ae_mem_Ioc_prod_predictableMeasure P t] with ⟨u, ω⟩ hsub h1 h2 hk hu
    rw [hsub, hk, Pi.sub_apply]
    dsimp only [ft, fsExt, fs]
    rw [h1, h2]
    simp only [k, indicator_apply, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true]
    rcases le_or_gt u s with hus | hsu
    · simp [hu.1.1, hus, hus.not_gt]
    · simp [hsu.not_ge, hsu, hu.1.2]
  have hmap : hW.l2Integral t ft - hW.l2Integral s fs = hW.l2Integral t (hmk.toLp k) := by
    rw [← hW.l2Integral_predictableMeasureExtendLp hst fs, ← map_sub, hdiff]
  refine (eLpNorm_congr_ae (Lp.coeFn_sub (hW.l2Integral t ft) (hW.l2Integral s fs)).symm).trans ?_
  rw [hmap, hW.eLpNorm_l2Integral t hk_pred hmk]
  dsimp only [k]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict
    ((measurableSet_Ioc (a := s) (b := t)).prod MeasurableSet.univ).nullMeasurableSet,
    ← Measure.restrict_prod_eq_prod_univ]

/-- The finite-horizon `L²` Brownian integral defines a continuous `L²(P)`-valued curve in time
for every `BrownianIntegrable` integrand. -/
theorem continuous_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) :
    Continuous fun t : ℝ≥0 ↦
      hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  rw [continuous_iff_continuousAt]
  intro t₀
  let F (t : ℝ≥0) : Lp ℝ 2 P :=
    hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))
  let T : ℝ≥0 := t₀ + 1
  let g (t : ℝ≥0) (p : ℝ≥0 × Ω) : ℝ :=
    (Ioc (min t t₀) (max t t₀) ×ˢ (univ : Set Ω)).indicator (Function.uncurry H) p
  have hbound (t : ℝ≥0) (ht : t ≤ T) :
      ‖F t - F t₀‖ₑ ≤ eLpNorm (g t) 2 ((timeMeasure T).prod P) := by
    have hnorm : ‖F t - F t₀‖ₑ = eLpNorm (⇑(F t) - ⇑(F t₀)) 2 P := by
      rw [Lp.eNorm_def]
      exact eLpNorm_congr_ae (Lp.coeFn_sub (F t) (F t₀))
    rw [hnorm]
    rcases le_total t₀ t with ht₀t | htt₀
    · rw [hW.eLpNorm_l2Integral_sub_of_le hH ht₀t]
      have hmeas : ((timeMeasure t).restrict (Ioc t₀ t)).prod P ≤
          ((timeMeasure T).restrict (Ioc t₀ t)).prod P :=
        Measure.prod_mono (Measure.restrict_mono Set.Subset.rfl (timeMeasure_mono ht)) le_rfl
      refine (eLpNorm_mono_measure _ hmeas).trans_eq ?_
      rw [Measure.restrict_prod_eq_prod_univ, ← eLpNorm_indicator_eq_eLpNorm_restrict
        ((measurableSet_Ioc (a := t₀) (b := t)).prod MeasurableSet.univ).nullMeasurableSet]
      simp [g, min_eq_right ht₀t, max_eq_left ht₀t]
    · rw [eLpNorm_sub_comm, hW.eLpNorm_l2Integral_sub_of_le hH htt₀]
      have hmeas : ((timeMeasure t₀).restrict (Ioc t t₀)).prod P ≤
          ((timeMeasure T).restrict (Ioc t t₀)).prod P :=
        Measure.prod_mono
          (Measure.restrict_mono Set.Subset.rfl (timeMeasure_mono (le_self_add : t₀ ≤ T))) le_rfl
      refine (eLpNorm_mono_measure _ hmeas).trans_eq ?_
      rw [Measure.restrict_prod_eq_prod_univ, ← eLpNorm_indicator_eq_eLpNorm_restrict
        ((measurableSet_Ioc (a := t) (b := t₀)).prod MeasurableSet.univ).nullMeasurableSet]
      simp [g, min_eq_left htt₀, max_eq_right htt₀]
  have hzero : timeMeasure T {t₀} = 0 := by
    rw [timeMeasure_apply T (measurableSet_singleton t₀)]
    exact measure_mono_null (by rintro _ ⟨y, ⟨rfl, -⟩, rfl⟩; rfl) Real.volume_singleton
  have hne : ∀ᵐ p : ℝ≥0 × Ω ∂(timeMeasure T).prod P, p.1 ≠ t₀ :=
    Measure.quasiMeasurePreserving_fst.ae
      (ae_iff.mpr (by rw [show {a | ¬a ≠ t₀} = {t₀} from by ext; simp, hzero]))
  have hg_lim : Tendsto (fun t ↦ eLpNorm (g t - 0) 2 ((timeMeasure T).prod P)) (𝓝 t₀) (𝓝 0) := by
    refine TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
      (.of_forall fun t ↦ ((hH.isStronglyPredictable.indicator
        (measurableSet_predictable_Ioc_prod (min t t₀) (max t t₀) MeasurableSet.univ)).mono
        ℱ.predictable_le_prod).aestronglyMeasurable)
      (hH.memLp_timeMeasure T)
      (.of_forall fun t ↦ .of_forall fun p ↦ by
        simp only [Pi.zero_apply, sub_zero, ENNReal.coe_one, one_mul, g]
        exact eNorm_indicator_le_eNorm_self _ p) ?_
    filter_upwards [hne] with ⟨u, ω⟩ hu
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Metric.ball_mem_nhds t₀ (dist_pos.mpr hu)] with t ht
    have hnot : (u, ω) ∉ Ioc (min t t₀) (max t t₀) ×ˢ (univ : Set Ω) := by
      rintro ⟨⟨hmin, hmax⟩, -⟩
      dsimp only at hmin hmax
      simp only [Metric.mem_ball, NNReal.dist_eq] at ht
      rcases le_total t t₀ with htt₀ | ht₀t
      · rw [min_eq_left htt₀] at hmin
        rw [max_eq_right htt₀] at hmax
        rw [abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hmax)), neg_sub] at ht
        rw [abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr htt₀)), neg_sub] at ht
        linarith [show (t : ℝ) < u from hmin]
      · rw [min_eq_right ht₀t] at hmin
        rw [max_eq_left ht₀t] at hmax
        rw [abs_of_pos (sub_pos.mpr (NNReal.coe_lt_coe.mpr hmin))] at ht
        rw [abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr ht₀t))] at ht
        linarith [show (u : ℝ) ≤ t from hmax]
    simp [g, indicator_of_notMem hnot]
  have henorm : Tendsto (fun t ↦ ‖F t - F t₀‖ₑ) (𝓝 t₀) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [sub_zero] using hg_lim)
      (.of_forall fun _ ↦ zero_le)
      (Filter.mem_of_superset (Iic_mem_nhds (lt_add_one t₀)) hbound)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp henorm
  simpa only [Function.comp_def, toReal_eNorm, ENNReal.toReal_zero] using hreal

/-- Any Itô integral of a `BrownianIntegrable` integrand has expectation zero at every time. -/
theorem integral_eq_zero_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (t : ℝ≥0) : ∫ ω, I t ω ∂P = 0 :=
  (integral_congr_ae (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t)).trans
    (hW.integral_l2Integral t _)

/-- **Bilinear Itô cross-isometry (covariance).** For two `BrownianIntegrable` integrands and
their Itô integrals, the expected product at time `t` equals the time-product integral of the
product of the integrands on `(0, t]`. -/
theorem integral_mul_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H₁ H₂ I₁ I₂ : ℝ≥0 → Ω → ℝ}
    (hH₁ : BrownianIntegrable ℱ P H₁) (hH₂ : BrownianIntegrable ℱ P H₂)
    (hI₁ : IsItoIntegral ℱ P W H₁ I₁) (hI₂ : IsItoIntegral ℱ P W H₂ I₂) (t : ℝ≥0) :
    ∫ ω, I₁ t ω * I₂ t ω ∂P = ∫ p, H₁ p.1 p.2 * H₂ p.1 p.2 ∂(timeMeasure t).prod P := by
  let f₁ := (hH₁.memLp_predictableMeasure t).toLp (Function.uncurry H₁)
  let f₂ := (hH₂.memLp_predictableMeasure t).toLp (Function.uncurry H₂)
  calc ∫ ω, I₁ t ω * I₂ t ω ∂P = ⟪hW.l2Integral t f₁, hW.l2Integral t f₂⟫_ℝ := by
        rw [L2.inner_def]
        exact integral_congr_ae ((hW.ae_eq_l2Integral_of_isItoIntegral hH₁ hI₁ t).mp
          ((hW.ae_eq_l2Integral_of_isItoIntegral hH₂ hI₂ t).mono fun _ h2 h1 ↦ by
            simp only [f₁, f₂, RCLike.inner_apply, conj_trivial, h1, h2, mul_comm]))
    _ = ⟪f₁, f₂⟫_ℝ := (hW.l2Integral t).inner_map_map f₁ f₂
    _ = ∫ p, H₁ p.1 p.2 * H₂ p.1 p.2 ∂ℱ.predictableMeasure P t := by
        rw [L2.inner_def]
        exact integral_congr_ae ((hH₁.memLp_predictableMeasure t).coeFn_toLp.mp
          ((hH₂.memLp_predictableMeasure t).coeFn_toLp.mono fun ⟨_, _⟩ h2 h1 ↦ by
            simp only [f₁, f₂, RCLike.inner_apply, conj_trivial, h1, h2,
              Function.uncurry_apply_pair, mul_comm]))
    _ = ∫ p, H₁ p.1 p.2 * H₂ p.1 p.2 ∂(timeMeasure t).prod P :=
        ℱ.integral_predictableMeasure P (hH₁.isStronglyPredictable.mul hH₂.isStronglyPredictable) t

end TauCeti.Probability.IsFilteredPreBrownianReal

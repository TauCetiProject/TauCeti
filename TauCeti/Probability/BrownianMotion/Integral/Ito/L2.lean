/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Deterministic
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.Probability.BrownianMotion.Integral.Restriction
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy

/-!
# The L² Brownian Itô integral process

For a predictable integrand `H` in `L²((timeMeasure t).prod P)` and a filtered pre-Brownian motion
`W`, any process satisfying `TauCeti.Probability.IsItoIntegral ℱ P W H I` agrees almost surely at
time `t` with the finite-horizon predictable L² Brownian integral `hW.l2Integral t`
(`ae_eq_l2Integral_of_memLp`, and globally for `TauCeti.BrownianIntegrable` in
`ae_eq_l2Integral_of_isItoIntegral`). For deterministic `L²(timeMeasure t)` integrands `f`,
`ae_eq_wienerIntegral_of_isItoIntegral` identifies any Itô integral at time `t` with the Wiener
integral `hW.toIsPreBrownianReal.wienerIntegral t (hf.toLp f)`. This also yields mean zero
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

namespace TauCeti.Probability

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- On each finite horizon, a predictable integrand with finite expected square energy can be
approximated arbitrarily closely in `L²((timeMeasure t).prod P)` by a bounded
`ElementaryIntegrand`. -/
theorem exists_elementaryIntegrand_eLpNorm_sub_lt (ℱ : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) [IsFiniteMeasure P] (t : ℝ≥0) {H : ℝ≥0 → Ω → ℝ}
    (hHp : IsStronglyPredictable ℱ H)
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : ElementaryIntegrand ℱ,
      eLpNorm (fun p : ℝ≥0 × Ω ↦ K.toProcess p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure t).prod P) < ε := by
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, herr⟩ :=
    ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P t hHp hH hε
  let K : ElementaryIntegrand ℱ := ElementaryIntegrand.ofSimpleHolding hτ.monotoneOn ha
    fun j hj ↦ ⟨C, fun ω ↦ by simpa [Real.norm_eq_abs] using hb j hj ω⟩
  refine ⟨K, ?_⟩
  simpa only [K, ElementaryIntegrand.toProcess_ofSimpleHolding] using herr

/-- For a predictable integrand in `L²((timeMeasure t).prod P)`, there is a sequence of bounded
`ElementaryIntegrand`s whose represented processes converge to it in
`L²((timeMeasure t).prod P)`. -/
theorem exists_seq_elementaryIntegrand_tendsto_eLpNorm (ℱ : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) [IsFiniteMeasure P] (t : ℝ≥0) {H : ℝ≥0 → Ω → ℝ}
    (hHp : IsStronglyPredictable ℱ H)
    (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    ∃ K : ℕ → ElementaryIntegrand ℱ,
      Tendsto (fun k ↦ eLpNorm
        (fun p : ℝ≥0 × Ω ↦ (K k).toProcess p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure t).prod P)) atTop (𝓝 0) := by
  choose K hK using fun k : ℕ ↦ exists_elementaryIntegrand_eLpNorm_sub_lt ℱ P t hHp hH
    (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top (k + 1)))
  refine ⟨K, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
    (fun _ ↦ zero_le) fun k ↦ (hK k).le⟩

namespace IsFilteredPreBrownianReal

variable {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- The `L²(P)` distance between an elementary Brownian integral and `hW.l2Integral t` of a
predictable integrand in `L²((timeMeasure t).prod P)` equals the time-product `L²` distance between
their integrands. -/
theorem eLpNorm_simpleGains_sub_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) (t : ℝ≥0) {H : ℝ≥0 → Ω → ℝ}
    (hHp : IsStronglyPredictable ℱ H) (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P)) :
    eLpNorm (fun ω ↦ Finance.simpleGains τ n a W t ω -
        hW.l2Integral t
          (((ℱ.memLp_predictableMeasure_iff P hHp t 2).mpr hH).toLp (Function.uncurry H)) ω) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure t).prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hK : MemLp (Function.uncurry (Finance.simpleHolding τ n a)) 2 (ℱ.predictableMeasure P t) :=
    Finance.memLp_simpleHolding_predictableMeasure ha ha₂ t
  exact (eLpNorm_congr_ae ((hW.coeFn_l2Integral_simpleHolding hτ ha t hK).symm.mono
    fun ω hω ↦ by simp only [Pi.sub_apply, hω])).trans
    (hW.eLpNorm_l2Integral_sub t (Finance.isStronglyPredictable_simpleHolding ha)
      hHp hK ((ℱ.memLp_predictableMeasure_iff P hHp t 2).mpr hH))

/-- Fixed-horizon `L²` identification for any predictable integrand in `L²((timeMeasure t).prod P)`:
every Itô integral at time `t` agrees almost surely with `hW.l2Integral t`. -/
theorem ae_eq_l2Integral_of_memLp (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} (hH : MemLp (Function.uncurry H) 2 ((timeMeasure t).prod P))
    (hI : IsItoIntegral ℱ P W H I) :
    I t =ᵐ[P] hW.l2Integral t
      (((ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).mpr hH).toLp
        (Function.uncurry H)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨K, hKlim⟩ := exists_seq_elementaryIntegrand_tendsto_eLpNorm ℱ P t
    hI.isStronglyPredictable hH
  have hlim_sh : Tendsto (fun k ↦ eLpNorm
      (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (K k).dates (K k).n (K k).positions p.1 p.2 -
        H p.1 p.2) 2 ((timeMeasure t).prod P)) atTop (𝓝 0) := by
    simpa only [ElementaryIntegrand.toProcess_eq_simpleHolding] using hKlim
  exact hI.ae_eq_of_tendstoInMeasure hW (fun k ↦ (K k).monotone_dates.monotoneOn _)
    (fun k ↦ (K k).measurable_positions)
    (ElementaryIntegrand.tendsto_measure_le_lintegral_of_tendsto_eLpNorm
      (fun _ ↦ hI.isStronglyPredictable) hKlim)
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (hlim_sh.congr fun k ↦ (hW.eLpNorm_simpleGains_sub_l2Integral
        ((K k).monotone_dates.monotoneOn _) (K k).measurable_positions
        (fun j _ ↦ (K k).memLp_positions P 2 j) t hI.isStronglyPredictable hH).symm))

/-- For a `BrownianIntegrable` integrand, every Itô integral agrees almost surely at every time `t`
with the finite-horizon predictable L² Brownian integral `hW.l2Integral t`. Neither Brownian path
continuity nor progressive measurability of `I` is required. -/
theorem ae_eq_l2Integral_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (t : ℝ≥0) :
    I t =ᵐ[P] hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) :=
  hW.ae_eq_l2Integral_of_memLp (hH.memLp_timeMeasure t) hI

/-- At any time `t`, an Itô integral of a deterministic integrand `f ∈ L²(timeMeasure t)` agrees
almost surely with its Wiener integral `hW.toIsPreBrownianReal.wienerIntegral t (hf.toLp f)`. -/
theorem ae_eq_wienerIntegral_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {f : ℝ≥0 → ℝ} {I : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} (hf : MemLp f 2 (timeMeasure t))
    (hI : IsItoIntegral ℱ P W (fun s _ ↦ f s) I) :
    I t =ᵐ[P] hW.toIsPreBrownianReal.wienerIntegral t (hf.toLp f) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hf_prod : MemLp (Function.uncurry fun s (_ : Ω) ↦ f s) 2 ((timeMeasure t).prod P) :=
    (hf.comp_measurePreserving (measurePreserving_fst (μ := timeMeasure t) (ν := P))).ae_eq
      (.of_forall fun _ ↦ rfl)
  have hfp := (ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).mpr hf_prod
  have hl2 : hfp.toLp (Function.uncurry fun s (_ : Ω) ↦ f s) =
      (hf.comp_measurePreserving (ℱ.measurePreserving_fst_predictableMeasure P t)).toLp
        (fun p : ℝ≥0 × Ω ↦ f p.1) :=
    Lp.ext (hfp.coeFn_toLp.trans
      ((hf.comp_measurePreserving
        (ℱ.measurePreserving_fst_predictableMeasure P t)).coeFn_toLp.mono fun _ h ↦ h.symm))
  have hcomp := (Lp.toLp_compMeasurePreserving hf
    (ℱ.measurePreserving_fst_predictableMeasure P t)).symm
  dsimp only [Function.comp_def] at hcomp
  refine (hW.ae_eq_l2Integral_of_memLp hf_prod hI).trans ?_
  rw [hl2, hcomp, hW.l2Integral_compMeasurePreserving_fst t (hf.toLp f)]

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

/-- Bound the `L²(P)` distance between `hW.l2Integral t` and `hW.l2Integral s` (for `s ≤ t ≤ T`)
by the `L²` norm of the `(s, t]` indicator of `H` at the fixed horizon `T`. -/
private theorem eNorm_l2Integral_sub_le_indicator_of_le (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) {s t T : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) :
    ‖hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) -
      hW.l2Integral s ((hH.memLp_predictableMeasure s).toLp (Function.uncurry H))‖ₑ ≤
      eLpNorm ((Ioc s t ×ˢ (univ : Set Ω)).indicator (Function.uncurry H)) 2
        ((timeMeasure T).prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let Ft := hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))
  let Fs := hW.l2Integral s ((hH.memLp_predictableMeasure s).toLp (Function.uncurry H))
  have hnorm : ‖Ft - Fs‖ₑ = eLpNorm (⇑Ft - ⇑Fs) 2 P := by
    rw [Lp.eNorm_def]
    exact eLpNorm_congr_ae (Lp.coeFn_sub Ft Fs)
  rw [hnorm, hW.eLpNorm_l2Integral_sub_of_le hH hst]
  have hmeas : ((timeMeasure t).restrict (Ioc s t)).prod P ≤
      ((timeMeasure T).restrict (Ioc s t)).prod P :=
    Measure.prod_mono (Measure.restrict_mono Set.Subset.rfl (timeMeasure_mono htT)) le_rfl
  refine (eLpNorm_mono_measure _ hmeas).trans_eq ?_
  rw [Measure.restrict_prod_eq_prod_univ, ← eLpNorm_indicator_eq_eLpNorm_restrict
    ((measurableSet_Ioc (a := s) (b := t)).prod MeasurableSet.univ).nullMeasurableSet]

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
  -- Step 1: for `t ≤ T`, bound `‖F t - F t₀‖ₑ` symmetrically by `‖g t‖₂` on `(0, T] × Ω`.
  have hbound (t : ℝ≥0) (ht : t ≤ T) :
      ‖F t - F t₀‖ₑ ≤ eLpNorm (g t) 2 ((timeMeasure T).prod P) := by
    rcases le_total t₀ t with ht₀t | htt₀
    · simpa only [g, min_eq_right ht₀t, max_eq_left ht₀t] using
        hW.eNorm_l2Integral_sub_le_indicator_of_le hH ht₀t ht
    · simpa only [g, eNorm_sub_rev, min_eq_left htt₀, max_eq_right htt₀] using
        hW.eNorm_l2Integral_sub_le_indicator_of_le hH htt₀ le_self_add
  -- Step 2: since `timeMeasure T {t₀} = 0`, `g t → 0` a.e. and hence in `L²`.
  have hne_time : ∀ᵐ u ∂timeMeasure T, u ≠ t₀ :=
    ae_iff.mpr (by simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, timeMeasure_singleton])
  have hne : ∀ᵐ p : ℝ≥0 × Ω ∂(timeMeasure T).prod P, p.1 ≠ t₀ :=
    Measure.quasiMeasurePreserving_fst.ae hne_time
  have hexcl (u : ℝ≥0) (hu : u ≠ t₀) : ∀ᶠ t in 𝓝 t₀, u ∉ Ioc (min t t₀) (max t t₀) := by
    rcases lt_or_gt_of_ne hu with hut₀ | ht₀u
    · exact (eventually_gt_nhds hut₀).mono fun t ht h ↦ h.1.not_ge (le_min ht.le hut₀.le)
    · exact (eventually_lt_nhds ht₀u).mono fun t ht h ↦ h.2.not_gt (max_lt ht ht₀u)
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
    refine tendsto_const_nhds.congr' ((hexcl u hu).mono fun t ht ↦ ?_)
    have hnot : (u, ω) ∉ Ioc (min t t₀) (max t t₀) ×ˢ (univ : Set Ω) := fun h ↦ ht h.1
    simp [g, indicator_of_notMem hnot]
  -- Step 3: squeeze `‖F t - F t₀‖ₑ → 0` and pass to `ContinuousAt`.
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

end IsFilteredPreBrownianReal

end TauCeti.Probability

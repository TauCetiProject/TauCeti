/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
public import Mathlib.Probability.Martingale.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Process.ElementaryDensity

/-!
# The square-integrable Itô integral process and Itô's isometry

For an integrand `H` in the expected-square-energy domain `TauCeti.BrownianIntegrable ℱ P H`, this
file bridges `TauCeti.IsItoIntegral` with the terminal-time Hilbert-space isometry
`IsFilteredPreBrownianReal.l2Integral` and constructs a predictable almost surely continuous
martingale Itô integral process on raw filtrations:

* `IsItoIntegral.ae_eq_l2Integral`: against a filtered pre-Brownian motion `W`, any Itô integral
  `I` of `H` agrees almost surely at each horizon `t` with `hW.l2Integral t`.
* `IsItoIntegral.integral_eq_zero`, `IsItoIntegral.integral_mul`, `IsItoIntegral.integral_sq`:
  zero expectation, cross-covariance identity, and Itô's `L²` isometry, without requiring path
  continuity of `W` or adaptation of `I`.
* `IsItoIntegral.martingale`: any strongly adapted Itô integral of a `BrownianIntegrable`
  integrand against a filtered pre-Brownian motion is a true `L²` martingale.
* `BrownianIntegrable.exists_isItoIntegral`: against a filtered pre-Brownian motion `W` with almost
  surely continuous paths, every `BrownianIntegrable` integrand admits a predictable almost surely
  continuous martingale Itô integral.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B–C.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal InnerProductSpace Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H K I J : ℝ≥0 → Ω → ℝ}

/-- Every `BrownianIntegrable` integrand belongs to `L²` of the finite-horizon predictable measure
at each deterministic horizon. -/
theorem BrownianIntegrable.memLp_predictableMeasure (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    MemLp (Function.uncurry H) 2 (ℱ.predictableMeasure P t) := by
  refine (ℱ.memLp_predictableMeasure_iff P hH.isStronglyPredictable t 2).2 ?_
  simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using hH.memLp t

private theorem coeFn_sum_smul_indicatorConstLp_Ioc_prod [IsProbabilityMeasure P]
    {k : ℕ} (c : Fin k → ℝ) (l u : Fin k → ℝ≥0) (A : Fin k → Set Ω)
    (hA : ∀ i, MeasurableSet[ℱ (l i)] (A i)) (T : ℝ≥0) :
    ⇑(∑ i : Fin k, c i • indicatorConstLp (μ := ℱ.predictableMeasure P T) 2
      (measurableSet_predictable_Ioc_prod (l i) (u i) (hA i)) (measure_ne_top _ _) (1 : ℝ))
      =ᵐ[ℱ.predictableMeasure P T]
        fun p ↦ ∑ i : Fin k, (Ioc (l i) (u i)).indicator
          (fun _ ↦ c i * (A i).indicator (fun _ ↦ (1 : ℝ)) p.2) p.1 := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hcoe := Lp.coeFn_finsetSum (s := Finset.univ) fun i : Fin k ↦ c i •
    indicatorConstLp (μ := ℱ.predictableMeasure P T) 2
      (measurableSet_predictable_Ioc_prod (l i) (u i) (hA i)) (measure_ne_top _ _) (1 : ℝ)
  have hterms (i : Fin k) :
      ⇑(c i • indicatorConstLp (μ := ℱ.predictableMeasure P T) 2
        (measurableSet_predictable_Ioc_prod (l i) (u i) (hA i)) (measure_ne_top _ _) (1 : ℝ))
        =ᵐ[ℱ.predictableMeasure P T] fun p ↦ (Ioc (l i) (u i)).indicator
          (fun _ ↦ c i * (A i).indicator (fun _ ↦ (1 : ℝ)) p.2) p.1 := by
    filter_upwards [Lp.coeFn_smul (c i) (indicatorConstLp (μ := ℱ.predictableMeasure P T) 2
        (measurableSet_predictable_Ioc_prod (l i) (u i) (hA i)) (measure_ne_top _ _) (1 : ℝ)),
      indicatorConstLp_coeFn (μ := ℱ.predictableMeasure P T) (p := 2)
        (hs := measurableSet_predictable_Ioc_prod (l i) (u i) (hA i))
        (hμs := measure_ne_top _ _) (c := (1 : ℝ))] with p hp hq
    rw [hp, Pi.smul_apply, smul_eq_mul, hq]
    by_cases ht : p.1 ∈ Ioc (l i) (u i) <;> by_cases hω : p.2 ∈ A i <;> simp [ht, hω]
  filter_upwards [hcoe.trans (eventuallyEq_sum fun i _ ↦ hterms i)] with p hp
  simpa only [Finset.sum_apply] using hp

private theorem coeFn_l2Integral_sum_smul_indicatorConstLp_Ioc_prod
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    {k : ℕ} (c : Fin k → ℝ) (l u : Fin k → ℝ≥0) (A : Fin k → Set Ω)
    (hA : ∀ i, MeasurableSet[ℱ (l i)] (A i)) (T : ℝ≥0) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    ⇑(hW.l2Integral T (∑ i : Fin k, c i • indicatorConstLp (μ := ℱ.predictableMeasure P T) 2
      (measurableSet_predictable_Ioc_prod (l i) (u i) (hA i)) (measure_ne_top _ _) (1 : ℝ)))
      =ᵐ[P] fun ω ↦ ∑ i : Fin k, if l i ≤ u i then
        (c i * (A i).indicator (fun _ ↦ (1 : ℝ)) ω) *
          (W (min (u i) T) ω - W (min (l i) T) ω) else 0 := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  rw [map_sum]
  have hcoe := Lp.coeFn_finsetSum (s := Finset.univ) fun i : Fin k ↦ hW.l2Integral T
    (c i • indicatorConstLp (μ := ℱ.predictableMeasure P T) 2
      (measurableSet_predictable_Ioc_prod (l i) (u i) (hA i)) (measure_ne_top _ _) (1 : ℝ))
  have hterms (i : Fin k) :
      ⇑(hW.l2Integral T (c i • indicatorConstLp (μ := ℱ.predictableMeasure P T) 2
        (measurableSet_predictable_Ioc_prod (l i) (u i) (hA i)) (measure_ne_top _ _) (1 : ℝ)))
        =ᵐ[P] fun ω ↦ if l i ≤ u i then
          (c i * (A i).indicator (fun _ ↦ (1 : ℝ)) ω) *
            (W (min (u i) T) ω - W (min (l i) T) ω) else 0 := by
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul (c i) (hW.l2Integral T (indicatorConstLp
        (μ := ℱ.predictableMeasure P T) 2
        (measurableSet_predictable_Ioc_prod (l i) (u i) (hA i)) (measure_ne_top _ _) (1 : ℝ))),
      hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod T (l i) (u i) (hA i) 1] with ω hsm hrect
    have hsub : W (max (l i) (min (u i) T)) ω - W (l i) ω =
        if l i ≤ u i then W (min (u i) T) ω - W (min (l i) T) ω else 0 := by
      by_cases hlu : l i ≤ u i
      · rw [ite_eq_left hlu]
        rcases le_total (l i) T with hlT | hTl
        · rw [min_eq_left hlT, max_eq_right (le_min hlu hlT)]
        · rw [min_eq_right hTl, min_eq_right (hTl.trans hlu), max_eq_left hTl, sub_self, sub_self]
      · rw [ite_eq_right hlu, max_eq_left ((min_le_left (u i) T).trans (le_of_not_ge hlu)),
          sub_self]
    rw [hsm, Pi.smul_apply, smul_eq_mul, hrect, hsub]
    split_ifs <;> simp [mul_assoc]
  filter_upwards [hcoe.trans (eventuallyEq_sum fun i _ ↦ hterms i)] with ω hω
  simpa only [Finset.sum_apply] using hω

private theorem exists_simpleHolding_ae_eq_l2Integral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P) (M : ℝ≥0)
    {g : Lp ℝ 2 (ℱ.predictableMeasure P M)}
    (hg : letI := (hW.hasLaw_eval 0).isProbabilityMeasure
      g ∈ Submodule.span ℝ {v : Lp ℝ 2 (ℱ.predictableMeasure P M) |
        ∃ (s t : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[ℱ s] A),
          v = indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
            (measure_ne_top _ _) 1}) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    ∃ (n : ℕ) (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (C : ℝ),
      StrictMonoOn τ (Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) ∧
      (∀ j < n, ∀ ω, ‖a j ω‖ ≤ C) ∧
      (fun p ↦ Finance.simpleHolding τ n a p.1 p.2) =ᵐ[ℱ.predictableMeasure P M] g ∧
      ∀ T : ℝ≥0, ∃ gT : Lp ℝ 2 (ℱ.predictableMeasure P T),
        ((fun p ↦ Finance.simpleHolding τ n a p.1 p.2) =ᵐ[ℱ.predictableMeasure P T] gT) ∧
        Finance.simpleGains τ n a W T =ᵐ[P] hW.l2Integral T gT := by
  classical
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  obtain ⟨k, c, v, hv⟩ := Submodule.mem_span_set'.mp hg
  choose l u A hA heq using fun i : Fin k ↦ (v i).property
  let b (i : Fin k) (ω : Ω) : ℝ := c i * (A i).indicator (fun _ ↦ 1) ω
  have hb (i : Fin k) : StronglyMeasurable[ℱ (l i)] (b i) :=
    (stronglyMeasurable_const.indicator (hA i)).const_mul (c i)
  obtain ⟨n, τ, a, -, hτ, ha, hbound, hhold, hgains⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sum ℱ Finset.univ l u b (fun i _ ↦ hb i)
  have hhold_ae (T : ℝ≥0) :
      (fun p ↦ Finance.simpleHolding τ n a p.1 p.2) =ᵐ[ℱ.predictableMeasure P T]
        ⇑(∑ i : Fin k, c i • indicatorConstLp (μ := ℱ.predictableMeasure P T) 2
          (measurableSet_predictable_Ioc_prod (l i) (u i) (hA i)) (measure_ne_top _ _) (1 : ℝ)) :=
    (coeFn_sum_smul_indicatorConstLp_Ioc_prod c l u A hA T).mono fun p hp ↦
      (hhold p.1 p.2).trans hp.symm
  refine ⟨n, τ, a, ∑ i, |c i|, hτ, ha, ?_, ?_, fun T ↦ ?_⟩
  · intro j hj ω
    refine (hbound j hj ω).trans (sum_le_sum fun i _ ↦ ?_)
    by_cases hω : ω ∈ A i <;> simp [b, hω]
  · convert hhold_ae M using 2
    rw [← hv]
    congr 1
    exact sum_congr rfl fun i _ ↦ by rw [heq i]
  · refine ⟨_, hhold_ae T, ?_⟩
    exact (coeFn_l2Integral_sum_smul_indicatorConstLp_Ioc_prod hW c l u A hA T).mono
      fun ω hω ↦ (hgains W T ω).trans hω.symm

private theorem exists_simpleHolding_eLpNorm_lt
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) (m : ℕ) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    ∃ (n : ℕ) (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (C : ℝ),
      StrictMonoOn τ (Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) ∧
      (∀ j < n, ∀ ω, ‖a j ω‖ ≤ C) ∧
      eLpNorm (fun p ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
        ((Probability.timeMeasure m).prod P) < (m : ℝ≥0∞)⁻¹ ∧
      ∀ T : ℝ≥0, ∃ gT : Lp ℝ 2 (ℱ.predictableMeasure P T),
        ((fun p ↦ Finance.simpleHolding τ n a p.1 p.2) =ᵐ[ℱ.predictableMeasure P T] gT) ∧
        Finance.simpleGains τ n a W T =ᵐ[P] hW.l2Integral T gT := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let S : Submodule ℝ (Lp ℝ 2 (ℱ.predictableMeasure P m)) := Submodule.span ℝ
    {v | ∃ (s t : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[ℱ s] A),
      v = indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) 1}
  have hdense := ℱ.topologicalClosure_span_indicatorConstLp_Ioc_prod_eq_top
    (ℱ.predictableMeasure P m) (fun _ _ _ _ ↦ measure_ne_top _ _)
    (ℱ.predictableMeasure_singleton_zero_prod P m MeasurableSet.univ)
  have hmem : (hH.memLp_predictableMeasure m).toLp (Function.uncurry H) ∈
      closure (S : Set (Lp ℝ 2 (ℱ.predictableMeasure P m))) := by
    rw [← S.topologicalClosure_coe, hdense]
    trivial
  obtain ⟨g, hg, hdist⟩ := EMetric.mem_closure_iff.mp hmem (m : ℝ≥0∞)⁻¹
    (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top m))
  obtain ⟨n, τ, a, C, hτ, ha, hb, heq, hT⟩ := exists_simpleHolding_ae_eq_l2Integral hW m hg
  refine ⟨n, τ, a, C, hτ, ha, hb, ?_, hT⟩
  have hs : StronglyMeasurable[ℱ.predictable]
      (fun p ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) :=
    (Finance.isStronglyPredictable_simpleHolding ha).sub hH.isStronglyPredictable
  rw [← eLpNorm_trim ℱ.predictable_le_prod hs, ← ℱ.predictableMeasure_def]
  have hcongr : eLpNorm (fun p ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
      (ℱ.predictableMeasure P m) = eLpNorm
        (⇑g - ⇑((hH.memLp_predictableMeasure m).toLp (Function.uncurry H))) 2
        (ℱ.predictableMeasure P m) :=
    eLpNorm_congr_ae (heq.sub (hH.memLp_predictableMeasure m).coeFn_toLp.symm)
  rw [hcongr, ← Lp.edist_def, edist_comm]
  exact hdist

private theorem exists_seq_simpleHolding_tendsto_l2Integral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ m, StrictMonoOn (τ m) (Iic (n m))) ∧
      (∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)) ∧
      (∀ m j, j < n m → ∀ ω, ‖a m j ω‖ ≤ C m) ∧
      (∀ T : ℝ≥0, Tendsto (fun m ↦ eLpNorm
        (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
          ((Probability.timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      ∀ T : ℝ≥0, Tendsto (fun m ↦ eLpNorm
        (Finance.simpleGains (τ m) (n m) (a m) W T -
          ⇑(hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)))) 2 P)
        atTop (𝓝 0) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  choose n τ a C hτ ha hb herr hgains using exists_simpleHolding_eLpNorm_lt hW hH
  have hlim_hold (T : ℝ≥0) : Tendsto (fun m ↦ eLpNorm
      (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
        ((Probability.timeMeasure T).prod P)) atTop (𝓝 0) := by
    obtain ⟨N, hN⟩ := exists_nat_ge T
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [eventually_ge_atTop N] with m hm
    have hTm : T ≤ (m : ℝ≥0) := hN.trans (by exact_mod_cast hm)
    have hle : (Probability.timeMeasure T).prod P ≤ (Probability.timeMeasure m).prod P := by
      rw [Probability.timeMeasure_def, Probability.timeMeasure_def]
      exact Measure.prod_mono (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right hTm)) le_rfl
    exact (eLpNorm_mono_measure _ hle).trans (herr m).le
  refine ⟨n, τ, a, C, hτ, ha, hb, hlim_hold, fun T ↦ ?_⟩
  choose gT hgT_hold hgT_gains using fun m ↦ hgains m T
  let fT := (hH.memLp_predictableMeasure T).toLp (Function.uncurry H)
  have hgT_lim : Tendsto gT atTop (𝓝 fT) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm' gT fT).2 ((hlim_hold T).congr fun m ↦ ?_)
    have hs : StronglyMeasurable[ℱ.predictable]
        (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) :=
      (Finance.isStronglyPredictable_simpleHolding (ha m)).sub hH.isStronglyPredictable
    rw [← eLpNorm_trim ℱ.predictable_le_prod hs, ← ℱ.predictableMeasure_def]
    exact eLpNorm_congr_ae ((hgT_hold m).sub (hH.memLp_predictableMeasure T).coeFn_toLp.symm)
  have hmap_lim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun m ↦ hW.l2Integral T (gT m)) (hW.l2Integral T fT)).1
      ((hW.l2Integral T).continuous.tendsto fT |>.comp hgT_lim)
  exact hmap_lim.congr fun m ↦
    eLpNorm_congr_ae ((hgT_gains m).symm.sub EventuallyEq.rfl)

private theorem tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm [SFinite P] {t : ℝ≥0}
    {n : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (ha : ∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j))
    (hH : IsStronglyPredictable ℱ H)
    (hlim : Tendsto (fun m ↦ eLpNorm
      (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
        ((Probability.timeMeasure t).prod P)) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
  let E (m : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
      ∂Probability.timeMeasure t
  have hmeas (m : ℕ) : Measurable
      (fun p : ℝ≥0 × Ω ↦ ‖Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2‖ₑ ^ 2) :=
    (((Finance.isStronglyPredictable_simpleHolding (ha m)).sub hH).mono
      ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
  have hint_lim : Tendsto (fun m ↦ ∫⁻ ω, E m ω ∂P) atTop (𝓝 0) := by
    have hsq : Tendsto (fun m ↦ eLpNorm
        (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
          ((Probability.timeMeasure t).prod P) ^ 2) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.pow (n := 2) hlim
    refine hsq.congr fun m ↦ ?_
    have hpow := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      (((Finance.isStronglyPredictable_simpleHolding (ha m)).sub hH).mono
        ℱ.predictable_le_prod).aestronglyMeasurable (μ := (Probability.timeMeasure t).prod P)
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] at hpow
    refine hpow.trans ?_
    exact (lintegral_prod _ (hmeas m).aemeasurable).trans
      (lintegral_lintegral_swap (hmeas m).aemeasurable)
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hint_lim
      (fun _ ↦ zero_le) fun m ↦ ?_
    have hsub : {ω | ∞ ≤ E m ω} ⊆ {ω | 1 ≤ E m ω} := fun ω hω ↦
      (le_top : (1 : ℝ≥0∞) ≤ ∞).trans hω
    refine (measure_mono hsub).trans ?_
    simpa only [one_mul] using mul_meas_ge_le_lintegral (hmeas m).lintegral_prod_left' 1
  · have hdiv : Tendsto (fun m ↦ (∫⁻ ω, E m ω ∂P) / ε) atTop (𝓝 0) := by
      simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hint_lim (.inr hε.ne')
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
      (fun _ ↦ zero_le) fun m ↦ ?_
    rw [ENNReal.le_div_iff_mul_le (.inl hε.ne') (.inl hεtop), mul_comm]
    exact mul_meas_ge_le_lintegral (hmeas m).lintegral_prod_left' ε

namespace IsItoIntegral

/-- Against a filtered pre-Brownian motion, every Itô integral of a `BrownianIntegrable` integrand
agrees almost surely at each horizon `t` with the terminal-time predictable `L²` integral
`hW.l2Integral t`. Neither path continuity of `W` nor adaptation of `I` is needed. -/
theorem ae_eq_l2Integral (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    I t =ᵐ[P] hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, -, hτ, ha, -, hhold, hgains⟩ :=
    exists_seq_simpleHolding_tendsto_l2Integral hW hH
  have h1 := hI.tendstoInMeasure_simpleGains hW (fun m ↦ (hτ m).monotoneOn) ha fun ε hε ↦
    tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm ha hH.isStronglyPredictable (hhold t) hε
  have h2 := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hgains t)
  exact tendstoInMeasure_ae_unique h1 h2

/-- Every Itô integral of a `BrownianIntegrable` integrand against a filtered pre-Brownian motion
is square-integrable at each horizon. -/
theorem memLp_two (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    MemLp (I t) 2 P :=
  (Lp.memLp _).ae_eq (hI.ae_eq_l2Integral hW hH t).symm

/-- Every Itô integral of a `BrownianIntegrable` integrand against a filtered pre-Brownian motion
has expectation zero at each horizon. -/
theorem integral_eq_zero (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    ∫ ω, I t ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral hW hH t)).trans (hW.integral_l2Integral t _)

/-- **Itô's covariance identity.** Against a filtered pre-Brownian motion, the inner product of
two Itô integrals of `BrownianIntegrable` integrands at horizon `t` equals the time-product
integral of the product of their integrands on `(0, t] × Ω`. -/
theorem integral_mul (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K) (t : ℝ≥0) :
    ∫ ω, I t ω * J t ω ∂P =
      ∫ p, H p.1 p.2 * K p.1 p.2 ∂(Probability.timeMeasure t).prod P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let fH := (hH.memLp_predictableMeasure t).toLp (Function.uncurry H)
  let fK := (hK.memLp_predictableMeasure t).toLp (Function.uncurry K)
  have hlhs : ∫ ω, I t ω * J t ω ∂P = ⟪hW.l2Integral t fH, hW.l2Integral t fK⟫_ℝ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hI.ae_eq_l2Integral hW hH t, hJ.ae_eq_l2Integral hW hK t] with ω hIω hJω
    simp [fH, fK, hIω, hJω, mul_comm]
  rw [hlhs, (hW.l2Integral t).inner_map_map, L2.inner_def]
  have hrhs : ∫ p, ⟪fH p, fK p⟫_ℝ ∂ℱ.predictableMeasure P t =
      ∫ p, H p.1 p.2 * K p.1 p.2 ∂ℱ.predictableMeasure P t := by
    refine integral_congr_ae ?_
    filter_upwards [(hH.memLp_predictableMeasure t).coeFn_toLp,
      (hK.memLp_predictableMeasure t).coeFn_toLp] with p hpH hpK
    simp [fH, fK, hpH, hpK, Function.uncurry, mul_comm]
  exact hrhs.trans
    (ℱ.integral_predictableMeasure P (hH.isStronglyPredictable.mul hK.isStronglyPredictable) t)

/-- **Itô's `L²` isometry.** Against a filtered pre-Brownian motion, the second moment of an Itô
integral of a `BrownianIntegrable` integrand at horizon `t` equals its expected square energy on
`(0, t] × Ω`. -/
theorem integral_sq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(Probability.timeMeasure t).prod P := by
  simpa only [sq] using hI.integral_mul hW hI hH hH t

/-- Against a filtered pre-Brownian motion, any strongly adapted Itô integral of a
`BrownianIntegrable` integrand is a true martingale on the raw filtration. -/
theorem martingale (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hH : BrownianIntegrable ℱ P H)
    (hAdapt : StronglyAdapted ℱ I) :
    Martingale I ℱ P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, hτ, ha, hb, -, hgains⟩ :=
    exists_seq_simpleHolding_tendsto_l2Integral hW hH
  have hM (m : ℕ) : Martingale (Finance.simpleGains (τ m) (n m) (a m) W) ℱ P :=
    hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩
  refine martingale_of_tendsto_eLpNorm_one hM hAdapt fun t ↦ ?_
  refine MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≤ 2) ?_
  refine (hgains t).congr fun m ↦ ?_
  exact eLpNorm_congr_ae (EventuallyEq.rfl.sub (hI.ae_eq_l2Integral hW hH t).symm)

end IsItoIntegral

/-- **Existence of the `L²` Brownian Itô integral process.** Against a filtered pre-Brownian
motion `W` with almost surely continuous paths, every `BrownianIntegrable` integrand admits a
predictable almost surely continuous martingale Itô integral on the raw filtration. -/
theorem BrownianIntegrable.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Martingale I ℱ P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, hτ, ha, hb, hhold, hgains⟩ :=
    exists_seq_simpleHolding_tendsto_l2Integral hW hH
  let M (m : ℕ) := Finance.simpleGains (τ m) (n m) (a m) W
  have hM (m : ℕ) : Martingale (M m) ℱ P :=
    hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩
  have hcM (m : ℕ) : ∀ᵐ ω ∂P, Continuous (fun t ↦ M m t ω) :=
    (IsItoIntegral.simpleGains hcont (hτ m).monotoneOn (ha m)).ae_continuous
  have hmem (m : ℕ) (t : ℝ≥0) : MemLp (M m t) 2 P := by
    have hdef : M m t = fun ω ↦ ∑ j ∈ range (n m),
        a m j ω * (W (min (τ m (j + 1)) t) ω - W (min (τ m j) t) ω) :=
      funext (Finance.simpleGains_def (τ m) (n m) (a m) W t)
    rw [hdef]
    exact hW.memLp_sum_mul_sub_min (range (n m))
      (fun j hj ↦ (hτ m).monotoneOn (mem_range.1 hj).le (mem_range.1 hj) (Nat.le_succ j))
      (fun j hj ↦ ha m j (mem_range.1 hj))
      (fun j hj ↦ MemLp.of_bound ((ha m j (mem_range.1 hj)).mono (ℱ.le _)).aestronglyMeasurable
        (C m) (.of_forall (hb m j (mem_range.1 hj)))) t
  have hcau (t : ℝ≥0) : CauchySeq (fun m ↦ (hmem m t).toLp (M m t)) := by
    let g := hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))
    refine Tendsto.cauchySeq (x := (Lp.memLp g).toLp g) ?_
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun m ↦ M m t) (fun m ↦ hmem m t)
      g (Lp.memLp g)).2 (hgains t)
  obtain ⟨I, hImart, hIpred, hIlim, _, _, _, hIpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp (p := 2) hM hcM hmem hcau
  refine ⟨I, ⟨hH.isStronglyPredictable, Filter.Eventually.mono hIpath fun _ h ↦ h.1,
    fun t ↦ ⟨n, τ, a, fun m ↦ (hτ m).monotoneOn, ha, fun ε hε ↦
      tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm ha hH.isStronglyPredictable
        (hhold t) hε,
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hIlim t).2⟩⟩,
    hIpred, hImart⟩

end TauCeti

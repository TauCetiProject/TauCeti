/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.LargeDeviations.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Separation.Regular

/-!
# The rate function of a large deviation principle

A large deviation principle determines its rate function: in a regular space two lower
semicontinuous rate functions for the same family of measures coincide. For probability
measures, a good rate function vanishes somewhere. Outside any open set containing all of its
zeros the measures decay exponentially fast at the speed of the principle, so they concentrate on
the zero set. This is how a large deviation principle with a rate function having a unique zero
yields a law of large numbers, for example convergence of empirical spectral measures to an
equilibrium measure.

## Main results

* `TauCeti.Probability.HasLDP.eventually_pos`: the speed of a large deviation principle is
  eventually positive.
* `TauCeti.Probability.HasLDP.unique`: uniqueness of the rate function in a regular space.
* `TauCeti.Probability.HasLDP.exists_eq_zero`: for probability measures, a good rate function has
  a zero.
* `TauCeti.Probability.HasLDP.exists_eventually_measure_compl_le`: exponential decay of the
  measures off an open neighbourhood of the zero set.
* `TauCeti.Probability.HasLDP.tendsto_measure_compl`: the measures of the complement of such a
  neighbourhood tend to `0`.

## References

* A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Springer
  (1998), §1.2 and Lemma 4.1.4.
-/

public section

open Filter Topology MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  {l : Filter ι} {ε : ι → ℝ≥0} {μ : ι → Measure X} {I J : X → ℝ≥0∞}

/-- A large deviation principle forces the speed to be eventually positive: at a zero speed the
empty set would have rate `0` instead of `⊥`. -/
theorem HasLDP.eventually_pos (h : HasLDP l ε μ I) : ∀ᶠ i in l, 0 < ε i := by
  have hbot := h.upper_bound ∅ isClosed_empty
  simp only [measure_empty, ENNReal.log_zero, mem_empty_iff_false, iInf_false, iInf_top,
    EReal.coe_ennreal_top, EReal.neg_top] at hbot
  filter_upwards [eventually_lt_of_limsup_lt (hbot.trans_lt EReal.bot_lt_zero)] with i hi
  refine pos_iff_ne_zero.2 fun h0 => ?_
  simp [h0] at hi

/-- In a regular space, a rate function of one large deviation principle bounds that of another
for the same family from below. -/
private theorem HasLDP.le_of_hasLDP [RegularSpace X] [l.NeBot] (hI : HasLDP l ε μ I)
    (hJ : HasLDP l ε μ J) (x : X) : J x ≤ I x := by
  refine le_of_forall_lt_imp_le_of_dense fun a ha => ?_
  -- A closed neighbourhood of `x` on which `J > a`.
  obtain ⟨C, hCx, hCc, hCJ⟩ := exists_mem_nhds_isClosed_subset
    ((hJ.lowerSemicontinuous.isOpen_preimage a).mem_nhds ha)
  have hrate : -(I x : EReal) ≤ -((⨅ y ∈ C, J y : ℝ≥0∞) : EReal) :=
    calc -(I x : EReal)
        ≤ -((⨅ y ∈ interior C, I y : ℝ≥0∞) : EReal) :=
          EReal.neg_le_neg_iff.2 <| EReal.coe_ennreal_le_coe_ennreal_iff.2 <|
            biInf_le _ (mem_interior_iff_mem_nhds.2 hCx)
      _ ≤ liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i (interior C))) l :=
          hI.lower_bound _ isOpen_interior
      _ ≤ limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i C)) l :=
          (liminf_le_liminf (.of_forall fun i => mul_le_mul_of_nonneg_left
            (ENNReal.log_monotone (measure_mono interior_subset))
            (by exact_mod_cast (ε i).coe_nonneg))).trans liminf_le_limsup
      _ ≤ _ := hJ.upper_bound _ hCc
  exact (le_iInf₂ fun y hy => (hCJ hy).le).trans
    (EReal.coe_ennreal_le_coe_ennreal_iff.1 (EReal.neg_le_neg_iff.1 hrate))

/-- **Uniqueness of the rate function.** In a regular space, a family of measures along a
nontrivial filter satisfies a large deviation principle at a given speed with at most one rate
function. -/
theorem HasLDP.unique [RegularSpace X] [l.NeBot] (hI : HasLDP l ε μ I) (hJ : HasLDP l ε μ J) :
    I = J :=
  funext fun x => le_antisymm (hJ.le_of_hasLDP hI x) (hI.le_of_hasLDP hJ x)

/-- For probability measures along a nontrivial filter, a good rate function of a large deviation
principle has a zero. -/
theorem HasLDP.exists_eq_zero [l.NeBot] [∀ i, IsProbabilityMeasure (μ i)]
    (h : HasLDP l ε μ I) (hI : IsGoodRateFunction I) : ∃ x, I x = 0 := by
  have hinf : ((⨅ x ∈ (univ : Set X), I x : ℝ≥0∞) : EReal) ≤ 0 := by
    simpa using h.upper_bound univ isClosed_univ
  have hzero : ⨅ x ∈ (univ : Set X), I x = 0 := by
    exact_mod_cast le_antisymm hinf (EReal.coe_ennreal_nonneg _)
  obtain ⟨x, -, hx⟩ := hI.exists_eq_biInf isClosed_univ (hzero ▸ ENNReal.zero_ne_top)
  exact ⟨x, hx.trans hzero⟩

/-- **Exponential concentration on the zeros of the rate function.** For a large deviation
principle with a good rate function, the measure of the complement of an open set containing
every zero of the rate function is eventually at most `exp (-c / ε i)`, for some `c > 0`. -/
theorem HasLDP.exists_eventually_measure_compl_le (h : HasLDP l ε μ I)
    (hI : IsGoodRateFunction I) {U : Set X} (hU : IsOpen U) (hzero : ∀ x, I x = 0 → x ∈ U) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in l, μ i Uᶜ ≤ ENNReal.ofReal (Real.exp (-c / ε i)) := by
  -- The rate is bounded away from `0` on the closed set `Uᶜ`.
  have hd : 0 < ⨅ x ∈ Uᶜ, I x := by
    refine pos_iff_ne_zero.2 fun hd => ?_
    obtain ⟨x, hxU, hx⟩ := hI.exists_eq_biInf hU.isClosed_compl (hd ▸ ENNReal.zero_ne_top)
    exact hxU (hzero x (hx.trans hd))
  obtain ⟨c', hc'0, hc'⟩ := exists_between hd
  have hc'top : c' ≠ ∞ := ne_top_of_lt hc'
  refine ⟨c'.toReal, ENNReal.toReal_pos hc'0.ne' hc'top, ?_⟩
  have hlt : limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i Uᶜ)) l <
      ((-c'.toReal : ℝ) : EReal) := by
    refine (h.upper_bound _ hU.isClosed_compl).trans_lt ?_
    rw [EReal.coe_neg, EReal.neg_lt_neg_iff, EReal.coe_ennreal_toReal hc'top]
    exact EReal.coe_ennreal_lt_coe_ennreal_iff.2 hc'
  filter_upwards [eventually_lt_of_limsup_lt hlt, h.eventually_pos] with i hi hεi
  have hεi' : (0 : EReal) < ((ε i : ℝ) : EReal) := by exact_mod_cast hεi
  -- Divide the exponent by the speed.
  have hlog : ENNReal.log (μ i Uᶜ) ≤
      ENNReal.log (ENNReal.ofReal (Real.exp (-c'.toReal / ε i))) := by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp, EReal.coe_div,
      EReal.le_div_iff_mul_le hεi' (EReal.coe_ne_top _), mul_comm]
    exact hi.le
  exact ENNReal.log_le_log_iff.1 hlog

/-- For a large deviation principle with a good rate function at a speed tending to `0`, the
measures of the complement of an open set containing every zero of the rate function tend
to `0`. -/
theorem HasLDP.tendsto_measure_compl (h : HasLDP l ε μ I) (hI : IsGoodRateFunction I)
    (hε : Tendsto ε l (𝓝 0)) {U : Set X} (hU : IsOpen U) (hzero : ∀ x, I x = 0 → x ∈ U) :
    Tendsto (fun i => μ i Uᶜ) l (𝓝 0) := by
  obtain ⟨c, hc, hbound⟩ := h.exists_eventually_measure_compl_le hI hU hzero
  have hε' : Tendsto (fun i => (ε i : ℝ)) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨NNReal.tendsto_coe.2 hε, h.eventually_pos.mono fun i hi => hi⟩
  have hexp : Tendsto (fun i => ENNReal.ofReal (Real.exp (-c / ε i))) l (𝓝 0) := by
    have hdiv : Tendsto (fun i => -c / (ε i : ℝ)) l atBot := by
      simpa only [div_eq_mul_inv, Function.comp_def] using
        (tendsto_inv_nhdsGT_zero.comp hε').const_mul_atTop_of_neg (neg_neg_of_pos hc)
    simpa using ENNReal.tendsto_ofReal (Real.tendsto_exp_atBot.comp hdiv)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
    (.of_forall fun _ => bot_le) hbound

end TauCeti.Probability

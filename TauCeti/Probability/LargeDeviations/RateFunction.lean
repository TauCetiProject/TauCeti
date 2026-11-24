/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Probability.LargeDeviations.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Inv
import TauCeti.Analysis.SpecialFunctions.Log.ENNRealLog.Basic
import TauCeti.Data.EReal.Operations

/-!
# The rate function of a large deviation principle

Along a nontrivial filter, a large deviation principle at a given inverse speed determines its rate
function: in a regular space two lower semicontinuous rate functions for the same family of
measures at the same inverse speed coincide. For measures that eventually have total mass `1`,
along a nontrivial filter, a good rate function vanishes somewhere.

If the infimum of the rate function over a closed set `F` exceeds a real number `c`, the measure
of `F` is eventually at most `exp (-c / ε i)`. If that infimum is positive and the inverse speed
tends to `0`, the measures of `F` tend to `0`. Neither statement needs a good rate function. A
good rate function is bounded away from `0` on the complement of any open set containing all of
its zeros, so that complement has measure eventually at most `exp (-c / ε i)` for some `c > 0`, and
measure tending to `0` if the inverse speed tends to `0`: the measures concentrate on the zero
set. This is how a large deviation principle with a rate function having a unique zero yields a law
of large numbers, for example convergence of empirical spectral measures to an equilibrium measure.

In a pseudo-emetric space, the infimum of a good rate function over the closed `δ`-thickening of a
closed set `F` increases to its infimum over `F` as `δ` decreases to `0`. This lets an upper bound
on a thickening of `F`, as produced by exponentially equivalent families, pass to `F` itself.

## Main results

* `TauCeti.Probability.HasLDP.unique`: in a regular space, along a nontrivial filter, the rate
  function at a fixed inverse speed is unique.
* `TauCeti.Probability.HasLDP.exists_eq_zero`: for measures that eventually have total mass `1`,
  along a nontrivial filter, a good rate function has a zero.
* `TauCeti.Probability.HasLDP.eventually_measure_le_of_lt_biInf`: if a real `c` is below the
  infimum of the rate function over a closed set `F`, then `μ i F` is eventually at most
  `exp (-c / ε i)`.
* `TauCeti.Probability.HasLDP.tendsto_measure_of_biInf_pos`: if that infimum is positive and the
  inverse speed tends to `0`, the measures of `F` tend to `0`.
* `TauCeti.Probability.HasLDP.exists_eventually_measure_compl_le`: for a good rate function, the
  measure off an open neighbourhood of the zero set is eventually at most `exp (-c / ε i)` for
  some `c > 0`.
* `TauCeti.Probability.HasLDP.tendsto_measure_compl`: if moreover the inverse speed tends to `0`,
  the measures of the complement of such a neighbourhood tend to `0`.
* `TauCeti.Probability.IsGoodRateFunction.biSup_biInf_cthickening`: the infima of a good rate
  function over the closed thickenings of a closed set increase to its infimum over the set.
* `TauCeti.Probability.IsGoodRateFunction.exists_neg_coe_biInf_cthickening_lt`: every strict upper
  bound for `-inf_F I` is still a strict upper bound for `-inf I` over some closed thickening
  of `F`.

## References

* A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Springer
  (1998), §1.2, Lemma 4.1.4 and Lemma 4.1.6.
-/

public section

open Filter Topology MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι X : Type*}

section LDP

variable [TopologicalSpace X] [MeasurableSpace X]
  {l : Filter ι} {ε : ι → ℝ≥0} {μ : ι → Measure X} {I J : X → ℝ≥0∞}

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
          (ENNReal.liminf_coe_mul_log_mono (.of_forall fun i => measure_mono interior_subset)).trans
            liminf_le_limsup
      _ ≤ _ := hJ.upper_bound _ hCc
  exact (le_iInf₂ fun y hy => (Set.mem_Ioi.1 (Set.mem_preimage.1 (hCJ hy))).le).trans
    (EReal.coe_ennreal_le_coe_ennreal_iff.1 (EReal.neg_le_neg_iff.1 hrate))

/-- **Uniqueness of the rate function.** In a regular space, a family of measures along a
nontrivial filter satisfies a large deviation principle at a given inverse speed with at most one
rate function. -/
theorem HasLDP.unique [RegularSpace X] [l.NeBot] (hI : HasLDP l ε μ I) (hJ : HasLDP l ε μ J) :
    I = J :=
  funext fun x => le_antisymm (hJ.le_of_hasLDP hI x) (hI.le_of_hasLDP hJ x)

/-- For measures that eventually have total mass `1` along a nontrivial filter, a good rate
function of a large deviation principle has a zero. -/
theorem HasLDP.exists_eq_zero [l.NeBot] (h : HasLDP l ε μ I) (hI : IsGoodRateFunction I)
    (hμ : ∀ᶠ i in l, μ i univ = 1) : ∃ x, I x = 0 := by
  -- The whole space has rate `0`.
  have hlim : limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i univ)) l = 0 := by
    refine (limsup_congr ?_).trans (limsup_const (0 : EReal))
    filter_upwards [hμ] with i hi
    simp [hi]
  have hinf : ((⨅ x ∈ (univ : Set X), I x : ℝ≥0∞) : EReal) ≤ 0 := by
    simpa [hlim] using h.upper_bound univ isClosed_univ
  have hzero : ⨅ x ∈ (univ : Set X), I x = 0 := by
    exact_mod_cast le_antisymm hinf (EReal.coe_ennreal_nonneg _)
  obtain ⟨x, -, hx⟩ := hI.exists_eq_biInf isClosed_univ (hzero ▸ ENNReal.zero_ne_top)
  exact ⟨x, hx.trans hzero⟩

/-- **Exponential decay on a closed set.** If a real number `c` is below the infimum of the rate
function over a closed set `F`, the measure of `F` is eventually at most `exp (-c / ε i)`. The
threshold `c` may be negative. No goodness of the rate function is needed. -/
theorem HasLDP.eventually_measure_le_of_lt_biInf (h : HasLDP l ε μ I) {F : Set X}
    (hF : IsClosed F) {c : ℝ} (hc : (c : EReal) < ((⨅ x ∈ F, I x : ℝ≥0∞) : EReal)) :
    ∀ᶠ i in l, μ i F ≤ ENNReal.ofReal (Real.exp (-c / ε i)) := by
  have hlt : limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i F)) l <
      ((-c : ℝ) : EReal) := by
    refine (h.upper_bound _ hF).trans_lt ?_
    rwa [EReal.coe_neg, EReal.neg_lt_neg_iff]
  filter_upwards [eventually_lt_of_limsup_lt hlt, h.eventually_pos] with i hi hεi
  have hεi' : (0 : EReal) < ((ε i : ℝ) : EReal) := by exact_mod_cast hεi
  -- Divide the exponent by the inverse speed.
  have hlog : ENNReal.log (μ i F) ≤ ENNReal.log (ENNReal.ofReal (Real.exp (-c / ε i))) := by
    rw [← EReal.exp_coe, EReal.log_exp, EReal.coe_div,
      EReal.le_div_iff_mul_le hεi' (EReal.coe_ne_top _), mul_comm]
    exact hi.le
  exact ENNReal.log_le_log_iff.1 hlog

/-- At an inverse speed tending to `0`, the measures of a closed set over which the rate function
has a positive infimum tend to `0`. No goodness of the rate function is needed. -/
theorem HasLDP.tendsto_measure_of_biInf_pos (h : HasLDP l ε μ I) (hε : Tendsto ε l (𝓝 0))
    {F : Set X} (hF : IsClosed F) (hpos : 0 < ⨅ x ∈ F, I x) :
    Tendsto (fun i => μ i F) l (𝓝 0) := by
  obtain ⟨c, hc0, hc⟩ := EReal.exists_between_coe_real (EReal.coe_ennreal_pos.2 hpos)
  have hε' : Tendsto (fun i => (ε i : ℝ)) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨NNReal.tendsto_coe.2 hε,
      h.eventually_pos.mono fun i hi => Set.mem_Ioi.2 (NNReal.coe_pos.2 hi)⟩
  -- The bounds `exp (-c / ε i)` tend to `0`.
  have hexp : Tendsto (fun i => ENNReal.ofReal (Real.exp (-c / ε i))) l (𝓝 0) := by
    have hdiv : Tendsto (fun i => -c / (ε i : ℝ)) l atBot := by
      simpa only [div_eq_mul_inv, Function.comp_def] using
        (tendsto_inv_nhdsGT_zero.comp hε').const_mul_atTop_of_neg
          (neg_neg_of_pos (EReal.coe_pos.1 hc0))
    simpa using ENNReal.tendsto_ofReal (Real.tendsto_exp_atBot.comp hdiv)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
    (.of_forall fun _ => bot_le) (h.eventually_measure_le_of_lt_biInf hF hc)

/-- **Exponential concentration on the zeros of the rate function.** For a large deviation
principle with a good rate function, the measure of the complement of an open set containing
every zero of the rate function is eventually at most `exp (-c / ε i)`, for some `c > 0`. -/
theorem HasLDP.exists_eventually_measure_compl_le (h : HasLDP l ε μ I)
    (hI : IsGoodRateFunction I) {U : Set X} (hU : IsOpen U) (hzero : ∀ x, I x = 0 → x ∈ U) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in l, μ i Uᶜ ≤ ENNReal.ofReal (Real.exp (-c / ε i)) := by
  -- The rate is bounded away from `0` on the closed set `Uᶜ`.
  obtain ⟨c, hc0, hc⟩ := EReal.exists_between_coe_real <| EReal.coe_ennreal_pos.2 <|
    hI.biInf_pos hU.isClosed_compl fun x hx h0 => (Set.mem_compl_iff U x).1 hx (hzero x h0)
  exact ⟨c, EReal.coe_pos.1 hc0, h.eventually_measure_le_of_lt_biInf hU.isClosed_compl hc⟩

/-- For a large deviation principle with a good rate function at an inverse speed tending to `0`,
the measures of the complement of an open set containing every zero of the rate function tend
to `0`. -/
theorem HasLDP.tendsto_measure_compl (h : HasLDP l ε μ I) (hI : IsGoodRateFunction I)
    (hε : Tendsto ε l (𝓝 0)) {U : Set X} (hU : IsOpen U) (hzero : ∀ x, I x = 0 → x ∈ U) :
    Tendsto (fun i => μ i Uᶜ) l (𝓝 0) :=
  h.tendsto_measure_of_biInf_pos hε hU.isClosed_compl
    (hI.biInf_pos hU.isClosed_compl fun x hx h0 => (Set.mem_compl_iff U x).1 hx (hzero x h0))

end LDP

section Thickening

open Metric

variable [PseudoEMetricSpace X] {I : X → ℝ≥0∞}

/-- For a good rate function `I` and a closed set `F`, the infimum of `I` over the closed
`δ`-thickening of `F` increases to the infimum of `I` over `F` as `δ` decreases to `0`. -/
theorem IsGoodRateFunction.biSup_biInf_cthickening (hI : IsGoodRateFunction I)
    {F : Set X} (hF : IsClosed F) :
    ⨆ δ > (0 : ℝ), ⨅ x ∈ cthickening δ F, I x = ⨅ x ∈ F, I x := by
  refine le_antisymm (iSup₂_le fun δ _ => biInf_mono fun x hx => self_subset_cthickening F hx)
    (le_of_forall_lt fun c hc => ?_)
  obtain ⟨c', hcc', hc'⟩ := exists_between hc
  -- The compact sublevel set `{I ≤ c'}` misses `F`, so it misses a thickening of `F`.
  have hdisj : Disjoint {x | I x ≤ c'} F :=
    Set.disjoint_left.2 fun x hx hxF => (hc'.trans_le (biInf_le _ hxF)).not_ge (Set.mem_ofPred.1 hx)
  obtain ⟨δ, hδ, hδdisj⟩ :=
    hdisj.exists_cthickenings (hI.isCompact_sublevel c' (ne_top_of_lt hc')) hF
  refine hcc'.trans_le (le_iSup₂_of_le δ hδ (le_iInf₂ fun x hx => ?_))
  by_contra! hlt
  exact Set.disjoint_left.1 hδdisj (self_subset_cthickening _ (Set.mem_ofPred.2 hlt.le)) hx

/-- For a good rate function `I` and a closed set `F`, every `c > -inf_F I` also satisfies
`c > -inf I` over some closed thickening `cthickening δ F` with `δ > 0`. -/
theorem IsGoodRateFunction.exists_neg_coe_biInf_cthickening_lt (hI : IsGoodRateFunction I)
    {F : Set X} (hF : IsClosed F) {c : EReal} (hc : -((⨅ x ∈ F, I x : ℝ≥0∞) : EReal) < c) :
    ∃ δ > (0 : ℝ), -((⨅ x ∈ cthickening δ F, I x : ℝ≥0∞) : EReal) < c := by
  rw [← hI.biSup_biInf_cthickening hF, EReal.neg_lt_comm] at hc
  rcases lt_or_ge (-c) 0 with hc0 | hc0
  · exact ⟨1, one_pos, EReal.neg_lt_comm.1 (hc0.trans_le (EReal.coe_ennreal_nonneg _))⟩
  rw [← EReal.coe_toENNReal hc0, EReal.coe_ennreal_lt_coe_ennreal_iff] at hc
  obtain ⟨δ, hδ⟩ := lt_iSup_iff.1 hc
  obtain ⟨hδ0, hδ⟩ := lt_iSup_iff.1 hδ
  refine ⟨δ, hδ0, EReal.neg_lt_comm.1 ?_⟩
  rw [← EReal.coe_toENNReal hc0]
  exact EReal.coe_ennreal_lt_coe_ennreal_iff.2 hδ

end Thickening

end TauCeti.Probability

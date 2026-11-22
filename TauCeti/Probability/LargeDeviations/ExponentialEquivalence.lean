/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Probability.LargeDeviations.Basic
import Mathlib.Data.EReal.Inv
import TauCeti.Data.EReal.Operations
import TauCeti.Probability.LargeDeviations.LargestTerm

/-!
# Exponentially equivalent families

Two families of random variables `Z i` and `Z' i` on measure spaces `(Ω i, P i)`, with values in
a metric space, are *exponentially equivalent* at speed `ε` if the probability that they are more
than `δ` apart decays faster than every exponential:
`limsup ε i * log (P i {δ < dist (Z i) (Z' i)}) = ⊥` for each `δ > 0`. Exponentially equivalent
families satisfy the same large deviation principles with good rate functions. This allows a
principle to be transferred to truncated, rounded or slightly perturbed random variables.

For a good rate function `I` and a closed set `F`, the infimum of `I` over the closed
`δ`-thickening of `F` increases to its infimum over `F` as `δ` decreases to `0`.

## Main definitions

* `TauCeti.Probability.ExponentiallyEquivalent l ε P Z Z'`: exponential equivalence of the
  families `Z` and `Z'`.

## Main results

* `TauCeti.Probability.IsGoodRateFunction.iSup_iInf_cthickening`: the infima of a good rate
  function over the closed thickenings of a closed set increase to its infimum over the set.
* `TauCeti.Probability.HasLDP.of_exponentiallyEquivalent`: a large deviation principle with a good
  rate function passes to exponentially equivalent families.

## References

* A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Springer
  (1998), Lemma 4.1.6, Definition 4.2.10 and Theorem 4.2.13.
-/

public section

open Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι X : Type*}

section Thickening

variable [PseudoEMetricSpace X]

/-- For a good rate function `I` and a closed set `F`, the infimum of `I` over the closed
`δ`-thickening of `F` increases to the infimum of `I` over `F` as `δ` decreases to `0`. -/
theorem IsGoodRateFunction.iSup_iInf_cthickening {I : X → ℝ≥0∞} (hI : IsGoodRateFunction I)
    {F : Set X} (hF : IsClosed F) :
    ⨆ δ > (0 : ℝ), ⨅ x ∈ cthickening δ F, I x = ⨅ x ∈ F, I x := by
  refine le_antisymm (iSup₂_le fun δ _ => biInf_mono fun x hx => self_subset_cthickening F hx)
    (le_of_forall_lt fun c hc => ?_)
  obtain ⟨c', hcc', hc'⟩ := exists_between hc
  -- The compact sublevel set `{I ≤ c'}` misses `F`, so it misses a thickening of `F`.
  have hdisj : Disjoint {x | I x ≤ c'} F :=
    Set.disjoint_left.2 fun x hx hxF => (hc'.trans_le (biInf_le _ hxF)).not_ge hx
  obtain ⟨δ, hδ, hδdisj⟩ :=
    hdisj.exists_cthickenings (hI.isCompact_sublevel c' (ne_top_of_lt hc')) hF
  refine hcc'.trans_le (le_iSup₂_of_le δ hδ (le_iInf₂ fun x hx => ?_))
  by_contra! hlt
  exact Set.disjoint_left.1 hδdisj (self_subset_cthickening _ hlt.le) hx

/-- Below any level `c` above `-inf_F I`, a closed thickening of `F` keeps the rate above `-c`. -/
private theorem IsGoodRateFunction.exists_neg_coe_iInf_cthickening_lt {I : X → ℝ≥0∞}
    (hI : IsGoodRateFunction I) {F : Set X} (hF : IsClosed F) {c : EReal}
    (hc : -((⨅ x ∈ F, I x : ℝ≥0∞) : EReal) < c) :
    ∃ δ > (0 : ℝ), -((⨅ x ∈ cthickening δ F, I x : ℝ≥0∞) : EReal) < c := by
  rw [← hI.iSup_iInf_cthickening hF, EReal.neg_lt_comm] at hc
  rcases lt_or_ge (-c) 0 with hc0 | hc0
  · exact ⟨1, one_pos, EReal.neg_lt_comm.1 (hc0.trans_le (EReal.coe_ennreal_nonneg _))⟩
  rw [← EReal.coe_toENNReal hc0, EReal.coe_ennreal_lt_coe_ennreal_iff] at hc
  obtain ⟨δ, hδ⟩ := lt_iSup_iff.1 hc
  obtain ⟨hδ0, hδ⟩ := lt_iSup_iff.1 hδ
  refine ⟨δ, hδ0, EReal.neg_lt_comm.1 ?_⟩
  rw [← EReal.coe_toENNReal hc0]
  exact EReal.coe_ennreal_lt_coe_ennreal_iff.2 hδ

end Thickening

variable [PseudoMetricSpace X] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- The families `Z i` and `Z' i` of random variables on `(Ω i, P i)` are *exponentially
equivalent* at speed `ε` along `l`: for every `δ > 0`, the probability that `Z i` and `Z' i` are
more than `δ` apart has limsup rate `⊥`. -/
def ExponentiallyEquivalent (l : Filter ι) (ε : ι → ℝ≥0) (P : ∀ i, Measure (Ω i))
    (Z Z' : ∀ i, Ω i → X) : Prop :=
  ∀ δ : ℝ, 0 < δ → limsup (fun i => ((ε i : ℝ) : EReal) *
    ENNReal.log (P i {ω | δ < dist (Z i ω) (Z' i ω)})) l = ⊥

variable {l : Filter ι} {ε : ι → ℝ≥0} {P : ∀ i, Measure (Ω i)} {Z Z' : ∀ i, Ω i → X}

/-- Unfolding of `ExponentiallyEquivalent`. -/
theorem exponentiallyEquivalent_iff : ExponentiallyEquivalent l ε P Z Z' ↔
    ∀ δ : ℝ, 0 < δ → limsup (fun i => ((ε i : ℝ) : EReal) *
      ENNReal.log (P i {ω | δ < dist (Z i ω) (Z' i ω)})) l = ⊥ :=
  Iff.rfl

/-- Exponential equivalence is symmetric. -/
theorem ExponentiallyEquivalent.symm (h : ExponentiallyEquivalent l ε P Z Z') :
    ExponentiallyEquivalent l ε P Z' Z := by
  intro δ hδ
  simpa only [dist_comm] using h δ hδ

/-- Random variables that are uniformly within every positive distance of each other eventually
are exponentially equivalent at an eventually positive speed. -/
theorem ExponentiallyEquivalent.of_eventually_forall_dist_le
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in l, ∀ ω, dist (Z i ω) (Z' i ω) ≤ δ)
    (hpos : ∀ᶠ i in l, 0 < ε i) :
    ExponentiallyEquivalent l ε P Z Z' := by
  intro δ hδ
  refine (limsup_congr ?_).trans limsup_const_bot
  filter_upwards [hpos, h δ hδ] with i hi hδi
  have hempty : {ω | δ < dist (Z i ω) (Z' i ω)} = ∅ :=
    Set.eq_empty_of_forall_notMem fun ω hω => (hδi ω).not_gt hω
  simpa [hempty] using EReal.mul_bot_of_pos (by exact_mod_cast hi)

variable [MeasurableSpace X] [OpensMeasurableSpace X] {I : X → ℝ≥0∞}

/-- The lower bound for an exponentially equivalent family at a point of an open set. -/
private theorem HasLDP.neg_le_liminf_map_of_exponentiallyEquivalent
    (h : HasLDP l ε (fun i => (P i).map (Z i)) I) (hZ : ∀ i, AEMeasurable (Z i) (P i))
    (hZ' : ∀ i, AEMeasurable (Z' i) (P i)) (he : ExponentiallyEquivalent l ε P Z Z')
    (hε : Tendsto ε l (𝓝 0)) {G : Set X} (hG : IsOpen G) {x : X} (hx : x ∈ G) :
    -(I x : EReal) ≤
      liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z' i) G)) l := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hG x hx
  -- A ball of radius `r / 2` around `x` is caught by `G` up to an exponentially small error.
  have hsub (i : ι) : ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z i) (ball x (r / 2))) ≤
      ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z' i) G +
        P i {ω | r / 2 < dist (Z i ω) (Z' i ω)}) := by
    refine mul_le_mul_of_nonneg_left (ENNReal.log_monotone ?_)
      (by exact_mod_cast (ε i).coe_nonneg)
    rw [Measure.map_apply_of_aemeasurable (hZ i) isOpen_ball.measurableSet,
      Measure.map_apply_of_aemeasurable (hZ' i) hG.measurableSet]
    refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    by_cases hd : r / 2 < dist (Z i ω) (Z' i ω)
    · exact Or.inr hd
    · refine Or.inl (hball ?_)
      have hω' : dist (Z i ω) x < r / 2 := hω
      rw [mem_ball]
      linarith [dist_triangle (Z' i ω) (Z i ω) x, dist_comm (Z' i ω) (Z i ω)]
  calc -(I x : EReal) ≤ -((⨅ y ∈ ball x (r / 2), I y : ℝ≥0∞) : EReal) :=
        EReal.neg_le_neg_iff.2 <| EReal.coe_ennreal_le_coe_ennreal_iff.2 <|
          biInf_le _ (mem_ball_self (half_pos hr))
    _ ≤ liminf (fun i => ((ε i : ℝ) : EReal) *
          ENNReal.log ((P i).map (Z i) (ball x (r / 2)))) l := h.lower_bound _ isOpen_ball
    _ ≤ liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z' i) G +
          P i {ω | r / 2 < dist (Z i ω) (Z' i ω)})) l := liminf_le_liminf (.of_forall hsub)
    _ ≤ _ := by
      have := liminf_coe_mul_log_add_le (fun i => (P i).map (Z' i) G)
        (fun i => P i {ω | r / 2 < dist (Z i ω) (Z' i ω)}) hε
      rwa [he _ (half_pos hr), max_bot_right] at this

/-- The upper bound for an exponentially equivalent family on a closed set. -/
private theorem HasLDP.limsup_map_le_of_exponentiallyEquivalent
    (h : HasLDP l ε (fun i => (P i).map (Z i)) I) (hI : IsGoodRateFunction I)
    (hZ : ∀ i, AEMeasurable (Z i) (P i)) (hZ' : ∀ i, AEMeasurable (Z' i) (P i))
    (he : ExponentiallyEquivalent l ε P Z Z') (hε : Tendsto ε l (𝓝 0)) {F : Set X}
    (hF : IsClosed F) :
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z' i) F)) l ≤
      -((⨅ x ∈ F, I x : ℝ≥0∞) : EReal) := by
  refine le_of_forall_gt fun c hc => ?_
  obtain ⟨δ, hδ, hδc⟩ := hI.exists_neg_coe_iInf_cthickening_lt hF hc
  -- Up to an exponentially small error, `F` is caught by the thickening `cthickening δ F`.
  have hsub (i : ι) : ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z' i) F) ≤
      ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z i) (cthickening δ F) +
        P i {ω | δ < dist (Z i ω) (Z' i ω)}) := by
    refine mul_le_mul_of_nonneg_left (ENNReal.log_monotone ?_)
      (by exact_mod_cast (ε i).coe_nonneg)
    rw [Measure.map_apply_of_aemeasurable (hZ' i) hF.measurableSet,
      Measure.map_apply_of_aemeasurable (hZ i) isClosed_cthickening.measurableSet]
    refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    by_cases hd : δ < dist (Z i ω) (Z' i ω)
    · exact Or.inr hd
    · exact Or.inl (mem_cthickening_of_dist_le _ _ δ F hω (not_lt.1 hd))
  calc limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z' i) F)) l
      ≤ limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log ((P i).map (Z i) (cthickening δ F) +
          P i {ω | δ < dist (Z i ω) (Z' i ω)})) l := limsup_le_limsup (.of_forall hsub)
    _ ≤ limsup (fun i => ((ε i : ℝ) : EReal) *
          ENNReal.log ((P i).map (Z i) (cthickening δ F))) l := by
      rw [limsup_coe_mul_log_add _ _ hε, he δ hδ, max_bot_right]
    _ ≤ -((⨅ x ∈ cthickening δ F, I x : ℝ≥0∞) : EReal) := h.upper_bound _ isClosed_cthickening
    _ < c := hδc

/-- **Exponential equivalence.** If the laws of `Z i` satisfy a large deviation principle with a
good rate function at a speed tending to `0`, then so do the laws of every exponentially
equivalent family `Z' i`, with the same rate function. -/
theorem HasLDP.of_exponentiallyEquivalent (h : HasLDP l ε (fun i => (P i).map (Z i)) I)
    (hI : IsGoodRateFunction I) (hZ : ∀ i, AEMeasurable (Z i) (P i))
    (hZ' : ∀ i, AEMeasurable (Z' i) (P i)) (he : ExponentiallyEquivalent l ε P Z Z')
    (hε : Tendsto ε l (𝓝 0)) :
    HasLDP l ε (fun i => (P i).map (Z' i)) I := by
  refine ⟨h.lowerSemicontinuous, fun G hG => ?_,
    fun F hF => h.limsup_map_le_of_exponentiallyEquivalent hI hZ hZ' he hε hF⟩
  rw [EReal.neg_le]
  simp_rw [EReal.coe_ennreal_iInf]
  exact le_iInf₂ fun x hx => EReal.neg_le.1
    (h.neg_le_liminf_map_of_exponentiallyEquivalent hZ hZ' he hε hG hx)

end TauCeti.Probability

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Semicontinuity.Basic
import TauCeti.Analysis.SpecialFunctions.Log.ENNRealLog.Basic
import TauCeti.Order.Filter.Extr

/-!
# Large deviation principles

A family of measures `μ i` on a topological space `X`, indexed along a filter `l`, satisfies a
*large deviation principle* (LDP) with inverse speed `ε` and rate function `I : X → ℝ≥0∞` when
`ε i * log (μ i G)` has `liminf` at least `-inf_G I` for open `G`, and `limsup` at most
`-inf_F I` for closed `F`.

Logarithms are `ENNReal.log : ℝ≥0∞ → EReal`, so that `log 0 = ⊥`. The *inverse speed* `ε` is a
family of nonnegative reals, normally positive and tending to `0`. It is the reciprocal of the
speed `a` of Anderson–Guionnet–Zeitouni (Definition D.1), whose bounds are stated for
`a(n)⁻¹ log μ n`: a principle at speed `n` is `HasLDP atTop (fun n => (n : ℝ≥0)⁻¹) μ I`. The
bounds are stated with `ε i` as a multiplier in `EReal`, where `0 * ⊥ = 0`, so an inverse speed
`ε i = 0` is degenerate.

## Main definitions

* `TauCeti.Probability.IsGoodRateFunction I`: `I` is lower semicontinuous with compact sublevel
  sets `{x | I x ≤ α}` for `α < ∞`.
* `TauCeti.Probability.HasLDP l ε μ I`: the open-set lower and closed-set upper bounds.

## Main results

* `TauCeti.Probability.IsGoodRateFunction.exists_eq_biInf`: a good rate function attains its
  infimum over a closed set whenever that infimum is finite.
* `TauCeti.Probability.IsGoodRateFunction.biInf_pos`: a good rate function has a positive infimum
  over a closed set containing none of its zeros.
* `TauCeti.Probability.HasLDP.eventually_pos`: the inverse speed of a large deviation principle is
  eventually positive.
* `TauCeti.Probability.HasLDP.congr`: a large deviation principle depends only on the measures
  eventually along the filter.

The contraction principle is in `TauCeti.Probability.LargeDeviations.Contraction`, the
Dirac-mass example in `TauCeti.Probability.LargeDeviations.Dirac`, weak principles and
exponential tightness in `TauCeti.Probability.LargeDeviations.Weak`, exponential equivalence in
`TauCeti.Probability.LargeDeviations.ExponentialEquivalence`, uniqueness of the rate function,
concentration on its zeros and infima over thickenings in
`TauCeti.Probability.LargeDeviations.RateFunction`, and Gaussian laws in
`TauCeti.Probability.LargeDeviations.Gaussian`.

## References

* Dembo–Zeitouni, *Large Deviations Techniques and Applications*, §1.2 and §4.2.
-/

public section

open Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι X : Type*}

/-- A rate function is *good* if it is lower semicontinuous and has compact sublevel sets at every
finite level. -/
structure IsGoodRateFunction [TopologicalSpace X] (I : X → ℝ≥0∞) : Prop where
  lowerSemicontinuous : LowerSemicontinuous I
  isCompact_sublevel : ∀ α : ℝ≥0∞, α ≠ ∞ → IsCompact {x | I x ≤ α}

/-- A good rate function attains its infimum over every closed set on which that infimum is
finite. -/
theorem IsGoodRateFunction.exists_eq_biInf [TopologicalSpace X] {I : X → ℝ≥0∞}
    (hI : IsGoodRateFunction I) {F : Set X} (hF : IsClosed F) (hfin : ⨅ x ∈ F, I x ≠ ∞) :
    ∃ x ∈ F, I x = ⨅ y ∈ F, I y := by
  obtain ⟨x₁, hx₁, hlt⟩ : ∃ x₁ ∈ F, I x₁ < ∞ := by
    simpa only [iInf_lt_iff, exists_prop] using lt_top_iff_ne_top.mpr hfin
  -- Minimize `I` over the compact sublevel set `{x ∈ F | I x ≤ I x₁}`; the minimum is global.
  have hK : IsCompact {x ∈ F | I x ≤ I x₁} :=
    (hI.isCompact_sublevel _ hlt.ne).inter_left hF
  have hne : {x ∈ F | I x ≤ I x₁}.Nonempty := ⟨x₁, Set.mem_sep_iff.2 ⟨hx₁, le_rfl⟩⟩
  obtain ⟨x₀, hx₀, hmin⟩ := (hI.lowerSemicontinuous.lowerSemicontinuousOn _).exists_isMinOn hne hK
  obtain ⟨hx₀F, hx₀I⟩ := Set.mem_sep_iff.1 hx₀
  have hmin' : IsMinOn I F x₀ := (isMinOn_sublevel_iff hx₀I).1 hmin
  exact ⟨x₀, hx₀F, (iInf_subtype'.trans (hmin'.iInf_eq hx₀F)).symm⟩

/-- A good rate function is bounded away from `0` on a closed set containing none of its zeros:
its infimum there is attained, hence positive. -/
theorem IsGoodRateFunction.biInf_pos [TopologicalSpace X] {I : X → ℝ≥0∞}
    (hI : IsGoodRateFunction I) {F : Set X} (hF : IsClosed F) (hzero : ∀ x ∈ F, I x ≠ 0) :
    0 < ⨅ x ∈ F, I x := by
  refine pos_iff_ne_zero.2 fun hd => ?_
  obtain ⟨x, hxF, hx⟩ := hI.exists_eq_biInf hF (hd ▸ ENNReal.zero_ne_top)
  exact hzero x hxF (hx.trans hd)

/-- The family `μ i`, `i` along the filter `l`, satisfies a large deviation principle with inverse
speed `ε` and rate function `I`. The rate function is lower semicontinuous, and the bounds are
`-inf_G I ≤ liminf ε i * log (μ i G)` for open `G` and
`limsup ε i * log (μ i F) ≤ -inf_F I` for closed `F`. -/
structure HasLDP [TopologicalSpace X] [MeasurableSpace X] (l : Filter ι) (ε : ι → ℝ≥0)
    (μ : ι → Measure X) (I : X → ℝ≥0∞) : Prop where
  lowerSemicontinuous : LowerSemicontinuous I
  lower_bound : ∀ G : Set X, IsOpen G →
    -((⨅ x ∈ G, I x : ℝ≥0∞) : EReal) ≤
      liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i G)) l
  upper_bound : ∀ F : Set X, IsClosed F →
    limsup (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i F)) l ≤
      -((⨅ x ∈ F, I x : ℝ≥0∞) : EReal)

/-- A large deviation principle forces the inverse speed to be eventually positive: at a zero
inverse speed the empty set would have rate `0` instead of `⊥`. -/
theorem HasLDP.eventually_pos [TopologicalSpace X] [MeasurableSpace X] {l : Filter ι}
    {ε : ι → ℝ≥0} {μ : ι → Measure X} {I : X → ℝ≥0∞} (h : HasLDP l ε μ I) :
    ∀ᶠ i in l, 0 < ε i :=
  ENNReal.eventually_pos_of_limsup_coe_mul_log_lt_zero <|
    (h.upper_bound ∅ isClosed_empty).trans_lt (by simp)

/-- A large deviation principle depends only on the measures eventually along `l`: it passes to
every family `ν` with `μ i = ν i` eventually. -/
theorem HasLDP.congr [TopologicalSpace X] [MeasurableSpace X] {l : Filter ι} {ε : ι → ℝ≥0}
    {μ ν : ι → Measure X} {I : X → ℝ≥0∞} (h : HasLDP l ε μ I) (hμν : μ =ᶠ[l] ν) :
    HasLDP l ε ν I := by
  have hlog (A : Set X) : (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i A)) =ᶠ[l]
      fun i => ((ε i : ℝ) : EReal) * ENNReal.log (ν i A) :=
    hμν.mono fun i hi => by simp only [hi]
  exact ⟨h.lowerSemicontinuous, fun G hG => (h.lower_bound G hG).trans_eq (liminf_congr (hlog G)),
    fun F hF => (limsup_congr (hlog F)).symm.trans_le (h.upper_bound F hF)⟩

end TauCeti.Probability

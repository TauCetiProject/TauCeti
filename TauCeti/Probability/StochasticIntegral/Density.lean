/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable.Basic
public import TauCeti.Probability.Process.TimeMeasure
public import TauCeti.Probability.StochasticIntegral.Elementary
import TauCeti.Probability.Finance.SimpleStrategy.Approximation

/-!
# `L²` density of bounded elementary predictable integrands

On each finite horizon `(0, t]`, any predictable integrand in `L²((timeMeasure t).prod P)` can
be approximated arbitrarily closely in `L²((timeMeasure t).prod P)` — and therefore by a sequence
converging in `L²` — by bounded `TauCeti.ElementaryIntegrand`s, via the simple-holding
approximation theorem
`MeasureTheory.Filtration.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure`.

## Main results

* `MeasureTheory.Filtration.exists_elementaryIntegrand_eLpNorm_sub_lt`: single-step `L²`
  approximation of a predictable integrand by a bounded `TauCeti.ElementaryIntegrand`.
* `MeasureTheory.Filtration.exists_seq_elementaryIntegrand_tendsto_eLpNorm`: sequential `L²`
  approximation of a predictable integrand by bounded `TauCeti.ElementaryIntegrand`s.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B (Lemma 3.2.4 and Proposition 3.2.10).
-/

public section

noncomputable section

open MeasureTheory Filter Set TauCeti TauCeti.Probability
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Filtration

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
  choose K hK using fun k : ℕ ↦ ℱ.exists_elementaryIntegrand_eLpNorm_sub_lt P t hHp hH
    (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top (k + 1)))
  refine ⟨K, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
    (fun _ ↦ zero_le) fun k ↦ (hK k).le⟩

end MeasureTheory.Filtration

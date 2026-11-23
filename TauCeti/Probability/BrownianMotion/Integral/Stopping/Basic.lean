/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Process.StochasticInterval
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Stopping Brownian integrands

The predictable-set restriction lemmas for the expected and pathwise square-energy domains
specialize to `[0,τ]` and `(σ,τ]` for stopping times on a raw filtration, together with the
corresponding `toPredictableLp` cutoff laws (`BrownianIntegrable.toPredictableLp_ite_le`,
`BrownianIntegrable.toPredictableLp_ite_Ioc`). These are cutoff integrands, zero after the stopping
time, not stopped processes retaining their last value. Neither completeness nor right continuity of
the filtration is required.

Along stopping times tending almost surely to infinity, or decreasing almost surely to a target
stopping time `τ`, the cutoffs recover the integrand or its `τ`-cutoff in expected square-energy
norm on every finite horizon (`BrownianIntegrable.tendsto_eLpNorm_ite_le_sub`,
`BrownianIntegrable.tendsto_eLpNorm_ite_le_sub_ite_le`). These facts allow approximation and
localization of stochastic-integral inputs. The pathwise-domain closure results impose no
moment assumptions. No stochastic integral is constructed here.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ} {σ τ : Ω → WithTop ℝ≥0}

/-- Killing an integrand after a stopping time preserves finite expected square energy.
The value at the stopping time is retained. -/
theorem BrownianIntegrable.ite_le (hH : BrownianIntegrable ℱ P H)
    (hτ : IsStoppingTime ℱ τ) :
    BrownianIntegrable ℱ P (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Function.uncurry_apply_pair] using
    hH.indicator hτ.measurableSet_predictable_ge

/-- Killing an integrand after a stopping time preserves finite pathwise square energy.
The value at the stopping time is retained. -/
theorem LocallyBrownianIntegrable.ite_le (hH : LocallyBrownianIntegrable ℱ P H)
    (hτ : IsStoppingTime ℱ τ) :
    LocallyBrownianIntegrable ℱ P
      (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Function.uncurry_apply_pair] using
    hH.indicator hτ.measurableSet_predictable_ge

/-- Restriction to `(σ,τ]` preserves finite expected square energy. No ordering of the
stopping times is required. -/
theorem BrownianIntegrable.ite_Ioc (hH : BrownianIntegrable ℱ P H)
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) :
    BrownianIntegrable ℱ P
      (fun t ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Function.uncurry_apply_pair] using
    hH.indicator (hσ.measurableSet_predictable_Ioc hτ)

/-- Restriction to `(σ,τ]` preserves finite pathwise square energy. No ordering of the
stopping times is required. -/
theorem LocallyBrownianIntegrable.ite_Ioc (hH : LocallyBrownianIntegrable ℱ P H)
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) :
    LocallyBrownianIntegrable ℱ P
      (fun t ω ↦ if σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Function.uncurry_apply_pair] using
    hH.indicator (hσ.measurableSet_predictable_Ioc hτ)

/-- Cutoffs along stopping times tending almost surely to infinity converge on each finite
horizon in expected square-energy norm. Monotonicity of the times is unnecessary. -/
theorem BrownianIntegrable.tendsto_eLpNorm_ite_le_sub
    (hH : BrownianIntegrable ℱ P H) {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : ∀ n, IsStoppingTime ℱ (τ n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (τ · ω) atTop (𝓝 ⊤)) (T : ℝ≥0) :
    Tendsto (fun n ↦ eLpNorm
      (fun p : ℝ≥0 × Ω ↦ (if (p.1 : WithTop ℝ≥0) ≤ τ n p.2 then H p.1 p.2 else 0) -
        H p.1 p.2) 2
      (((volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ)).prod P))
      atTop (𝓝 0) := by
  apply tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
    (Eventually.of_forall fun n ↦ ((hH.ite_le (hτ n)).memLp T).aestronglyMeasurable)
    (hH.memLp T)
  · exact Eventually.of_forall fun n ↦ Eventually.of_forall fun p ↦ by
      dsimp only [Function.uncurry]
      split_ifs <;> simp
  · have hprod := (Measure.quasiMeasurePreserving_snd
        (μ := (volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ))
        (ν := P)).ae hlim
    filter_upwards [hprod] with p hp
    apply tendsto_const_nhds.congr'
    filter_upwards [hp.eventually (eventually_gt_nhds (WithTop.coe_lt_top p.1))] with n hn
    exact (ite_eq_left hn.le).symm

/-- Killing a `BrownianIntegrable` integrand after a stopping time `τ` cuts off its predictable `L²`
class by the indicator of the closed stochastic interval `⟦0, τ⟧`. -/
theorem BrownianIntegrable.toPredictableLp_ite_le (hH : BrownianIntegrable ℱ P H)
    (hτ : IsStoppingTime ℱ τ) (T : ℝ≥0) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    (hH.ite_le hτ).toPredictableLp T =
      ((Lp.memLp (hH.toPredictableLp T)).indicator
        hτ.measurableSet_predictable_ge.nullMeasurableSet).toLp
          ({p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0) ≤ τ p.2}.indicator (hH.toPredictableLp T)) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have heq : (hH.ite_le hτ).toPredictableLp T =
      (hH.indicator hτ.measurableSet_predictable_ge).toPredictableLp T := by
    rw [BrownianIntegrable.toPredictableLp_eq_iff]
    refine .of_forall ?_
    rintro ⟨t, ω⟩
    dsimp only [Function.uncurry_apply_pair]
    by_cases h : (t : WithTop ℝ≥0) ≤ τ ω
    · rw [ite_eq_left h, Set.indicator_of_mem h]; rfl
    · rw [ite_eq_right h, Set.indicator_of_notMem h]
  exact heq.trans (hH.toPredictableLp_indicator hτ.measurableSet_predictable_ge T)

/-- Restricting a `BrownianIntegrable` integrand to the half-open stochastic interval `(σ, τ]` cuts
off its predictable `L²` class by the indicator of `(σ, τ]`. -/
theorem BrownianIntegrable.toPredictableLp_ite_Ioc (hH : BrownianIntegrable ℱ P H)
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) (T : ℝ≥0) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    (hH.ite_Ioc hσ hτ).toPredictableLp T =
      ((Lp.memLp (hH.toPredictableLp T)).indicator
        (hσ.measurableSet_predictable_Ioc hτ).nullMeasurableSet).toLp
          ({p : ℝ≥0 × Ω | σ p.2 < p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ τ p.2}.indicator
            (hH.toPredictableLp T)) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have heq : (hH.ite_Ioc hσ hτ).toPredictableLp T =
      (hH.indicator (hσ.measurableSet_predictable_Ioc hτ)).toPredictableLp T := by
    rw [BrownianIntegrable.toPredictableLp_eq_iff]
    refine .of_forall ?_
    rintro ⟨t, ω⟩
    dsimp only [Function.uncurry_apply_pair]
    by_cases h : σ ω < t ∧ (t : WithTop ℝ≥0) ≤ τ ω
    · rw [ite_eq_left h, Set.indicator_of_mem h]; rfl
    · rw [ite_eq_right h, Set.indicator_of_notMem h]
  exact heq.trans (hH.toPredictableLp_indicator (hσ.measurableSet_predictable_Ioc hτ) T)

/-- Cutoffs along stopping times decreasing almost surely to a random time `τ` converge to the
cutoff at `τ` in `L²((timeMeasure T).prod P)` on every finite horizon. -/
theorem BrownianIntegrable.tendsto_eLpNorm_ite_le_sub_ite_le
    (hH : BrownianIntegrable ℱ P H) {σ : ℕ → Ω → WithTop ℝ≥0} {τ : Ω → WithTop ℝ≥0}
    (hσ : ∀ n, IsStoppingTime ℱ (σ n))
    (hle : ∀ᵐ ω ∂P, ∀ n, τ ω ≤ σ n ω)
    (hlim : ∀ᵐ ω ∂P, Tendsto (σ · ω) atTop (𝓝 (τ ω))) (T : ℝ≥0) :
    Tendsto (fun n ↦ eLpNorm
      (fun p : ℝ≥0 × Ω ↦ (if (p.1 : WithTop ℝ≥0) ≤ σ n p.2 then H p.1 p.2 else 0) -
        (if (p.1 : WithTop ℝ≥0) ≤ τ p.2 then H p.1 p.2 else 0)) 2
      ((Probability.timeMeasure T).prod P)) atTop (𝓝 0) := by
  refine TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) ENNReal.ofNat_ne_top
    (.of_forall fun n ↦ ((hH.ite_le (hσ n)).memLp_timeMeasure T).aestronglyMeasurable)
    (hH.memLp_timeMeasure T)
    (.of_forall fun n ↦ .of_forall fun ⟨t, ω⟩ ↦ by split_ifs <;> simp) ?_
  have hprod := (Measure.quasiMeasurePreserving_snd
    (μ := Probability.timeMeasure T) (ν := P)).ae (hle.and hlim)
  filter_upwards [hprod] with ⟨t, ω⟩ ⟨hωle, hωlim⟩
  by_cases hle' : (t : WithTop ℝ≥0) ≤ τ ω
  · exact tendsto_const_nhds.congr fun n ↦ by
      rw [ite_eq_left hle', ite_eq_left (hle'.trans (hωle n))]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hωlim.eventually (isOpen_Iio.mem_nhds (not_le.mp hle'))] with n hn
    rw [ite_eq_right hle', ite_eq_right (not_le.mpr hn)]

end TauCeti

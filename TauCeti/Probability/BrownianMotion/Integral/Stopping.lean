/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Process.StochasticInterval
public import TauCeti.Probability.Process.StoppingApproximation
import Mathlib.MeasureTheory.Integral.Indicator
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Stopping Brownian integrands

The predictable-set restriction lemmas for the expected and pathwise square-energy domains
specialize to `[0,τ]` and `(σ,τ]` for stopping times on a raw filtration. These are
cutoff integrands, zero after the stopping time, not stopped processes retaining their last
value. Neither completeness nor right continuity of the filtration is required.

Along stopping times tending almost surely to infinity, the cutoffs recover an integrand in
expected square-energy norm on every finite horizon. Along dyadic ceiling approximations
`dyadicCeilTime d ∘ τ` of any stopping time `τ`, the cutoffs of a `LocallyBrownianIntegrable`
integrand converge to the `[0, τ]` cutoff in pathwise square energy in probability on every finite
horizon (`LocallyBrownianIntegrable.tendsto_measure_lintegral_dyadicCeilTime`). These facts allow
approximation and localization of stochastic-integral inputs. The pathwise-domain closure results
impose no moment assumptions. No stochastic integral is constructed here.

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

/-- Along the dyadic ceiling approximations `dyadicCeilTime d ∘ τ` of any stopping time `τ` on the
raw filtration, the pathwise square-energy error on `(0, T]` between the `[0, dyadicCeilTime d ∘ τ]`
and `[0, τ]` cutoffs of a `LocallyBrownianIntegrable` integrand tends to zero in measure under a
finite sample measure. -/
theorem LocallyBrownianIntegrable.tendsto_measure_lintegral_dyadicCeilTime [IsFiniteMeasure P]
    (hH : LocallyBrownianIntegrable ℱ P H) (hτ : IsStoppingTime ℱ τ)
    (T : ℝ≥0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun d ↦ P {ω | ε ≤ ∫⁻ s,
      ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then H s ω else 0) -
        (if (s : WithTop ℝ≥0) ≤ τ ω then H s ω else 0)‖ₑ ^ 2
      ∂Probability.timeMeasure T}) atTop (𝓝 0) := by
  let F (d : ℕ) (s : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
    ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then H s ω else 0) -
      (if (s : WithTop ℝ≥0) ≤ τ ω then H s ω else 0)‖ₑ ^ 2
  have hF_meas (d : ℕ) : Measurable (fun p : ℝ≥0 × Ω ↦ F d p.1 p.2) :=
    (((hH.isStronglyPredictable.ite_le (hτ.dyadicCeilTime d)).sub
      (hH.isStronglyPredictable.ite_le hτ)).mono ℱ.predictable_le_prod).measurable.eNorm
      |>.pow_const 2
  rw [← measure_empty (μ := P)]
  refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty
    (fun d ↦ (hF_meas d).lintegral_prod_left' measurableSet_Ici)
    (hH.ae_memLp.mono fun ω hω ↦ ?_)
  have hm := hω T
  rw [NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def] at hm
  have hlim := tendsto_lintegral_dyadicCeilTime (u := τ ω)
    (hm.aestronglyMeasurable.eNorm.pow_const 2)
    (hm.aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.1 hm).ne
  filter_upwards [hlim.eventually (eventually_lt_nhds hε)] with d hd
  simp only [Set.mem_empty_iff_false, iff_false, not_le]
  exact hd

end TauCeti

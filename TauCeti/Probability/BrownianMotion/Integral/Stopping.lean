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
expected square-energy norm on every finite horizon. Under a finite measure `P`, cutting off a
locally Brownian-integrable integrand at the upward dyadic approximations `dyadicCeilTime k ∘ σ`
also converges in probability in pathwise square energy on `(0, T]` to the cutoff at `σ`
(`TauCeti.LocallyBrownianIntegrable.tendsto_measure_lintegral_ite_le_dyadicCeilTime_sub_sq`).
These facts allow approximation and localization of stochastic-integral inputs. The
pathwise-domain closure results impose no moment assumptions. No stochastic integral is
constructed here.

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

/-- On a finite measure space `P`, stopping a locally Brownian-integrable integrand at the dyadic
ceilings `dyadicCeilTime k ∘ σ` converges in probability in pathwise square energy on `(0, T]` to
the cutoff at `σ`. -/
theorem LocallyBrownianIntegrable.tendsto_measure_lintegral_ite_le_dyadicCeilTime_sub_sq
    [IsFiniteMeasure P] (hH : LocallyBrownianIntegrable ℱ P H) (hσ : IsStoppingTime ℱ σ)
    (T : ℝ≥0) (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s,
      ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ ω) then H s ω else 0) -
        if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0‖ₑ ^ 2
      ∂Probability.timeMeasure T}) atTop (𝓝 0) := by
  let D (k : ℕ) (ω : Ω) : ℝ≥0∞ := ∫⁻ s,
    ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ ω) then H s ω else 0) -
      if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0‖ₑ ^ 2 ∂Probability.timeMeasure T
  have hdiff_m (k : ℕ) : Measurable (Function.uncurry fun (s : ℝ≥0) ω ↦
      ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ ω) then H s ω else 0) -
        if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0‖ₑ ^ 2) :=
    (((hH.ite_le (hσ.dyadicCeilTime k)).isStronglyPredictable.sub
      (hH.ite_le hσ).isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
  have hmem : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∈ {ω | ε ≤ D k ω} ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hH.ae_memLp] with ω hω
    have hT : MemLp (fun s ↦ H s ω) 2 (Probability.timeMeasure T) := by
      simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using hω T
    have hdom (k : ℕ) (s : ℝ≥0) :
        ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ ω) then H s ω else 0) -
          if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0‖ₑ ^ 2 ≤ ‖H s ω‖ₑ ^ 2 := by
      by_cases hs : (s : WithTop ℝ≥0) ≤ σ ω
      · rw [ite_eq_left (hs.trans (le_dyadicCeilTime k (σ ω))), ite_eq_left hs]; simp
      · rw [ite_eq_right hs, sub_zero]; split_ifs <;> simp
    have hpt (s : ℝ≥0) : Tendsto (fun k ↦
        ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ ω) then H s ω else 0) -
          if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0‖ₑ ^ 2) atTop (𝓝 0) := by
      by_cases hs : (s : WithTop ℝ≥0) ≤ σ ω
      · refine tendsto_const_nhds.congr fun k ↦ ?_
        rw [ite_eq_left (hs.trans (le_dyadicCeilTime k (σ ω))), ite_eq_left hs]; simp
      · refine tendsto_const_nhds.congr' <|
          ((tendsto_dyadicCeilTime (σ ω)).eventually (eventually_lt_nhds (lt_of_not_ge hs))).mono
            fun k hk ↦ by dsimp only; rw [ite_eq_right hk.not_ge, ite_eq_right hs]; simp
    have hD0 : Tendsto (fun k ↦ D k ω) atTop (𝓝 0) := by
      simpa [D] using tendsto_lintegral_of_dominated_convergence (fun s ↦ ‖H s ω‖ₑ ^ 2)
        (fun k ↦ (hdiff_m k).comp (measurable_id.prodMk measurable_const))
        (fun k ↦ .of_forall (hdom k))
        ((AEStronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top
          hT.aestronglyMeasurable).mp hT).ne (.of_forall hpt)
    exact (hD0.eventually (eventually_lt_nhds hε)).mono fun _ hk ↦ by simp [hk.not_ge]
  simpa using tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty
    (fun k ↦ measurableSet_le measurable_const (hdiff_m k).lintegral_prod_left') hmem

end TauCeti

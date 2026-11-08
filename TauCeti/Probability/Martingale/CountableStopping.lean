/-
Copyright (c) 2023 Rémy Degenne, 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.OptionalSampling
public import TauCeti.Probability.Martingale.Basic
public import TauCeti.Probability.Process.StoppedValue

/-!
# Countable-range stopping on raw filtrations

Stopping a martingale at a countable-range stopping time preserves the martingale property,
even when the time index itself is uncountable. No path regularity, completeness or right
continuity of the filtration is required. In particular this applies to discrete-grid stopping
times of continuous-time processes, as used in localization.

We first prove bounded optional sampling with conditioning at another countable-range time.
The stopped-process theorem follows by capping the stopping time at a deterministic horizon.
The final theorem gives the indicator-stopped form appearing in `MeasureTheory.IsStable` and
`MeasureTheory.Locally`, so countable-range stopping times can be used for localization: paths
stopped at the bottom time contribute zero, rather than their possibly nonzero initial value.
All stopped values in the bounded sampling statements are at finite times; no terminal value
at infinity is asserted.

The optional-sampling argument adapts Rémy Degenne's
`MeasureTheory.Martingale.stoppedValue_min_ae_eq_condExp` in Mathlib's
`Probability/Martingale/OptionalSampling.lean`: countable-range measurable gluing replaces
its discrete-time measurability and integrability inputs. The existing countable-range
conditional-expectation identities remain the sampling engine.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §1.3.
-/

public section

noncomputable section

open Filter Set

namespace MeasureTheory

variable {Ω ι E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [Nonempty ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [IsFiniteMeasure μ] {ℱ : Filtration ι m} {X : ι → Ω → E} {τ σ : Ω → WithTop ι}

section Integrability

variable [FirstCountableTopology ι]

/-- A martingale evaluated at a bounded countable-range stopping time is integrable, even
when the time index is uncountable. -/
theorem Martingale.integrable_stoppedValue_of_countable_range (hX : Martingale X ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) {T : ι}
    (hb : ∀ ω, τ ω ≤ T) : Integrable (stoppedValue X τ) μ :=
  integrable_condExp.congr
    (hX.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hb hc).symm

end Integrability

variable [SecondCountableTopology ι]

/-- Once `τ ≤ σ`, the value at a bounded countable-range stopping time `τ` is already
known at `σ`. This is the restricted conditional-expectation identity, without any path
regularity assumption on the martingale. -/
theorem Martingale.condExp_stoppedValue_stopping_time_ae_eq_restrict_le_of_countable_range
    (hX : Martingale X ℱ μ) (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ)
    (hc : (range τ).Countable) {T : ι} (hb : ∀ ω, τ ω ≤ T) :
    μ[stoppedValue X τ | hσ.measurableSpace] =ᵐ[μ.restrict {ω | τ ω ≤ σ ω}]
      stoppedValue X τ := by
  have hint := hX.integrable_stoppedValue_of_countable_range hτ hc hb
  have hm := hX.stronglyAdapted.stronglyMeasurable_stoppedValue_of_countable_range_of_le_const
    hτ hc hb
  have hA := hτ.measurableSet_le_stopping_time hσ
  have hB := hτ.measurableSet_stopping_time_le hσ
  rw [ae_eq_restrict_iff_indicator_ae_eq (hτ.measurableSpace_le _ hA)]
  refine (condExp_indicator hint hB).symm.trans ?_
  refine condExp_of_stronglyMeasurable hσ.measurableSpace_le ?_
    (hint.indicator (hτ.measurableSpace_le _ hA)) |>.eventuallyEq
  refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on hA
    (fun t ht ↦ ?_) (hm.indicator hA) (fun ω hω ↦ Set.indicator_of_notMem hω _)
  rw [Set.inter_comm, hτ.measurableSet_inter_le_iff hσ,
    IsStoppingTime.measurableSet_min_iff hτ hσ] at ht
  simpa only [Set.inter_comm] using ht.2

/-- Bounded optional sampling at two countable-range times on a possibly uncountable time
index: conditioning the value at `τ` on the information at `σ` gives the value at `σ ∧ τ`.
Only `τ` is required to be bounded. -/
theorem Martingale.stoppedValue_min_ae_eq_condExp_of_countable_range (hX : Martingale X ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ)
    (hcτ : (range τ).Countable) (hcσ : (range σ).Countable) {T : ι}
    (hb : ∀ ω, τ ω ≤ T) :
    stoppedValue X (fun ω ↦ min (σ ω) (τ ω)) =ᵐ[μ]
      μ[stoppedValue X τ | hσ.measurableSpace] := by
  have hcmin := hcσ.range_min hcτ
  refine (hX.stoppedValue_ae_eq_condExp_of_le_of_countable_range hτ (hσ.min hτ)
    (fun _ ↦ min_le_right _ _) hb hcτ hcmin).trans ?_
  refine ae_of_ae_restrict_of_ae_restrict_compl {ω | σ ω ≤ τ ω} ?_ ?_
  · exact condExp_min_stopping_time_ae_eq_restrict_le hσ hτ
  · have heq : μ[stoppedValue X τ | (hσ.min hτ).measurableSpace]
        =ᵐ[μ.restrict {ω | τ ω ≤ σ ω}] μ[stoppedValue X τ | hσ.measurableSpace] := by
      have hm :=
        hX.stronglyAdapted.stronglyMeasurable_stoppedValue_of_countable_range_of_le_const hτ hcτ hb
      have hcond : μ[stoppedValue X τ | hτ.measurableSpace] = stoppedValue X τ :=
        condExp_of_stronglyMeasurable hτ.measurableSpace_le hm
          (hX.integrable_stoppedValue_of_countable_range hτ hcτ hb)
      calc
        μ[stoppedValue X τ | (hσ.min hτ).measurableSpace]
            = μ[stoppedValue X τ | (hτ.min hσ).measurableSpace] := by
                rw [hσ.measurableSpace_min hτ, hτ.measurableSpace_min hσ, inf_comm]
        _ =ᵐ[μ.restrict {ω | τ ω ≤ σ ω}] stoppedValue X τ := by
          simpa only [hcond] using
            condExp_min_stopping_time_ae_eq_restrict_le (μ := μ) (f := stoppedValue X τ) hτ hσ
        _ =ᵐ[μ.restrict {ω | τ ω ≤ σ ω}] μ[stoppedValue X τ | hσ.measurableSpace] := by
          exact (hX.condExp_stoppedValue_stopping_time_ae_eq_restrict_le_of_countable_range
            hτ hσ hcτ hb).symm
    rw [ae_restrict_iff' (hσ.measurableSpace_le _ (hσ.measurableSet_le_stopping_time hτ).compl)]
    rw [EventuallyEq, ae_restrict_iff'
      (hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time hσ))] at heq
    filter_upwards [heq] with ω hω hmem
    exact hω (not_le.1 hmem).le

/-- Stopping a martingale at a countable-range stopping time preserves the martingale
property in the original filtration. The time index may be uncountable; no path regularity
or usual-filtration hypotheses are imposed, and the stopping time may be unbounded. -/
theorem Martingale.stoppedProcess_of_countable_range (hX : Martingale X ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) :
    Martingale (stoppedProcess X τ) ℱ μ := by
  refine ⟨hX.stronglyAdapted.stoppedProcess_of_countable_range hτ hc, fun s t hst ↦ ?_⟩
  have hct := ((countable_singleton (t : WithTop ι)).mono range_const_subset).range_min hc
  have hcs : (range (fun _ : Ω ↦ (s : WithTop ι))).Countable :=
    (countable_singleton _).mono range_const_subset
  have hmin : (fun ω ↦ min (s : WithTop ι) (min (t : WithTop ι) (τ ω))) =
      (fun ω ↦ min (s : WithTop ι) (τ ω)) := by
    ext ω
    rw [← min_assoc, min_eq_left (WithTop.coe_le_coe.2 hst)]
  rw [stoppedProcess_eq_stoppedValue]
  simpa only [hmin, IsStoppingTime.measurableSpace_const]
    using (hX.stoppedValue_min_ae_eq_condExp_of_countable_range
      ((isStoppingTime_const ℱ t).min hτ) (isStoppingTime_const ℱ s) hct hcs
      (fun _ ↦ min_le_left _ _)).symm

/-- The indicator-stopped form appearing in `MeasureTheory.IsStable` and `MeasureTheory.Locally`
for a countable-range stopping time. On paths stopped at the bottom time the whole process is
zero. -/
theorem Martingale.stoppedProcess_indicator_of_countable_range [OrderBot ι]
    (hX : Martingale X ℱ μ) (hτ : IsStoppingTime ℱ τ) (hc : (range τ).Countable) :
    Martingale (stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ) ℱ μ := by
  rw [stoppedProcess_indicator_comm']
  refine (hX.stoppedProcess_of_countable_range hτ hc).indicator (fun t ↦ ℱ.mono bot_le _ ?_)
  simpa only [Set.compl_ofPred, not_le, WithTop.coe_bot] using (hτ ⊥).compl

end MeasureTheory

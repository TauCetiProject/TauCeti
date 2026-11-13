/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Basic
public import TauCeti.Probability.Process.LocalProperty
import TauCeti.Probability.Process.Stopping

/-!
# Initial-measurable multipliers of local martingales

Multiplication by a finite random scalar known at the initial time preserves native locality,
without any moment assumption on the scalar or on the initial value of the process. This allows
random initial capital in exponential-process constructions and initial-measurable factors in
localized stochastic identities.

The localizers are the original localizers, cut off at time zero where the multiplier exceeds
an increasing deterministic bound. Each new stopped stage is a bounded initial-measurable
multiple of an original stopped martingale. The positive-localizing-time indicator in Mathlib's
`Locally` is essential: stopping at zero alone would not remove the unbounded initial value.
No path regularity or usual conditions on the filtration are required.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Chapter 1, §5, for localization of martingales.
-/

public section

open Filter MeasureTheory
open scoped Topology

namespace ProbabilityTheory.Locally

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ι mΩ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : ι → Ω → E}

/-- A finite initial-measurable random scalar preserves native local martingales, with no
integrability assumption on the scalar and no regularity or literal adaptation assumption
on the original process. -/
theorem martingale_smul_initial (hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ ⊥] ξ) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ ξ ω • X t ω) P := by
  classical
  let A : ℕ → Set Ω := fun n ↦ {ω | ‖ξ ω‖ ≤ (n : ℝ)}
  have hA (n : ℕ) : MeasurableSet[ℱ ⊥] (A n) :=
    measurableSet_le hξ.norm.measurable measurable_const
  have hAmono : Monotone A := by
    intro n m hnm ω hω
    have hbound : ‖ξ ω‖ ≤ (n : ℝ) := hω
    exact hbound.trans (by exact_mod_cast hnm)
  have hexhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ A n :=
    ae_of_all P fun ω ↦
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖ξ ω‖)
  refine hX.isLocalizingSequence_localSeq.locally_of_indicator hA hAmono hexhaust fun n ↦ ?_
  let Z := stoppedProcess (fun t ↦ {ω | ⊥ < hX.localSeq n ω}.indicator (X t))
    (hX.localSeq n)
  have hZ : Martingale Z ℱ P := hX.stoppedProcess_localSeq n
  let c := (A n).indicator ξ
  have hc (t : ι) : StronglyMeasurable[ℱ t] c :=
    (hξ.indicator (hA n)).mono (ℱ.mono bot_le)
  have hbound : ∀ ω, ‖c ω‖ ≤ (n : ℝ) := by
    intro ω
    by_cases hω : ω ∈ A n
    · simp only [c, Set.indicator_of_mem hω]
      exact hω
    · simp only [c, Set.indicator_of_notMem hω, norm_zero, Nat.cast_nonneg]
  convert hZ.bdd_smul hc (n : ℝ) (ae_of_all P hbound) using 1
  ext t ω
  simp only [Z, stoppedProcess_indicator_pos_apply]
  by_cases hω : ω ∈ A n
  · simp only [c, Set.indicator_of_mem hω, stoppedProcess_indicator_pos_apply]
    split_ifs <;> simp
  · simp [hω, c]

end ProbabilityTheory.Locally

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty
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
  let τ : ℕ → Ω → WithTop ι := fun n ↦
    (A n).piecewise (hX.localSeq n) (fun _ ↦ ⊥)
  -- The cutoffs eventually disappear on every sample point, so the new times still localize.
  have hτ : IsLocalizingSequence ℱ τ P := by
    refine ⟨⟨fun n ↦ ?_, ?_⟩, ?_⟩
    · exact (hX.isLocalizingSequence_localSeq.isStoppingTime n).piecewise_of_le
        (isStoppingTime_const ℱ ⊥) (i := ⊥) (by simp) (by simp) (hA n)
    · filter_upwards [hX.isLocalizingSequence_localSeq.tendsto_top] with ω hω
      have hlarge : ∀ᶠ n : ℕ in atTop, ω ∈ A n :=
        tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖ξ ω‖)
      exact hω.congr' (hlarge.mono fun n hn ↦ by simp [τ, hn])
    · filter_upwards [hX.isLocalizingSequence_localSeq.mono] with ω hω n m hnm
      by_cases hn : ω ∈ A n
      · have hm : ω ∈ A m := hAmono hnm hn
        simpa [τ, Set.piecewise, hn, hm] using hω hnm
      · simp [τ, Set.piecewise, hn]
  refine ⟨τ, hτ, fun n ↦ ?_⟩
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
  have hint (t : ι) : Integrable (fun ω ↦ c ω • Z t ω) P :=
    (hZ.integrable t).bdd_smul (n : ℝ)
      ((hc t).mono (ℱ.le t)).aestronglyMeasurable (ae_of_all P hbound)
  -- Conditional pull-out applies only after cutting the multiplier down to a bounded one.
  have hmart : Martingale (fun t ω ↦ c ω • Z t ω) ℱ P := by
    refine ⟨fun t ↦ (hc t).smul (hZ.stronglyMeasurable t), fun s t hst ↦ ?_⟩
    exact (condExp_smul_of_aestronglyMeasurable_left (hc s).aestronglyMeasurable
      (hint t) (hZ.integrable t)).trans
        ((hZ.condExp_ae_eq hst).mono fun ω hω ↦ by simp only [Pi.smul_apply', hω])
  convert hmart using 1
  ext t ω
  simp only [Z, stoppedProcess_indicator_pos_apply]
  by_cases hω : ω ∈ A n
  · simp only [τ, Set.piecewise, hω, ↓reduceIte, c, Set.indicator_of_mem hω]
    split_ifs <;> simp
  · simp [τ, hω, c]

end ProbabilityTheory.Locally

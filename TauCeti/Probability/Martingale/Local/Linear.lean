/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty
public import Mathlib.Topology.Order.Cadlag
import TauCeti.Probability.Martingale.ContinuousStopping
import TauCeti.Probability.Process.Stopping

/-!
# Linear combinations of native local martingales

Real scalar multiplication preserves native local martingales on any raw filtration without path
regularity or finiteness assumptions (`ProbabilityTheory.Locally.martingale_smul`). On a finite
measure space, sums, differences, and finite sums of strongly progressive, almost-surely
right-continuous local martingales remain local martingales
(`ProbabilityTheory.Locally.martingale_add`, `ProbabilityTheory.Locally.martingale_sub`,
`Finset.locally_martingale_sum`), by intersecting localizing sequences and restopping via
`MeasureTheory.Martingale.stoppedProcess_indicator_of_le_of_ae_isRightContinuous`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §5.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory.Locally

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Real scalar multiplication preserves native local martingales without path regularity or
finiteness assumptions. -/
theorem martingale_smul {ι : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι]
    [OrderTopology ι] {ℱ : Filtration ι mΩ} {X : ι → Ω → E}
    (hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P) (a : ℝ) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ a • X t ω) P :=
  ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ by
    convert (hX.stoppedProcess_localSeq n).smul a using 1
    exact stoppedProcess_indicator_pos_smul a X (hX.localSeq n)⟩

variable [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}

/-- The sum of two strongly progressive, almost-surely right-continuous native local martingales
on a finite measure space is a native local martingale. -/
theorem martingale_add {X Y : ℝ≥0 → Ω → E}
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P)
    (hY : Locally (fun U ↦ Martingale U ℱ P) ℱ Y P)
    (hXp : IsStronglyProgressive ℱ X) (hYp : IsStronglyProgressive ℱ Y)
    (hXc : ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ X t ω))
    (hYc : ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ Y t ω)) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ X t ω + Y t ω) P := by
  have hτ := hX.isLocalizingSequence_localSeq.min hY.isLocalizingSequence_localSeq
  refine ⟨min hX.localSeq hY.localSeq, hτ, fun n ↦ ?_⟩
  have hXn := (hX.stoppedProcess_localSeq n).stoppedProcess_indicator_of_le_of_ae_isRightContinuous
    hXp hXc (hX.isLocalizingSequence_localSeq.isStoppingTime n) (hτ.isStoppingTime n)
    (fun _ ↦ min_le_left _ _)
  have hYn := (hY.stoppedProcess_localSeq n).stoppedProcess_indicator_of_le_of_ae_isRightContinuous
    hYp hYc (hY.isLocalizingSequence_localSeq.isStoppingTime n) (hτ.isStoppingTime n)
    (fun _ ↦ min_le_right _ _)
  convert hXn.add hYn using 1
  ext t ω
  have hadd := stoppedProcess_indicator_pos_add X Y ((hX.localSeq ⊓ hY.localSeq) n)
  rw [bot_eq_zero] at hadd
  exact congrFun (congrFun hadd t) ω

/-- The difference of two strongly progressive, almost-surely right-continuous native local
martingales on a finite measure space is a native local martingale. -/
theorem martingale_sub {X Y : ℝ≥0 → Ω → E}
    (hX : Locally (fun U ↦ Martingale U ℱ P) ℱ X P)
    (hY : Locally (fun U ↦ Martingale U ℱ P) ℱ Y P)
    (hXp : IsStronglyProgressive ℱ X) (hYp : IsStronglyProgressive ℱ Y)
    (hXc : ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ X t ω))
    (hYc : ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ Y t ω)) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ X t ω - Y t ω) P := by
  simpa only [sub_eq_add_neg, neg_one_smul] using
    hX.martingale_add (hY.martingale_smul (-1)) hXp (fun T ↦ (hYp T).const_smul (-1)) hXc
      (hYc.mono fun _ h t ↦ (h t).const_smul (-1))

end ProbabilityTheory.Locally

/-- A finite sum of strongly progressive, almost-surely right-continuous native local martingales
on a finite measure space is a native local martingale. -/
theorem Finset.locally_martingale_sum {κ Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ℱ : Filtration ℝ≥0 mΩ} (s : Finset κ) {X : κ → ℝ≥0 → Ω → E}
    (hloc : ∀ k ∈ s, Locally (fun U ↦ Martingale U ℱ P) ℱ (X k) P)
    (hprog : ∀ k ∈ s, IsStronglyProgressive ℱ (X k))
    (hrc : ∀ k ∈ s, ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ X k t ω)) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ ∑ k ∈ s, X k t ω) P := by
  classical
  have hmain : IsStronglyProgressive ℱ (fun t ω ↦ ∑ k ∈ s, X k t ω) ∧
      (∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ ∑ k ∈ s, X k t ω)) ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ ∑ k ∈ s, X k t ω) P := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨fun _ ↦ stronglyMeasurable_const,
        ae_of_all P fun _ ↦ continuous_const.isRightContinuous,
        Locally.of_prop (martingale_zero E ℱ P)⟩
    | @insert a s ha ih =>
      obtain ⟨hsp, hsc, hsl⟩ := ih (fun k hk ↦ hloc k (Finset.mem_insert_of_mem hk))
        (fun k hk ↦ hprog k (Finset.mem_insert_of_mem hk))
        (fun k hk ↦ hrc k (Finset.mem_insert_of_mem hk))
      have hap := hprog a (Finset.mem_insert_self a s)
      have hac := hrc a (Finset.mem_insert_self a s)
      have hal := hloc a (Finset.mem_insert_self a s)
      simp_rw [Finset.sum_insert ha]
      exact ⟨fun T ↦ (hap T).add (hsp T),
        hac.mp (hsc.mono fun _ hs' ha' t ↦ (ha' t).add (hs' t)),
        hal.martingale_add hsl hap hsp hac hsc⟩
  exact hmain.2.2

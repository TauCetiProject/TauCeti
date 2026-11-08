/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.ConditionalExpectation.Completion
public import TauCeti.Probability.Process.Filtration.NullAugmentation
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty

/-!
# Martingales under null augmentation

A martingale remains a martingale after completing the ambient measure and adjoining all
ambient null sets to its filtration. For an originally strongly adapted process the converse
also holds. No path regularity or right continuity of the filtration is needed for this step.

Native local martingales lift using the very same localizing sequence and the same
initial-time indicators. In particular, no integrability or literal adaptation of the
original local process is inferred or required: only its native stopped stages are lifted.
This is the completion step in passing from raw to usual stochastic bases; taking the
right-continuous hull is a separate operation.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991,
  Chapter 1, §2.
-/

public section

open MeasureTheory ProbabilityTheory Filter TauCeti.MeasureTheory

namespace MeasureTheory

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section Preorder

variable [Preorder ι]

/-- Conditional expectation on a null-augmented filtration under the completed measure
agrees almost everywhere with conditional expectation on the original filtration. -/
theorem Filtration.condExp_nullAugment_completion (ℱ : Filtration ι mΩ) (s : ι)
    [SigmaFinite (P.trim (ℱ.le s))] {f : Ω → E} (hf : AEStronglyMeasurable f P) :
    @condExp (NullMeasurableSpace Ω P) E (ℱ.nullAugment P s) _ _ _ P.completion f
      =ᵐ[P.completion] @condExp Ω E (ℱ s) mΩ _ _ P f := by
  -- NullMeasurableSpace Ω P is definitionally Ω, with measurable-space instance
  -- eventuallyMeasurableSpace mΩ (ae P), exactly the ambient space of nullAugment.
  -- This identifies the left side with the completion lemma's left side, not with
  -- conditional expectation under mΩ. The a.e. filter is transported by ae_completion.
  rw [Filtration.nullAugment_apply, P.ae_completion]
  exact condExp_eventuallyMeasurableSpace_completion (μ := P) (ℱ.le s) hf

variable {ℱ : Filtration ι mΩ} {X : ι → Ω → E} [SigmaFiniteFiltration P ℱ]

/-- A martingale lifts to the null-augmented filtration on the completed ambient space. -/
theorem Martingale.nullAugment (hX : Martingale X ℱ P) :
    @Martingale (NullMeasurableSpace Ω P) E ι _ _ _ _
      (fun t (ω : NullMeasurableSpace Ω P) => X t ω) (ℱ.nullAugment P) P.completion := by
  -- The carrier tag changes only the ambient measurable-space instance, not X t.
  -- Strong measurability names its σ-algebra explicitly, so mono transports it
  -- along le_nullAugment without any additional carrier map.
  refine ⟨fun t => (hX.stronglyMeasurable t).mono (ℱ.le_nullAugment P t), ?_⟩
  intro s t hst
  refine (ℱ.condExp_nullAugment_completion s (hX.integrable t).aestronglyMeasurable).trans ?_
  rw [P.ae_completion]
  exact hX.condExp_ae_eq hst

/-- For a process strongly adapted to the original filtration, null augmentation neither
creates nor destroys the martingale property. Original adaptation is essential to the
reverse implication on an incomplete basis. -/
@[simp]
theorem StronglyAdapted.martingale_nullAugment_iff (hX : StronglyAdapted ℱ X) :
    @Martingale (NullMeasurableSpace Ω P) E ι _ _ _ _
      (fun t (ω : NullMeasurableSpace Ω P) => X t ω) (ℱ.nullAugment P) P.completion ↔
      Martingale X ℱ P := by
  -- Keep the original adaptation hX: no descent of strong measurability from the
  -- augmented σ-algebra is used. As above, the carrier tag leaves X unchanged.
  refine ⟨fun h => ⟨hX, fun s t hst => ?_⟩, Martingale.nullAugment⟩
  have hce := ℱ.condExp_nullAugment_completion (P := P) s
    ((hX t).mono (ℱ.le t)).aestronglyMeasurable
  have heq := hce.symm.trans (h.condExp_ae_eq hst)
  rwa [P.ae_completion] at heq

end Preorder

end MeasureTheory

namespace ProbabilityTheory.Locally

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {ℱ : Filtration ι mΩ} {X : ι → Ω → E} [SigmaFiniteFiltration P ℱ]

/-- A native local martingale lifts to the null-augmented filtration under the completed
measure, without any path regularity or initial moment assumption. The original localizers
and the native indicator of a positive localizing time are preserved. -/
theorem martingale_nullAugment (hX : Locally (fun Y => Martingale Y ℱ P) ℱ X P) :
    @Locally ι (NullMeasurableSpace Ω P) E _ _ _ _ _ _
      (fun Y => Martingale Y (ℱ.nullAugment P) P.completion) (ℱ.nullAugment P)
      (fun t (ω : NullMeasurableSpace Ω P) => X t ω) P.completion := by
  obtain ⟨τ, hτ, hM⟩ := hX
  -- The carrier tag is definitionally Ω: τ and its stopping events are unchanged.
  -- Neither stoppedProcess nor the positive-time indicator uses an ambient measurable
  -- space, so lifting their inputs gives definitionally the same pointwise process.
  -- Only event measurability changes via le_nullAugment; transport the a.e. localizer
  -- properties separately using ae_completion.
  refine ⟨τ, ⟨⟨fun n t => ?_, ?_⟩, ?_⟩, fun n => (hM n).nullAugment⟩
  · exact ℱ.le_nullAugment P t _ (hτ.isStoppingTime n t)
  · exact P.ae_completion.symm ▸ hτ.tendsto_top
  · exact P.ae_completion.symm ▸ hτ.mono

end ProbabilityTheory.Locally

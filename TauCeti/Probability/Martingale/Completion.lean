/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Filtration.Completion
public import Mathlib.Probability.Martingale.Basic

/-!
# Raw martingales across ambient completion

Completing the ambient measure space, while keeping every time slice of a raw
filtration unchanged, preserves and reflects the martingale property. The same is
true of native local martingales: precisely the same stopping times and localizing
sequences work in both spaces. The native indicator of a positive localizing time
is preserved, so no initial moment assumption is introduced.

This is the measure-space transport needed to bring raw-filtration conclusions
proved on a completed ambient space back to the original basis. It does not descend
stopping times from a null-augmented filtration: those times need not be raw stopping
times. No path regularity, completeness of the original space, or right continuity
of the filtration is assumed.

The conditional-expectation comparison is
`TauCeti.MeasureTheory.condExp_completion`. For the completion and local-martingale
conventions, see Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, second
edition, Chapter 1, §§2 and 5.
-/

public section

open MeasureTheory ProbabilityTheory Filter

namespace MeasureTheory

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section Preorder

variable [Preorder ι] {ℱ : Filtration ι mΩ} {X : ι → Ω → E}

/-- Completing only the ambient space neither creates nor destroys martingales
on the original time slices. Literal strong adaptation is the same on both sides. -/
@[simp]
theorem martingale_completion_iff :
    @Martingale (NullMeasurableSpace Ω P) E ι _ _ _ _
      X (ℱ.monoAmbient le_eventuallyMeasurableSpace) P.completion ↔
      Martingale X ℱ P := by
  -- Adaptation refers only to the unchanged raw time slices.
  constructor
  · intro hX
    have hraw := (stronglyAdapted_monoAmbient_iff _).mp hX.stronglyAdapted
    refine ⟨hraw, fun s t hst ↦ ?_⟩
    have hf : AEStronglyMeasurable (X t) P :=
      ((hraw t).mono (ℱ.le t)).aestronglyMeasurable
    exact (TauCeti.MeasureTheory.condExp_completion (ℱ.le s) hf).symm.trans
      ((hX.condExp_ae_eq hst).filter_mono P.ae_completion.ge)
  · intro hX
    refine ⟨(stronglyAdapted_monoAmbient_iff _).mpr hX.stronglyAdapted,
      fun s t hst ↦ ?_⟩
    exact ((TauCeti.MeasureTheory.condExp_completion (ℱ.le s)
      (hX.integrable t).aestronglyMeasurable).trans
      (hX.condExp_ae_eq hst)).filter_mono P.ae_completion.le

end Preorder

end MeasureTheory

namespace ProbabilityTheory.Locally

variable {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {ℱ : Filtration ι mΩ} {X : ι → Ω → E}

/-- Native raw local martingales are invariant under completion of the ambient space.
Both directions keep the witnessing localizers and their initial-time indicators.
In particular, the original process need not be literally adapted or integrable. -/
-- Rewrite before simp changes the martingale predicate inside the lambda.
@[simp↓]
theorem martingale_completion_iff :
    @Locally ι (NullMeasurableSpace Ω P) E _ _ _ _ _ _
      (fun Y ↦ Martingale Y (ℱ.monoAmbient le_eventuallyMeasurableSpace) P.completion)
      (ℱ.monoAmbient le_eventuallyMeasurableSpace) X P.completion ↔
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P :=
  completion_iff fun _ ↦ MeasureTheory.martingale_completion_iff

end ProbabilityTheory.Locally

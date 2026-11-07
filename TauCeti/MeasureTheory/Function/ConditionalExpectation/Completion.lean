/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.ConditionalExpectation
public import TauCeti.MeasureTheory.Function.ConditionalExpectation.MeasurePreserving
public import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable

/-!
# Conditional expectations across completion

Completing the ambient measure does not change conditional expectations onto an original
sub-σ-algebra. Adjoining all ambient null sets to that sub-σ-algebra likewise leaves the
conditional expectation unchanged almost everywhere. These identities allow martingale
identities to be transported to a completed stochastic basis without identifying its
measurable space with the original one.

Only sigma-finiteness on the original conditioning σ-algebra is required. Observables are
assumed almost everywhere strongly measurable for the original measure; integrability is
not required, consistently with the zero convention for nonintegrable conditional expectations.
-/

public section

open MeasureTheory Filter

namespace TauCeti.MeasureTheory

variable {Ω E : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : Ω → E}

/-- Completion of the ambient measure preserves conditional expectation onto an original
sub-σ-algebra. -/
theorem condExp_completion (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hf : AEStronglyMeasurable f μ) :
    @condExp Ω E m (eventuallyMeasurableSpace m₀ (ae μ)) _ _ μ.completion f
      =ᵐ[μ] μ[f | m] := by
  -- Fix the carrier explicitly: completion changes the sigma-algebra, not its points.
  have hid : @MeasurePreserving Ω Ω (eventuallyMeasurableSpace m₀ (ae μ)) m₀
      id μ.completion μ := by
    have hmeas := @measurable_id'' Ω m₀ (eventuallyMeasurableSpace m₀ (ae μ))
      le_eventuallyMeasurableSpace
    refine @MeasurePreserving.mk Ω Ω (eventuallyMeasurableSpace m₀ (ae μ)) m₀
      id μ.completion μ hmeas
      (@Measure.ext Ω m₀ _ _ fun s hs => ?_)
    exact (@Measure.map_apply Ω Ω (eventuallyMeasurableSpace m₀ (ae μ)) m₀
      μ.completion id hmeas s hs).trans
      (μ.completion_apply s)
  have h := MeasurePreserving.condExp_comap (mα := eventuallyMeasurableSpace m₀ (ae μ))
    (mβ := m₀) hid hm hf
  convert h using 1
  · exact μ.ae_completion.symm
  · simp only [Function.comp_id, MeasurableSpace.comap_id]
  · simp only [Function.comp_id]

/-- Completing the ambient space and adjoining its null sets to the conditioning σ-algebra
preserves conditional expectation. The augmentation uses ambient null sets, not merely null
sets measurable in the original sub-σ-algebra. -/
theorem condExp_eventuallyMeasurableSpace_completion (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] (hf : AEStronglyMeasurable f μ) :
    @condExp Ω E (eventuallyMeasurableSpace m (ae μ))
      (eventuallyMeasurableSpace m₀ (ae μ)) _ _ μ.completion f =ᵐ[μ] μ[f | m] := by
  have hle : eventuallyMeasurableSpace m (ae μ) ≤
      eventuallyMeasurableSpace m₀ (ae μ) := by
    rintro s ⟨t, ht, hst⟩
    exact ⟨t, hm t ht, hst⟩
  -- Keep the original carrier explicit when trimming the completed measure.
  let ν : @Measure Ω (eventuallyMeasurableSpace m₀ (ae μ)) := μ.completion
  have htrim : ν.trim (hm.trans le_eventuallyMeasurableSpace) = μ.trim hm := by
    apply @Measure.ext Ω m
    intro s hs
    simp only [trim_measurableSet_eq _ hs]
    exact μ.completion_apply s
  have : SigmaFinite (ν.trim (hm.trans le_eventuallyMeasurableSpace)) :=
    htrim.symm ▸ inferInstance
  have hce := condExp_ae_eq_of_forall_exists_ae_eq (μ := ν) (f := f)
    (m₁ := m) (m₂ := eventuallyMeasurableSpace m (ae μ))
    le_eventuallyMeasurableSpace hle (fun _ hs => hs)
  exact hce.trans (condExp_completion hm hf)

end TauCeti.MeasureTheory

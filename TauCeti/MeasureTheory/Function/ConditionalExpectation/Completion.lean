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
conditional expectation unchanged almost everywhere. Consequently, conditional expectation
onto a sub-σ-algebra fixes every integrable function measurable for it modulo ambient null
sets. These identities allow martingale identities to be transported to a completed
stochastic basis without identifying its measurable space with the original one.

Only null-set augmentation requires sigma-finiteness on the original conditioning σ-algebra;
ambient completion alone does not. Observables are assumed almost everywhere strongly measurable
for the original measure; integrability is not required, consistently with the zero convention
for nonintegrable conditional expectations.
-/

public section

open MeasureTheory Filter

/- Carrier convention for the completion proofs below: Mathlib defines
NullMeasurableSpace Ω μ to be the type synonym Ω, and its instMeasurableSpace is
exactly eventuallyMeasurableSpace m₀ (ae μ). Thus μ.completion can be used as an
@Measure Ω (eventuallyMeasurableSpace m₀ (ae μ)) without a cast or a measure map.
The explicit ambient-space arguments below use this definitional identification;
they do not identify the original measurable space m₀ with its completion. -/

namespace MeasureTheory.Measure

variable {Ω : Type*} {m m₀ : MeasurableSpace Ω}

/-- Trimming the completed measure to an original sub-σ-algebra recovers the original trim. -/
theorem trim_completion (μ : Measure Ω) (hm : m ≤ m₀) :
    @Measure.trim Ω m (eventuallyMeasurableSpace m₀ (ae μ)) μ.completion
      (hm.trans le_eventuallyMeasurableSpace) = μ.trim hm := by
  apply @Measure.ext Ω m
  intro s hs
  rw [@trim_measurableSet_eq Ω m (eventuallyMeasurableSpace m₀ (ae μ))
    μ.completion s _ hs, trim_measurableSet_eq _ hs]
  exact μ.completion_apply s

/-- The identity from the completed ambient space to the original space preserves measure. -/
theorem measurePreserving_id_completion (μ : Measure Ω) :
    @MeasurePreserving Ω Ω (eventuallyMeasurableSpace m₀ (ae μ)) m₀
      id μ.completion μ := by
  have hmeas := @measurable_id'' Ω m₀ (eventuallyMeasurableSpace m₀ (ae μ))
    le_eventuallyMeasurableSpace
  refine @MeasurePreserving.mk Ω Ω (eventuallyMeasurableSpace m₀ (ae μ)) m₀
    id μ.completion μ hmeas ?_
  rw [← @trim_eq_map Ω m₀ (eventuallyMeasurableSpace m₀ (ae μ)) μ.completion
    le_eventuallyMeasurableSpace, μ.trim_completion le_rfl, trim_eq_self]

end MeasureTheory.Measure

namespace TauCeti.MeasureTheory

variable {Ω E : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : Ω → E}

/-- Completion of the ambient measure preserves conditional expectation onto an original
sub-σ-algebra. -/
theorem condExp_completion (hm : m ≤ m₀) (hf : AEStronglyMeasurable f μ) :
    @condExp Ω E m (eventuallyMeasurableSpace m₀ (ae μ)) _ _ μ.completion f
      =ᵐ[μ] μ[f | m] := by
  by_cases hσ : SigmaFinite (μ.trim hm)
  · have h := MeasurePreserving.condExp_comap (mα := eventuallyMeasurableSpace m₀ (ae μ))
      (mβ := m₀) μ.measurePreserving_id_completion hm hf
    convert h using 1
    · exact μ.ae_completion.symm
    · simp only [Function.comp_id, MeasurableSpace.comap_id]
    · simp only [Function.comp_id]
  · have hσ' : ¬SigmaFinite (@Measure.trim Ω m (eventuallyMeasurableSpace m₀ (ae μ))
        μ.completion (hm.trans le_eventuallyMeasurableSpace)) := by
      rwa [μ.trim_completion hm]
    rw [condExp_of_not_sigmaFinite (hm.trans le_eventuallyMeasurableSpace) hσ',
      condExp_of_not_sigmaFinite hm hσ]

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
  -- Use the carrier/instance identification above, retaining the completed σ-algebra.
  let ν : @Measure Ω (eventuallyMeasurableSpace m₀ (ae μ)) := μ.completion
  have : SigmaFinite (ν.trim (hm.trans le_eventuallyMeasurableSpace)) :=
    (μ.trim_completion hm).symm ▸ inferInstance
  have hce := condExp_ae_eq_of_forall_exists_ae_eq (μ := ν) (f := f)
    (m₁ := m) (m₂ := eventuallyMeasurableSpace m (ae μ))
    le_eventuallyMeasurableSpace hle (fun _ hs => hs)
  exact hce.trans (condExp_completion hm hf)

/-- Conditional expectation onto `m` fixes every integrable function that is almost everywhere
strongly measurable for `m` augmented by the ambient null sets. In particular, such a function
agrees almost everywhere with a strongly `m`-measurable function, although the augmented
σ-algebra need not be contained in the ambient one. -/
theorem condExp_of_aestronglyMeasurable_eventuallyMeasurableSpace (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)]
    (hf : AEStronglyMeasurable[eventuallyMeasurableSpace m (ae μ)] f μ)
    (hfi : Integrable f μ) : μ[f | m] =ᵐ[μ] f := by
  have hle : eventuallyMeasurableSpace m (ae μ) ≤ eventuallyMeasurableSpace m₀ (ae μ) := by
    rintro s ⟨t, ht, hst⟩
    exact ⟨t, hm t ht, hst⟩
  -- Condition on the augmented σ-algebra inside the completed space, where it is a
  -- sub-σ-algebra, and compare with conditioning on `m` there.
  let ν : @Measure Ω (eventuallyMeasurableSpace m₀ (ae μ)) := μ.completion
  have : SigmaFinite (ν.trim (hm.trans le_eventuallyMeasurableSpace)) :=
    (μ.trim_completion hm).symm ▸ inferInstance
  have : SigmaFinite (ν.trim hle) := sigmaFiniteTrim_mono hle le_eventuallyMeasurableSpace
  have hfiν : Integrable f ν := μ.measurePreserving_id_completion.integrable_comp_of_integrable hfi
  -- The completed measure has the same null sets, `Measure.ae_completion`.
  exact (condExp_eventuallyMeasurableSpace_completion hm hfi.aestronglyMeasurable).symm.trans
    (condExp_of_aestronglyMeasurable' (μ := ν) hle hf hfiν)

end TauCeti.MeasureTheory

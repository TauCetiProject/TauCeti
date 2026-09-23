/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Coding
import Mathlib.MeasureTheory.Function.FactorsThrough
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Transporting canonical probability-measure codes

The canonical code of a probability measure on a countably generated measurable space records its
values on a countable generating set algebra.  Besides determining the measure, these coordinates
generate the Giry measurable space on `ProbabilityMeasure α`.  Thus every measurable function of a
probability measure factors measurably through its code.

In particular, a measurable map `f : α → β` induces a measurable map between the ambient code
spaces.  On codes which represent probability measures, `probabilityMeasureCodeMap f hf` sends the
code of `P` to the code of `P.map f`.  Its values on non-representable codes are an arbitrary
measurable extension; the characteristic theorem deliberately specifies only realizable codes.
This lets measure-valued arguments work in a standard Borel code space without choosing a topology
on either value space.

## Main results

* `TauCeti.MeasureTheory.measurableSpace_probabilityMeasure_eq_comap_code` -- the Giry
  measurable space is induced by the canonical code;
* `TauCeti.MeasureTheory.probabilityMeasureCodeMap` -- measurable transport of codes along a
  measurable map;
* `TauCeti.MeasureTheory.probabilityMeasureCodeMap_apply` -- on realizable codes this transport is
  pushforward of the represented probability measure.
-/

public section

noncomputable section

open MeasureTheory MeasurableSpace

open scoped ENNReal

namespace TauCeti

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [CountablyGenerated α] [CountablyGenerated β]

/-- The Giry measurable space on probability measures over a countably generated space is the
pullback of the product measurable space along the canonical evaluation code. -/
theorem measurableSpace_probabilityMeasure_eq_comap_code :
    (inferInstance : MeasurableSpace (ProbabilityMeasure α)) =
      MeasurableSpace.comap (probabilityMeasureCode (α := α)) inferInstance := by
  apply le_antisymm
  · let mProb : MeasurableSpace (ProbabilityMeasure α) := inferInstance
    let mCode : MeasurableSpace (ProbabilityMeasure α) :=
      MeasurableSpace.comap (probabilityMeasureCode (α := α)) inferInstance
    have hcode : @Measurable (ProbabilityMeasure α)
        (ProbabilityMeasureCodeIndex α → ℝ≥0∞) mCode inferInstance
        (probabilityMeasureCode (α := α)) :=
      Measurable.of_comap_le le_rfl
    have hmeasure : @Measurable (ProbabilityMeasure α) (Measure α) mCode inferInstance
        ProbabilityMeasure.toMeasure := by
      refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
        (S := generateSetAlgebra (countableGeneratingSet α)) ?_ ?_ ?_
      · simp only [generateFrom_generateSetAlgebra_eq, generateFrom_countableGeneratingSet]
      · exact isSetAlgebra_generateSetAlgebra.isSetRing.isSetSemiring.isPiSystem
      · intro s hs
        convert (measurable_pi_apply ⟨s, hs⟩).comp hcode using 1
        ext P
        exact (probabilityMeasureCode_apply P ⟨s, hs⟩).symm
    have hid : @Measurable (ProbabilityMeasure α) (ProbabilityMeasure α) mCode mProb id := by
      exact hmeasure.subtype_mk (p := fun μ : Measure α => IsProbabilityMeasure μ)
    have hle := hid.comap_le
    simpa only [MeasurableSpace.comap_id] using hle
  · exact measurable_probabilityMeasureCode.comap_le

/-- A measurable function of a probability measure factors measurably through its canonical code.
The extension away from codes of actual probability measures is not specified. -/
theorem exists_measurable_comp_probabilityMeasureCode
    {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace γ] [Nonempty γ]
    {F : ProbabilityMeasure α → γ} (hF : Measurable F) :
    ∃ G : (ProbabilityMeasureCodeIndex α → ℝ≥0∞) → γ,
      Measurable G ∧ F = G ∘ probabilityMeasureCode := by
  have hF' : Measurable[MeasurableSpace.comap probabilityMeasureCode inferInstance] F := by
    rw [← measurableSpace_probabilityMeasure_eq_comap_code (α := α)]
    exact hF
  exact hF'.exists_eq_measurable_comp

/-- A measurable map between value spaces induces a measurable map between their ambient
probability-measure code spaces.  Outside the subset of realizable codes this is the measurable
extension supplied by Doob--Dynkin factorization. -/
def probabilityMeasureCodeMap (f : α → β) (hf : Measurable f) :
    (ProbabilityMeasureCodeIndex α → ℝ≥0∞) →
      ProbabilityMeasureCodeIndex β → ℝ≥0∞ :=
  Classical.choose <| exists_measurable_comp_probabilityMeasureCode
    (measurable_probabilityMeasureCode.comp (measurable_probabilityMeasure_map hf))

/-- Transport of probability-measure codes is measurable on the whole ambient code space. -/
theorem measurable_probabilityMeasureCodeMap (f : α → β) (hf : Measurable f) :
    Measurable (probabilityMeasureCodeMap f hf) :=
  (Classical.choose_spec <| exists_measurable_comp_probabilityMeasureCode
    (measurable_probabilityMeasureCode.comp (measurable_probabilityMeasure_map hf))).1

/-- On the code of an actual probability measure, code transport is pushforward. -/
@[simp]
theorem probabilityMeasureCodeMap_apply (f : α → β) (hf : Measurable f)
    (P : ProbabilityMeasure α) :
    probabilityMeasureCodeMap f hf (probabilityMeasureCode P) =
      probabilityMeasureCode (P.map f) := by
  have hspec := (Classical.choose_spec <| exists_measurable_comp_probabilityMeasureCode
    (measurable_probabilityMeasureCode.comp (measurable_probabilityMeasure_map hf))).2
  exact congrFun hspec P |>.symm

end MeasureTheory

end TauCeti

end

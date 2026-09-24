/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Coding
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Transporting canonical probability-measure codes

The canonical code of a probability measure on a countably generated measurable space records its
values on a countable generating set algebra.  Besides determining the measure, these coordinates
generate the Giry measurable space on `ProbabilityMeasure α`.  Thus every measurable function of a
probability measure into a nonempty standard Borel space factors measurably through its code.

In particular, a measurable map `f : α → β` induces a measurable map between the ambient code
spaces.  On codes which represent probability measures, `probabilityMeasureCodeMap f hf` sends the
code of `P` to the code of `P.map f`.  Its values on non-representable codes are an arbitrary
measurable extension; the characteristic theorem deliberately specifies only realizable codes.
This lets measure-valued arguments work in a standard Borel code space without choosing a topology
on either value space.

## Main results

* `TauCeti.MeasureTheory.probabilityMeasureCodeMap` -- measurable transport of codes along a
  measurable map;
* `TauCeti.MeasureTheory.probabilityMeasureCodeMap_apply` -- on realizable codes this transport is
  pushforward of the represented probability measure;
* `TauCeti.MeasureTheory.ProbabilityMeasure.probabilityMeasureCode_map_apply` -- coordinatewise
  evaluation of a pushed-forward code;
* `TauCeti.MeasureTheory.measurable_probabilityMeasureCode_map` -- measurability of a
  pushed-forward code.
-/

public section

noncomputable section

open MeasureTheory MeasurableSpace

open scoped ENNReal

namespace TauCeti

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [CountablyGenerated α] [CountablyGenerated β]

omit [CountablyGenerated α] in
/-- Coding commutes with pushing a probability measure forward, coordinate by coordinate: the
value at a member of the coding set algebra is the original measure of its preimage. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.probabilityMeasureCode_map_apply
    {β : Type*} [MeasurableSpace β] [CountablyGenerated β]
    (P : ProbabilityMeasure α) (f : α → β) (hf : AEMeasurable f P)
    (s : ProbabilityMeasureCodeIndex β) :
    probabilityMeasureCode (P.map f) s =
      (P : Measure α) (f ⁻¹' (s : Set β)) := by
  simpa only [probabilityMeasureCode_apply, ProbabilityMeasure.toMeasure_map] using
    Measure.map_apply_of_aemeasurable hf (measurableSet_probabilityMeasureCodeIndex s)

omit [CountablyGenerated α] in
/-- A measurable pushforward followed by the canonical measure code is measurable in the input
probability measure. -/
theorem measurable_probabilityMeasureCode_map {β : Type*} [MeasurableSpace β]
    [CountablyGenerated β] (f : α → β) (hf : Measurable f) :
    Measurable (fun P : ProbabilityMeasure α => probabilityMeasureCode (P.map f)) :=
  measurable_probabilityMeasureCode.comp
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_map hf)

/-- A measurable map between value spaces induces a measurable map between their ambient
probability-measure code spaces.  Outside the subset of realizable codes this is the measurable
extension supplied by Doob--Dynkin factorization. -/
def probabilityMeasureCodeMap (f : α → β) (hf : Measurable f) :
    (ProbabilityMeasureCodeIndex α → ℝ≥0∞) →
      ProbabilityMeasureCodeIndex β → ℝ≥0∞ :=
  Classical.choose <|
    (measurable_probabilityMeasureCode.comp
      (measurable_probabilityMeasure_map hf)).exists_eq_measurable_comp_probabilityMeasureCode

/-- Transport of probability-measure codes is measurable on the whole ambient code space. -/
theorem measurable_probabilityMeasureCodeMap (f : α → β) (hf : Measurable f) :
    Measurable (probabilityMeasureCodeMap f hf) :=
  (Classical.choose_spec <|
    (measurable_probabilityMeasureCode.comp
      (measurable_probabilityMeasure_map hf)).exists_eq_measurable_comp_probabilityMeasureCode).1

/-- On the code of an actual probability measure, code transport is pushforward. -/
@[simp]
theorem probabilityMeasureCodeMap_apply (f : α → β) (hf : Measurable f)
    (P : ProbabilityMeasure α) :
    probabilityMeasureCodeMap f hf (probabilityMeasureCode P) =
      probabilityMeasureCode (P.map f) := by
  have hspec := (Classical.choose_spec <|
    (measurable_probabilityMeasureCode.comp
      (measurable_probabilityMeasure_map hf)).exists_eq_measurable_comp_probabilityMeasureCode).2
  exact congrFun hspec P |>.symm

end MeasureTheory

end TauCeti

end

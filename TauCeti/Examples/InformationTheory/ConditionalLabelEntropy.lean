/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.ConditionalLabelEntropy
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Worked examples: conditional entropy of standard-Borel labels

* `atomInformation` is `∞` at `0`, `0` at `1` and `log 2` at `1/2`.
* For the uniform probability on `[0, 1)`, which has no atoms, the point label conditioned on a
  constant has conditional entropy `∞`, while the point label conditioned on itself has
  conditional entropy `0`.
* For the Dirac probability on a one-point space both conditional entropies are `0`.
-/

public section

open MeasureTheory Real TauCeti
open scoped ENNReal

namespace TauCeti.ConditionalLabelEntropyExamples

example : atomInformation 0 = ∞ := atomInformation_zero

example : atomInformation 1 = 0 := atomInformation_one

example : atomInformation 2⁻¹ = ENNReal.ofReal (log 2) := atomInformation_half

/-- The uniform probability on `[0, 1)`. -/
noncomputable abbrev unitUniform : Measure ℝ := volume.restrict (Set.Ico 0 1)

instance instIsProbabilityMeasureUnitUniform : IsProbabilityMeasure unitUniform :=
  ⟨by simp⟩

/-- The point label of `[0, 1)` conditioned on a constant has conditional entropy `∞`: every atom
is null. -/
example : conditionalLabelEntropy unitUniform id (fun _ ↦ ()) = ∞ := by
  rw [conditionalLabelEntropy_const_right aemeasurable_id ()]
  simp

/-- The point label of `[0, 1)` conditioned on itself has conditional entropy `0`. -/
example : conditionalLabelEntropy unitUniform id id = 0 :=
  conditionalLabelEntropy_self aemeasurable_id

/-- Under the Dirac probability on a point, conditioning on a constant gives `0`. -/
example :
    conditionalLabelEntropy (Measure.dirac ()) (fun _ : Unit ↦ (0 : ℝ)) (fun _ ↦ ()) = 0 := by
  rw [conditionalLabelEntropy_const_right aemeasurable_const ()]
  simp

/-- Under the Dirac probability on a point, conditioning on itself gives `0`. -/
example : conditionalLabelEntropy (Measure.dirac ()) (fun _ : Unit ↦ (0 : ℝ))
    (fun _ : Unit ↦ (0 : ℝ)) = 0 :=
  conditionalLabelEntropy_self aemeasurable_const

end TauCeti.ConditionalLabelEntropyExamples

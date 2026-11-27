/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.CondExpPartitionEntropy.Countable
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Worked examples: conditional entropy of a countable label given a σ-algebra

These examples check the conventions of `TauCeti.condExpCountablePartitionEntropy`.

* A fair bit conditioned on the trivial σ-algebra has entropy `log 2`, and conditioning it on the
  bit itself gives `0`.
-/

public section

open MeasureTheory Real TauCeti
open scoped ENNReal

namespace TauCeti.CondExpCountablePartitionEntropyExamples

/-- The fair bit: the uniform probability on `Bool`. -/
noncomputable abbrev fairBit : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

instance instIsProbabilityMeasureFairBit : IsProbabilityMeasure fairBit :=
  ⟨by
    rw [smul_apply, Measure.count_univ]
    simp [ENNReal.inv_mul_cancel]⟩

/-- A fair bit conditioned on the trivial σ-algebra has entropy `log 2`. -/
theorem condExpCountablePartitionEntropy_fairBit_bot :
    condExpCountablePartitionEntropy fairBit ⊥ id = ENNReal.ofReal (log 2) := by
  rw [condExpCountablePartitionEntropy_eq_ofReal,
    condExpPartitionEntropy_bot (a := id) fun i ↦ (measurableSet_singleton i).nullMeasurableSet]
  simp [measureReal_def, negMulLog]

/-- A fair bit conditioned on the bit itself has entropy `0`. -/
example : condExpCountablePartitionEntropy fairBit Bool.instMeasurableSpace id = 0 :=
  condExpCountablePartitionEntropy_eq_zero_of_measurableSet measurableSet_singleton

end TauCeti.CondExpCountablePartitionEntropyExamples

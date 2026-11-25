/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.CondExpPartitionEntropy
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Worked examples: conditional entropy of a finite partition given a σ-algebra

These examples check the conventions of `TauCeti.condExpPartitionEntropy`.

* A one-atom partition has conditional entropy `0` given every sub-σ-algebra, including when its
  alphabet carries empty atoms.
* A fair bit conditioned on the trivial σ-algebra has entropy `log 2`, while conditioning it on
  the bit itself gives `0`; reversing the monotonicity of `condExpPartitionEntropy_anti` would
  fail here.
-/

public section

open MeasureTheory Real TauCeti
open scoped ENNReal

namespace TauCeti.CondExpPartitionEntropyExamples

/-- The fair bit: the uniform probability on `Bool`. -/
noncomputable abbrev fairBit : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

instance instIsProbabilityMeasureFairBit : IsProbabilityMeasure fairBit :=
  ⟨by
    rw [smul_apply, Measure.count_univ]
    simp [ENNReal.inv_mul_cancel]⟩

/-- A one-atom partition, with an empty second atom, has conditional entropy `0` given any
sub-σ-algebra. -/
example {X : Type*} [MeasurableSpace X] (μ : Measure X) (m : MeasurableSpace X) :
    condExpPartitionEntropy μ m (fun _ : X ↦ true) = 0 :=
  condExpPartitionEntropy_eq_zero_of_measurableSet fun i ↦
    measurable_const (measurableSet_singleton i)

/-- A fair bit conditioned on the trivial σ-algebra has entropy `log 2`. -/
example : condExpPartitionEntropy fairBit ⊥ id = log 2 := by
  rw [condExpPartitionEntropy_bot (a := id) fun i ↦ (measurableSet_singleton i).nullMeasurableSet]
  simp [measureReal_def, negMulLog]

/-- A fair bit conditioned on the bit itself has entropy `0`. -/
example : condExpPartitionEntropy fairBit Bool.instMeasurableSpace id = 0 :=
  condExpPartitionEntropy_eq_zero_of_measurableSet measurableSet_singleton

end TauCeti.CondExpPartitionEntropyExamples

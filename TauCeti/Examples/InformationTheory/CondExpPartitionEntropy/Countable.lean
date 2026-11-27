/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.CondExpPartitionEntropy.Countable
public import Mathlib.Probability.UniformOn

/-!
# Worked examples: conditional entropy of a countable label given a σ-algebra

These examples check the conventions of `TauCeti.condExpCountablePartitionEntropy`.

* A fair bit, the uniform probability `ProbabilityTheory.uniformOn Set.univ` on `Bool`,
  conditioned on the trivial σ-algebra has entropy `log 2`, and conditioning it on the bit itself
  gives `0`.
-/

public section

open MeasureTheory ProbabilityTheory Real TauCeti
open scoped ENNReal

namespace TauCeti.CondExpCountablePartitionEntropyExamples

/-- A fair bit conditioned on the trivial σ-algebra has entropy `log 2`. -/
theorem condExpCountablePartitionEntropy_fairBit_bot :
    condExpCountablePartitionEntropy (uniformOn (Set.univ : Set Bool)) ⊥ id =
      ENNReal.ofReal (log 2) := by
  rw [condExpCountablePartitionEntropy_eq_ofReal,
    condExpPartitionEntropy_bot (a := id) fun i ↦ (measurableSet_singleton i).nullMeasurableSet]
  simp only [measureReal_def, uniformOn_univ]
  simp [negMulLog]

/-- A fair bit conditioned on the bit itself has entropy `0`. -/
example :
    condExpCountablePartitionEntropy (uniformOn (Set.univ : Set Bool)) Bool.instMeasurableSpace id =
      0 :=
  condExpCountablePartitionEntropy_eq_zero_of_measurableSet measurableSet_singleton

end TauCeti.CondExpCountablePartitionEntropyExamples

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Uniform measures on finite types

This file records the probability-measure instance for the uniform measure on a nonempty finite
universe and the probability that two independent uniform samples from `Fin 2` differ.

## Main results

* `TauCeti.Probability.isProbabilityMeasure_uniformOfFinset_univ`: the uniform measure on a
  nonempty finite type has total mass one.
* `TauCeti.Probability.uniformOfFinset_univ_fin_two_prod_offDiagonal`: two independent uniform
  samples from `Fin 2` differ with probability `1 / 2`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.Probability

/-- The uniform measure on all of a nonempty finite type is a probability measure. -/
instance isProbabilityMeasure_uniformOfFinset_univ {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    IsProbabilityMeasure (Measure.uniformOfFinset (Finset.univ : Finset α)) :=
  ⟨by simp [Measure.uniformOfFinset_apply, ENNReal.div_self]⟩

/-- Two independent uniform samples from `Fin 2` differ with probability `1 / 2`. -/
@[simp]
theorem uniformOfFinset_univ_fin_two_prod_offDiagonal :
    ((Measure.uniformOfFinset (Finset.univ : Finset (Fin 2))).prod
      (Measure.uniformOfFinset (Finset.univ : Finset (Fin 2)))) {q | q.1 ≠ q.2} = (2 : ℝ≥0∞)⁻¹ := by
  have h : {q : Fin 2 × Fin 2 | q.1 ≠ q.2} = {(0, 1), (1, 0)} := by
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp
  rw [h, ← singleton_union, measure_union (by simp) (measurableSet_singleton _)]
  simp only [← singleton_prod_singleton, Measure.prod_prod,
    Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, Nat.cast_ofNat]
  rw [← mul_two, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

end TauCeti.Probability

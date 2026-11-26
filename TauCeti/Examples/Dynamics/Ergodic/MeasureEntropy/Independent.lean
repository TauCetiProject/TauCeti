/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.Dynamics.Ergodic.MeasureEntropy.Basic
public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Independent
public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Congr

/-!
# Worked example: the swap on two points

For the swap `not` on two equiprobable points with the partition into points, the label has
entropy `log 2` but rate `0`: the rate is strictly below the entropy. The labels `id` and
`not ∘ id = not` generate the same partition, so they are not independent, and accordingly the
iterates of the label are not independent (`TauCeti.partitionEntropyRate_of_iIndepFun` would
force rate `log 2`).
-/

public section

open MeasureTheory ProbabilityTheory Real TauCeti
open scoped ENNReal

namespace TauCeti.MeasureEntropyExamples

/-- Under the swap the partition into points has rate `0`. -/
theorem partitionEntropyRate_not_id : partitionEntropyRate fairBit not id = 0 :=
  nonpos_iff_eq_zero.mp <|
    (partitionEntropyRate_le_measureEntropy_of_finite not measurable_id).trans
      measureEntropy_not_fairBit.le

/-- **Check.** For the swap the rate of the partition into points is strictly below its entropy
`log 2`. -/
theorem partitionEntropyRate_not_id_lt :
    partitionEntropyRate fairBit not id < countablePartitionEntropy fairBit id := by
  rw [partitionEntropyRate_not_id, countablePartitionEntropy_fairBit_id]
  exact ENNReal.ofReal_pos.mpr (log_pos one_lt_two)

/-- **Check.** The label `id` and its image `not ∘ id` under the swap are not independent: the
cell `{true} ∩ not ⁻¹' {true}` is empty, while both atoms have mass `1 / 2`. -/
theorem not_indepFun_id_not : ¬ IndepFun id not fairBit := by
  intro h
  have := h.measure_inter_preimage_eq_mul {true} {true} (measurableSet_singleton _)
    (measurableSet_singleton _)
  have hempty : id ⁻¹' {true} ∩ not ⁻¹' {true} = (∅ : Set Bool) := by
    ext b
    cases b <;> simp
  have h1 : fairBit (id ⁻¹' {true}) = 2⁻¹ := by simp
  have h2 : fairBit (not ⁻¹' {true}) = 2⁻¹ := by
    rw [show not ⁻¹' {true} = ({false} : Set Bool) by ext b; cases b <;> simp]
    simp
  rw [hempty, measure_empty, h1, h2] at this
  exact absurd this.symm (by simp)

/-- **Check.** The iterates of the partition into points under the swap are not independent,
since independence would make the rate equal to the entropy. -/
theorem not_iIndepFun_iterate_not : ¬ iIndepFun (fun k (x : Bool) ↦ id (not^[k] x)) fairBit :=
  fun h ↦ partitionEntropyRate_not_id_lt.ne
    (partitionEntropyRate_of_iIndepFun measurePreserving_not_fairBit measurable_id h)

end TauCeti.MeasureEntropyExamples

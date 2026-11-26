/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.PartitionEntropy
import TauCeti.InformationTheory.PartitionEntropy.Finite

/-!
# Equality in subadditivity of partition entropy

Under a probability measure the entropy of the join of two measurable countable labels is at most
the sum of their entropies, `H(a ∨ b) ≤ H(a) + H(b)`
(`TauCeti.countablePartitionEntropy_pair_le_add`), with equality for independent labels
(`TauCeti.countablePartitionEntropy_pair_of_indepFun`). This file proves the converse for labels
with finitely many values: equality forces independence. On a finite alphabet the partition
entropy is the real label entropy (`TauCeti.toReal_countablePartitionEntropy`), so this is
`TauCeti.indepFun_of_labelEntropy_pair_eq_add`.

## Main results

* `TauCeti.indepFun_of_countablePartitionEntropy_pair_eq_add`: if `H(a ∨ b) = H(a) + H(b)` for
  measurable labels with finitely many values, they are independent.
* `TauCeti.countablePartitionEntropy_pair_eq_add_iff_indepFun`: for such labels,
  `H(a ∨ b) = H(a) + H(b)` exactly when `a` and `b` are independent.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Proposition 4.3, p. 106.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {X ι κ : Type*} {mX : MeasurableSpace X} {μ : Measure X} [Finite ι] [Finite κ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- **Equality in subadditivity.** Under a probability measure (or the zero measure), if two
measurable labels with finitely many values satisfy `H(a ∨ b) = H(a) + H(b)`, they are
independent. -/
theorem indepFun_of_countablePartitionEntropy_pair_eq_add [IsZeroOrProbabilityMeasure μ]
    {a : X → ι} {b : X → κ} (ha : Measurable a) (hb : Measurable b)
    (h : countablePartitionEntropy μ (fun x ↦ (a x, b x)) =
      countablePartitionEntropy μ a + countablePartitionEntropy μ b) :
    IndepFun a b μ := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  refine indepFun_of_labelEntropy_pair_eq_add ha hb ?_
  simpa [ENNReal.toReal_add, countablePartitionEntropy_ne_top, toReal_countablePartitionEntropy]
    using congrArg ENNReal.toReal h

/-- **Equality in subadditivity.** Under a probability measure (or the zero measure), measurable
labels with finitely many values satisfy `H(a ∨ b) = H(a) + H(b)` exactly when they are
independent. -/
theorem countablePartitionEntropy_pair_eq_add_iff_indepFun [IsZeroOrProbabilityMeasure μ]
    {a : X → ι} {b : X → κ} (ha : Measurable a) (hb : Measurable b) :
    countablePartitionEntropy μ (fun x ↦ (a x, b x)) =
        countablePartitionEntropy μ a + countablePartitionEntropy μ b ↔ IndepFun a b μ :=
  ⟨indepFun_of_countablePartitionEntropy_pair_eq_add ha hb,
    countablePartitionEntropy_pair_of_indepFun ha hb⟩

end TauCeti

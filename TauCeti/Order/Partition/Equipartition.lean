/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Partition.Equipartition
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Cardinality bounds for finite equipartitions

In an equipartition `P` of a finite set `s`, every part has cardinality `#s / #P.parts` or
`#s / #P.parts + 1`. Consequently, for every part `A ∈ P.parts` there are at most `#s / #P.parts`
other elements in `A`, so the total number of within-part ordered distinct pairs across all parts of
`P` is at most `#s * (#s / #P.parts)`.

## Main results

* `Finpartition.IsEquipartition.sum_card_mul_sub_one_le`: the within-part ordered distinct pairs of
  an equipartition `P` of `s` total at most `#s * (#s / #P.parts)`.
-/

public section

open Finset

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α} {P : Finpartition s}

/-- In an equipartition `P` of `s`, the within-part ordered distinct pairs total at most
`#s * (#s / #P.parts)`: every part has size `#s / #P.parts` or `#s / #P.parts + 1`, so `#A - 1` is
always at most `#s / #P.parts`. -/
theorem IsEquipartition.sum_card_mul_sub_one_le (hP : P.IsEquipartition) :
    ∑ A ∈ P.parts, #A * (#A - 1) ≤ #s * (#s / #P.parts) := by
  calc ∑ A ∈ P.parts, #A * (#A - 1)
      ≤ ∑ A ∈ P.parts, #A * (#s / #P.parts) :=
        sum_le_sum fun A hA ↦ Nat.mul_le_mul_left _
          (Nat.sub_le_iff_le_add.2 (hP.card_part_le_average_add_one hA))
    _ = #s * (#s / #P.parts) := by rw [← sum_mul, P.sum_card_parts]

end Finpartition

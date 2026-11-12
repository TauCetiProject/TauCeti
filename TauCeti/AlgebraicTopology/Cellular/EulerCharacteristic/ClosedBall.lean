/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType

/-!
# The Euler characteristic of a closed ball

A closed ball of nonnegative radius in a real normed space is contractible, so it has finite CW
type and Euler characteristic one. A closed ball of negative radius is empty, so closed balls have
finite CW type for every radius.

## Main declarations

* `TauCeti.finiteCWType_closedBall`: every closed ball of a real normed space has finite CW type.
* `TauCeti.eulerChar_closedBall`: a closed ball of nonnegative radius has `χ = 1`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the Euler characteristic after Theorem 2.44.
-/

public section

open Metric

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A closed ball in a real normed space has finite CW type: it is contractible for a nonnegative
radius and empty otherwise. -/
instance finiteCWType_closedBall (x : E) (r : ℝ) : FiniteCWType (closedBall x r) := by
  rcases le_or_gt 0 r with hr | hr
  · have := contractibleSpace_closedBall (x := x) hr
    infer_instance
  · have : IsEmpty (closedBall x r) := by
      rw [Set.isEmpty_coe_sort, closedBall_eq_empty]
      exact hr
    exact FiniteCWType.of_discreteTopology _

/-- A closed ball of nonnegative radius in a real normed space has Euler characteristic one. -/
@[simp]
theorem eulerChar_closedBall (x : E) {r : ℝ} (hr : 0 ≤ r) : eulerChar (closedBall x r) = 1 :=
  have := contractibleSpace_closedBall (x := x) hr
  eulerChar_of_contractibleSpace

end TauCeti

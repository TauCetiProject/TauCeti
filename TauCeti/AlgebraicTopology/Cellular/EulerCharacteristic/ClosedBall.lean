/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Topology.CWComplex.Classical.ClosedBall

/-!
# The Euler characteristic of a closed ball

A closed ball of nonnegative radius in a real normed space is contractible, so it has Euler
characteristic one. Its finite CW type is `TauCeti.finiteCWType_closedBall`.

## Main declarations

* `TauCeti.eulerChar_closedBall`: a closed ball of nonnegative radius has `χ = 1`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the Euler characteristic after Theorem 2.44.
-/

public section

open Metric

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A closed ball of nonnegative radius in a real normed space has Euler characteristic one. -/
@[simp]
theorem eulerChar_closedBall (x : E) {r : ℝ} (hr : 0 ≤ r) : eulerChar (closedBall x r) = 1 :=
  have := contractibleSpace_closedBall (x := x) hr
  eulerChar_of_contractibleSpace

end TauCeti

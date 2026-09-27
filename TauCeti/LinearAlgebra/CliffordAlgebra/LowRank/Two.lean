/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
-- Private: injectivity of the Clifford generator is used only in the dimension comparison.
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors

/-!
# Clifford algebras in dimension two

The odd component of a two-dimensional Clifford algebra consists entirely of vector generators.
Indeed, the generator image lies in the odd component, and both spaces have dimension two: the
generator is injective, while the odd component has dimension `2 ^ (2 - 1)`.

This is a general grading fact, independent of the Lipschitz and Spin groups.

## Main results

* `CliffordAlgebra.range_ι_eq_evenOdd_one_of_finrank_eq_two`: every odd Clifford element in
  dimension two is a vector generator.
-/

public section

open Module

namespace CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

/-- In dimension two, every odd Clifford element is a vector generator. -/
theorem range_ι_eq_evenOdd_one_of_finrank_eq_two (Q : QuadraticForm K V)
    (hV : finrank K V = 2) : LinearMap.range (ι Q) = evenOdd Q 1 := by
  let _ : FiniteDimensional K V :=
    FiniteDimensional.of_finrank_pos (by rw [hV]; decide)
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; decide)
  apply Submodule.eq_of_le_of_finrank_eq (range_ι_le_evenOdd_one Q)
  rw [LinearMap.finrank_range_of_inj (ι_injective Q), finrank_evenOdd Q, hV]
  norm_num

end CliffordAlgebra

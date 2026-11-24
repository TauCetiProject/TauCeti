/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut

/-!
# Continuity of conjugation by invertible matrices

Over a topological commutative semiring `R`, the inner automorphism `X ↦ g X g⁻¹` of the matrix
algebra (`Matrix.GeneralLinearGroup.innerAut`) depends continuously on `g ∈ GL n R`, as a map to
the space of maps of the matrix algebra with the topology of pointwise convergence: each value
`g X g⁻¹` is a product of continuous functions of `g` and `g⁻¹`, and the topology of `GL n R` is
that of the pair `(g, g⁻¹)`.

## Main results

* `Matrix.GeneralLinearGroup.continuous_innerAut`: conjugation by invertible matrices is
  continuous.
-/

public section

namespace Matrix.GeneralLinearGroup

/-- Conjugation by invertible matrices over a topological commutative semiring is continuous, as a
map to the space of maps of the matrix algebra with the topology of pointwise convergence. -/
theorem continuous_innerAut {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]
    [TopologicalSpace R] [IsTopologicalSemiring R] :
    Continuous fun g : GL n R => ⇑(innerAut g) := by
  refine continuous_pi fun X => ?_
  simp only [innerAut_apply]
  exact (Units.continuous_val.matrix_mul continuous_const).matrix_mul Units.continuous_coe_inv

end Matrix.GeneralLinearGroup

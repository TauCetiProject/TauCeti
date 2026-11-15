/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.TraceForm
public import Mathlib.Algebra.Lie.Matrix
import TauCeti.Algebra.Lie.OfAssociative
import TauCeti.LinearAlgebra.Matrix.Trace.LinearMap

/-!
# The Killing form of the general linear Lie algebra

The Killing form of `gl n R = Matrix n n R`, with the commutator bracket, is

`κ(X, Y) = 2 n trace (X * Y) - 2 trace X * trace Y`,

where `n` is the cardinality of the index type. The adjoint operator `ad X` is
`Z ↦ X * Z - Z * X`, so `ad X ∘ ad Y` is a combination of the operators `Z ↦ A * Z * B`
(`LieAlgebra.ad_comp_ad`), whose traces are `trace A * trace B`
(`Matrix.trace_mulLeft_comp_mulRight`). The formula holds over every commutative ring.

On trace-free matrices the second term vanishes. Combined with a projection onto a subalgebra,
the same computation gives the Killing form of the symplectic Lie algebra in
`TauCeti/Algebra/Lie/Symplectic/Killing.lean`.

## Main results

* `Matrix.killingForm_apply`: the Killing form of `gl n R`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter I (the Killing forms of the classical Lie algebras).
-/

public section

namespace Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- **The Killing form of `gl n R`**: `κ(X, Y) = 2 n trace (X * Y) - 2 trace X * trace Y`. -/
theorem killingForm_apply (X Y : Matrix n n R) :
    killingForm R (Matrix n n R) X Y =
      2 * Fintype.card n * (X * Y).trace - 2 * X.trace * Y.trace := by
  rw [killingForm_apply_apply, LieAlgebra.ad_comp_ad]
  simp only [map_add, map_sub, trace_mulLeft, trace_mulRight, trace_mulLeft_comp_mulRight,
    trace_mul_comm Y X]
  ring

end Matrix

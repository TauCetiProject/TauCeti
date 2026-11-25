/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.Killing
import TauCeti.Algebra.Lie.GeneralLinear.Killing
import TauCeti.Algebra.Lie.Killing.Subalgebra

/-!
# The Killing form of the special linear Lie algebra

The special linear Lie algebra `𝔰𝔩 n R = LieAlgebra.SpecialLinear.sl n R` is an ideal of
`𝔤𝔩 n R`, since commutators have trace zero, so over a principal ideal domain its Killing form is
the restriction of that of `𝔤𝔩 n R` (`LieSubalgebra.killingForm_eq_of_lie_mem`). By
`Matrix.killingForm_apply` this is `2 n trace (X * Y) - 2 trace X * trace Y`, and the second term
vanishes on trace-free matrices:

`κ(X, Y) = 2 n trace (X * Y)`

for `n` the cardinality of the index type.

## Main results

* `LieAlgebra.SpecialLinear.killingForm_apply`: `κ(X, Y) = 2 n trace (X * Y)` on `𝔰𝔩 n R`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§1.2 and 5.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter I (the Killing forms of the classical Lie algebras).
-/

public section

namespace LieAlgebra.SpecialLinear

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R]

/-- **The Killing form of `𝔰𝔩 n R`**: `κ(X, Y) = 2 n trace (X * Y)`, over a principal ideal
domain. -/
theorem killingForm_apply (X Y : sl n R) :
    killingForm R (sl n R) X Y = 2 * Fintype.card n * ((X : Matrix n n R) * Y).trace := by
  have hX : (X : Matrix n n R).trace = 0 := X.property
  rw [LieSubalgebra.killingForm_eq_of_lie_mem (sl n R) fun x _ y ↦
      LinearMap.mem_ker.2 <| matrix_trace_commutator_zero _ _ x y, Matrix.killingForm_apply, hX]
  ring

end LieAlgebra.SpecialLinear

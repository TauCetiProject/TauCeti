/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Trace

/-!
# Endomorphisms of a free module of rank two

An endomorphism `f` of a finite free module of rank two has characteristic polynomial
`X ^ 2 - tr(f) X + det(f)`, the basis-free form of Mathlib's `Matrix.charpoly_of_card_eq_two`.
Taking the trace of the Cayley–Hamilton identity `f ^ 2 - tr(f) f + det(f) = 0` gives
`tr(f²) = tr(f)² - 2 det(f)`, so that the characteristic polynomial is determined by the traces of
`f` and `f²` as soon as `2` is invertible. This is the case `n = 2` of Newton's identities, and it
is how a characteristic polynomial is computed from a trace formula.

## Main results

* `LinearMap.charpoly_of_finrank_eq_two`: `f.charpoly = X ^ 2 - C (tr f) * X + C (det f)`.
* `LinearMap.trace_mul_self_of_finrank_eq_two`: `tr (f * f) = tr f ^ 2 - 2 * det f`.
-/

public section

open Module Polynomial

namespace LinearMap

variable {R M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M]

/-- **The characteristic polynomial of an endomorphism of a free module of rank two** is
`X ^ 2 - tr(f) X + det(f)`. -/
theorem charpoly_of_finrank_eq_two (h : finrank R M = 2) (f : M →ₗ[R] M) :
    f.charpoly = X ^ 2 - C (trace R M f) * X + C (LinearMap.det f) := by
  let b := Module.finBasisOfFinrankEq R M h
  rw [← charpoly_toMatrix f b, Matrix.charpoly_fin_two, ← trace_eq_matrix_trace, det_toMatrix]

/-- **The trace of the square of an endomorphism of a free module of rank two**:
`tr(f²) = tr(f)² - 2 det(f)`, the trace of the Cayley–Hamilton identity
`f ^ 2 - tr(f) f + det(f) = 0`. -/
theorem trace_mul_self_of_finrank_eq_two (h : finrank R M = 2) (f : M →ₗ[R] M) :
    trace R M (f * f) = trace R M f ^ 2 - 2 * LinearMap.det f := by
  have hCH := congrArg (trace R M) (aeval_self_charpoly f)
  rw [charpoly_of_finrank_eq_two h] at hCH
  simp only [map_add, map_sub, map_mul, aeval_C, aeval_X, map_zero, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, map_smul, trace_one, h, smul_eq_mul, sq] at hCH
  push_cast at hCH
  linear_combination hCH

end LinearMap

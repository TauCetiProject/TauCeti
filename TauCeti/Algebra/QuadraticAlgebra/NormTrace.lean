/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant

/-!
# The algebra norm and trace of a quadratic algebra

`QuadraticAlgebra R a b` is free of rank two over `R`, on the basis `1, ω` with `ω² = a + bω`.
Its explicit norm `QuadraticAlgebra.norm` and trace `QuadraticAlgebra.trace` are the determinant
and the trace of multiplication on that basis, so they agree with the general `Algebra.norm` and
`Algebra.trace` of a finite free algebra.

These comparisons let the general theory of `Algebra.norm` (for instance surjectivity of the norm
of an extension of finite fields, or Hensel's lemma for the norm) be applied to the explicit norm
form `x² + bxy - ay²`.

## Main results

* `QuadraticAlgebra.algebraNorm_eq_norm`: `Algebra.norm R z = z.norm`.
* `QuadraticAlgebra.algebraTrace_eq_trace`: `Algebra.trace R _ z = trace z`.
-/

public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R}

/-- The algebra norm of `QuadraticAlgebra R a b` over `R` is its explicit norm
`z.re² + b z.re z.im - a z.im²`. -/
@[simp]
theorem algebraNorm_eq_norm (z : QuadraticAlgebra R a b) : Algebra.norm R z = z.norm := by
  rw [Algebra.norm_apply, ← det_toLinearMap_eq_norm]
  congr 1

/-- The algebra trace of `QuadraticAlgebra R a b` over `R` is its explicit trace
`2 z.re + b z.im`. -/
@[simp]
theorem algebraTrace_eq_trace (z : QuadraticAlgebra R a b) :
    Algebra.trace R (QuadraticAlgebra R a b) z = trace z := by
  rw [Algebra.trace_eq_matrix_trace (basis a b), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basis_apply_zero,
    basis_apply_one, trace_def]
  simp only [mul_one, basis_repr_apply, Matrix.cons_val_zero, Matrix.cons_val_one, im_mul,
    re_omega, im_omega]
  ring

end QuadraticAlgebra

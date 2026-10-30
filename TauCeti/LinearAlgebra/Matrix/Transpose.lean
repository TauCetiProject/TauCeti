/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Matrix.Basic

/-!
# Polynomials evaluated at a transpose

Evaluating a polynomial at the transpose of a square matrix gives the transpose of its value
(`Matrix.aeval_transpose`). This is the image of `Polynomial.aeval_algHom_apply` under Mathlib's
`Matrix.transposeAlgEquiv` to the opposite ring.
-/

public section

open Polynomial

namespace Matrix

variable {n R α : Type*} [Fintype n] [DecidableEq n] [CommSemiring R] [CommSemiring α]
  [Algebra R α]

/-- Evaluating a polynomial at the transpose of a matrix gives the transpose of its value. -/
theorem aeval_transpose (M : Matrix n n α) (q : R[X]) : aeval Mᵀ q = (aeval M q)ᵀ :=
  MulOpposite.op_injective <| by
    rw [← aeval_op_apply]
    exact aeval_algHom_apply (transposeAlgEquiv n R α) M q

end Matrix

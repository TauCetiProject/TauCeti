/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.LinearAlgebra.Pi

/-!
# Polynomial evaluation as a linear map

This file packages polynomial evaluation over a semiring `R` as an `R`-linear map
`Polynomial.evalLinearMap R : R[X] →ₗ[R] (R → R)`.
-/

public section

namespace Polynomial

/-- Evaluation of polynomials as an `R`-linear map `R[X] →ₗ[R] (R → R)`. -/
noncomputable def evalLinearMap (R : Type*) [Semiring R] : R[X] →ₗ[R] (R → R) :=
  LinearMap.pi fun r ↦ leval r

/-- Applying `evalLinearMap R` to a polynomial `p` and an element `r` evaluates `p` at `r`. -/
@[simp]
theorem evalLinearMap_apply (R : Type*) [Semiring R] (p : R[X]) (r : R) :
    evalLinearMap R p r = p.eval r := by
  simp [evalLinearMap]

end Polynomial

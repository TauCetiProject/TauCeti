/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Star.StarPolynomial
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Regression examples: noncommutative star polynomials

These examples exercise `TauCeti.StarPolynomial` over `ℂ`:

* the involution conjugates coefficients and reverses words;
* a generator is not self-adjoint, unlike in Mathlib's star structure on `FreeAlgebra`;
* evaluating at a family of complex matrices sends formal adjoints to conjugate transposes.
-/

open TauCeti StarPolynomial

-- The involution conjugates the coefficient and reverses the word.
example (c : ℂ) (i j : Fin 2) :
    star (c • X i * X j : StarPolynomial ℂ (Fin 2)) = star c • (star (X j) * star (X i)) := by
  simp [star_mul, star_smul]

-- The formal adjoint of a generator is a new variable.
example : star (X 0 : StarPolynomial ℂ (Fin 1)) ≠ X 0 :=
  star_X_ne_X 0

-- Evaluation at two complex matrices sends `X₀* X₁` to `a₀ᴴ a₁`.
example (a : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ) :
    lift (R := ℂ) a (star (X 0) * X 1) = (a 0).conjTranspose * a 1 := by
  simp [Matrix.star_eq_conjTranspose]

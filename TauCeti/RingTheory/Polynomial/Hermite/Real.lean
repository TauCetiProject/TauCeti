/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# The probabilists' Hermite polynomials over `ℝ`

Mathlib defines the probabilists' Hermite polynomials `Polynomial.hermite n` in `ℤ[X]`. Analytic
statements about them (Hermite functions, Gaussian `L²` bases) need the same family as real
polynomials. This file names the image of `Hₙ` in `ℝ[X]` and records how it evaluates and that it
keeps degree `n`. Nothing here involves a measure or an inner product.

## Main definitions

* `TauCeti.hermiteℝ` — `Hₙ` mapped into `ℝ[X]`.

## Main statements

* `TauCeti.eval_hermiteℝ` — evaluating `hermiteℝ n` at `x` is `aeval x (hermite n)`.
* `TauCeti.degree_hermiteℝ` — `hermiteℝ n` has degree exactly `n`.
-/

public section

namespace TauCeti

open Polynomial

/-- The probabilists' Hermite polynomial `Hₙ` as a real polynomial: the image of Mathlib's
`Polynomial.hermite n ∈ ℤ[X]` under the cast `ℤ → ℝ`. -/
noncomputable def hermiteℝ (n : ℕ) : Polynomial ℝ := (hermite n).map (Int.castRingHom ℝ)

/-- Evaluating `hermiteℝ n` at a real `x` is evaluating the integer polynomial `Hₙ` at `x`. -/
@[simp]
theorem eval_hermiteℝ (n : ℕ) (x : ℝ) : (hermiteℝ n).eval x = aeval x (hermite n) := by
  rw [hermiteℝ, ← algebraMap_int_eq, eval_map_algebraMap]

/-- `hermiteℝ n` has degree exactly `n`, as `Hₙ` does in `ℤ[X]`. -/
@[simp]
theorem degree_hermiteℝ (n : ℕ) : (hermiteℝ n).degree = (n : WithBot ℕ) := by
  rw [hermiteℝ, degree_map_eq_of_injective Int.cast_injective, degree_hermite]

end TauCeti

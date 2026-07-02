/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Real realizations of the Hermite polynomials

This file provides the real-polynomial realization of Mathlib's integer Hermite polynomials.
The probabilists' Hermite polynomial `Polynomial.hermite n` lives in `ℤ[X]`; `Polynomial.hermiteℝ`
is its image in `ℝ[X]`, with evaluation lemmas relating `eval` of that image to `aeval` of the
integer polynomial.
-/

public section

noncomputable section

namespace TauCeti

open Polynomial

/-- The probabilists' Hermite polynomial `hermite n`, realised as a real polynomial. -/
@[expose]
def _root_.Polynomial.hermiteℝ (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

/-- The defining equation for `Polynomial.hermiteℝ`. -/
theorem _root_.Polynomial.hermiteℝ_def (n : ℕ) :
    hermiteℝ n = (hermite n).map (Int.castRingHom ℝ) :=
  rfl

/-- Evaluating the `ℝ`-realisation of an integer polynomial agrees with `aeval` of the
original. -/
private theorem eval_map_intCast (x : ℝ) (q : ℤ[X]) :
    (q.map (Int.castRingHom ℝ)).eval x = aeval x q := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq]

/-- Evaluating the real-polynomial realization of `hermite n` agrees with evaluating the original
integer polynomial by `aeval`. -/
@[simp]
theorem _root_.Polynomial.eval_hermiteℝ (x : ℝ) (n : ℕ) :
    (hermiteℝ n).eval x = aeval x (hermite n) :=
  eval_map_intCast x (hermite n)

/-- The `aeval` form of `eval_hermiteℝ`. -/
@[simp]
theorem _root_.Polynomial.aeval_hermiteℝ (x : ℝ) (n : ℕ) :
    aeval x (hermiteℝ n) = aeval x (hermite n) := by
  rw [coe_aeval_eq_eval, eval_hermiteℝ]

end TauCeti

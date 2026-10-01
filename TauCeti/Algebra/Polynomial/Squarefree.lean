/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Squarefree.Basic

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Simple roots of squarefree polynomials

A squarefree polynomial has nonzero derivative at every root in its coefficient ring.
This supplies the pointwise simple-root premise of `TauCeti.Sturm.IsAlternating.sum_sign`,
which requires `p.derivative.eval r ≠ 0` at each root `r` in the interval.
-/

public section

open Polynomial

namespace Squarefree

/-- A squarefree polynomial has nonzero derivative at every root in its coefficient ring. -/
theorem eval_derivative_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    {p : R[X]} (hp : Squarefree p) {x : R} (hx : p.eval x = 0) :
    p.derivative.eval x ≠ 0 := by
  obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr hx
  intro h
  have hq : q.eval x = 0 := by
    simpa using h
  obtain ⟨s, hs⟩ := dvd_iff_isRoot.mpr hq
  exact not_isUnit_X_sub_C x (hp (X - C x) ⟨s, by rw [hs, mul_assoc]⟩)

end Squarefree

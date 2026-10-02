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
import Mathlib.FieldTheory.Separable
import TauCeti.Algebra.Squarefree

/-! # Simple roots of squarefree polynomials

A squarefree polynomial has nonzero derivative at every root in its coefficient ring.
This supplies the pointwise simple-root premise of `TauCeti.Sturm.IsAlternating.sum_sign`,
which requires `p.derivative.eval r ≠ 0` at each root `r` in the interval.

The file also records that `-(X ^ 2 + 1)` is squarefree over a field of characteristic other than
two, the polynomial of the conic `x ^ 2 + y ^ 2 + 1 = 0` in the form `y ^ 2 = f(x)`.
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

namespace TauCeti.Polynomial

/-- `-(X ^ 2 + 1)` is squarefree over a field in which `2 ≠ 0`: `X ^ 2 + 1 = X ^ 2 - C (-1)` is
separable there. -/
theorem squarefree_neg_X_sq_add_one {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) :
    Squarefree (-(X ^ 2 + 1) : k[X]) := by
  have h : (X ^ 2 + 1 : k[X]) = X ^ 2 - C (-1) := by rw [C_neg, C_1, sub_neg_eq_add]
  rw [h]
  exact (separable_X_pow_sub_C (-1) (by exact_mod_cast h2)
    (neg_ne_zero.mpr one_ne_zero)).squarefree.neg

end TauCeti.Polynomial

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.OfFn

/-!
# Recovering a polynomial of bounded degree from its coefficient vector

`Polynomial.ofFn n` and `Polynomial.toFn n` pass between vectors of length `n` and polynomials.
Mathlib records that a polynomial of `natDegree` below `n` is recovered from its first `n`
coefficients; this file states the same recovery in terms of `degree`, so that it also applies
to the zero polynomial.  This is the form needed when a coefficient vector of prescribed length
is read off a polynomial that may vanish.
-/

public section

namespace TauCeti

open Polynomial

variable {R : Type*} [Semiring R] [DecidableEq R]

/-- A polynomial of degree below `n` is recovered from its vector of first `n` coefficients.
This is the `degree` form of `Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt`, which also covers
the zero polynomial. -/
theorem _root_.Polynomial.ofFn_comp_toFn_eq_id_of_degree_lt {n : ℕ} {p : R[X]} (h : p.degree < n) :
    ofFn n (toFn n p) = p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · exact ofFn_comp_toFn_eq_id_of_natDegree_lt ((natDegree_lt_iff_degree_lt hp).mpr h)

end TauCeti

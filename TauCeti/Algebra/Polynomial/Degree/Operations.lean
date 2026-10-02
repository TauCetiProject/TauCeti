/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Degree bounds for products and sums of products of polynomials

Mathlib's `Polynomial.degree_mul_le` bounds the degree of a product by the sum of the degrees.
This file records the strict form with one factor of degree below a natural number `a` and the
other of `natDegree` at most `n`: the product has degree below `a + n`.  Stating the bound with
`degree` on the strict side lets the zero polynomial through on either side, which is what a
coefficient window of prescribed length needs when it is read off polynomials that may vanish.

`TauCeti.degree_mul_add_mul_lt_of_degree_lt_of_natDegree_le` combines two such product bounds
into the coefficient window used for polynomial relations with formal degree bounds `m` and `n`.
-/

public section

namespace TauCeti

open Polynomial

variable {R : Type*} [Semiring R]

/-- The product of a polynomial of degree below `a` with one of degree at most `n` has degree
below `a + n`; the zero polynomial is allowed on either side. -/
theorem _root_.Polynomial.degree_mul_lt_of_degree_lt_of_natDegree_le {A q : R[X]} {a n : ℕ}
    (hA : A.degree < a) (hq : q.natDegree ≤ n) :
    (A * q).degree < ((a + n : ℕ) : WithBot ℕ) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  · calc (A * q).degree ≤ A.degree + q.degree := degree_mul_le A q
      _ < (a : WithBot ℕ) + n :=
        WithBot.add_lt_add_of_lt_of_le (degree_ne_bot.mpr hq0) hA (degree_le_of_natDegree_le hq)
      _ = ((a + n : ℕ) : WithBot ℕ) := by push_cast; rfl

/-- A relation with multipliers of degrees below `m - j` and `n - j` has degree below
`(m - j) + (n - j) + j`, provided the input degrees are bounded by `m` and `n` and `j` lies
below both bounds. Either input or multiplier may be zero. -/
theorem degree_mul_add_mul_lt_of_degree_lt_of_natDegree_le {p q A B : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (hjm : j ≤ m) (hjn : j ≤ n)
    (hA : A.degree < (m - j : ℕ)) (hB : B.degree < (n - j : ℕ)) :
    (A * q + B * p).degree < (((m - j) + (n - j) + j : ℕ) : WithBot ℕ) := by
  apply (degree_add_le _ _).trans_lt
  apply max_lt
  · exact (degree_mul_lt_of_degree_lt_of_natDegree_le hA hn).trans_le
      (WithBot.coe_le_coe.mpr (by omega : m - j + n ≤ (m - j) + (n - j) + j))
  · exact (degree_mul_lt_of_degree_lt_of_natDegree_le hB hm).trans_le
      (WithBot.coe_le_coe.mpr (by omega : n - j + m ≤ (m - j) + (n - j) + j))

end TauCeti

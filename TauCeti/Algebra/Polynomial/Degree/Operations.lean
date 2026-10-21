/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Degrees of polynomial sums and products

Mathlib's `Polynomial.degree_mul_le` bounds the degree of a product by the sum of the degrees.
This file records the strict form with one factor of degree below a natural number `a` and the
other of `natDegree` at most `n`: the product has degree below `a + n`.  Stating the bound with
`degree` on the strict side lets the zero polynomial through on either side, which is what a
coefficient window of prescribed length needs when it is read off polynomials that may vanish.

`TauCeti.degree_mul_add_mul_lt_of_degree_lt_of_natDegree_le` combines two such product bounds
into the coefficient window used for polynomial relations with formal degree bounds `m` and `n`.
`Polynomial.natDegree_multiset_prod_X_sub_C_le` bounds the degree of a product of `card s` monic
linear factors by `card s` over any commutative ring, without the nontriviality that Mathlib's
`Polynomial.natDegree_multiset_prod_X_sub_C_eq_card` needs.
`Polynomial.natDegree_X_pow_add_C_mul_X_add_C` reads off the degree of the trinomial
`X ^ n + C a * X + C b` for `2 ≤ n`. `Polynomial.sub_C_ne_zero` records that a nonconstant
polynomial differs from every constant polynomial.
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

/-- A product of `card s` monic linear factors has degree at most `card s`; unlike
`natDegree_multiset_prod_X_sub_C_eq_card`, this needs no nontriviality. -/
theorem _root_.Polynomial.natDegree_multiset_prod_X_sub_C_le {S : Type*} [CommRing S]
    (s : Multiset S) : (s.map fun a ↦ X - C a).prod.natDegree ≤ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm]
    exact natDegree_mul_le.trans (add_le_add (natDegree_X_sub_C_le a) ih)

/-- A nonconstant polynomial differs from every constant polynomial. -/
theorem _root_.Polynomial.sub_C_ne_zero {S : Type*} [Ring S] {p : S[X]} (hp : 0 < p.natDegree)
    (a : S) : p - C a ≠ 0 :=
  ne_zero_of_natDegree_gt (n := 0) (by rwa [natDegree_sub_C])

/-- For `2 ≤ n`, the trinomial `X ^ n + C a * X + C b` has degree `n`. -/
theorem _root_.Polynomial.natDegree_X_pow_add_C_mul_X_add_C [Nontrivial R] (a b : R) {n : ℕ}
    (hn : 2 ≤ n) : (X ^ n + C a * X + C b).natDegree = n := by
  rw [add_assoc, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_linear_le.trans_lt (by exact_mod_cast (by omega : 1 < n))

end TauCeti

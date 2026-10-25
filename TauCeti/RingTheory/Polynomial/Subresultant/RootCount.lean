/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Roots
public import TauCeti.RingTheory.Polynomial.Subresultant.GCD

/-!
# Counting roots with principal subresultant coefficients

This file reads root counts off the principal subresultant coefficients, through the
principal-subresultant gcd criterion `Polynomial.natDegree_gcd_eq_iff_psc`.

For two nonzero polynomials `p` and `q`, the first nonzero principal coefficient of `(p, q)`
occurs at the number of their common roots, each counted with the minimum of its multiplicities
in `p` and in `q`. For a polynomial in characteristic zero, the first nonzero principal
coefficient of `(p, p')` occurs at the degree of the derivative gcd; subtracting that index from
the polynomial's degree gives the number of distinct roots.

The coefficient bounds are the actual degrees, as required by the fixed-bound subresultant
convention.

## Main results

* `Polynomial.card_roots_inter_eq_iff_psc_of_splits`: the principal-coefficient characterization
  of the number of common roots, when one input splits.
* `Polynomial.card_aroots_inter_eq_iff_psc`: the same for the common roots in an algebraically
  closed field of two polynomials over a field `k`, with the principal coefficients taken over
  `k`.
* `Polynomial.card_roots_toFinset_eq_iff_psc_of_splits`: the principal-coefficient
  characterization of the number of distinct roots of any split polynomial.
* `Polynomial.card_roots_toFinset_eq_iff_psc`: the specialization to an algebraically closed
  coefficient field.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapter 4, Proposition 4.25 and Corollary 4.26.
-/

public section

namespace TauCeti

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

section CommonRoots

/-- For nonzero `p` and `q` with `p` split, `r` is the number of common roots of `p` and `q`,
each counted with the minimum of its two multiplicities, exactly when the principal subresultant
coefficient at index `r` is the first nonzero one. -/
theorem _root_.Polynomial.card_roots_inter_eq_iff_psc_of_splits {p q : K[X]} (hp : p ≠ 0)
    (hq : q ≠ 0) (hsplit : p.Splits) (r : ℕ) :
    Multiset.card (p.roots ∩ q.roots) = r ↔
      psc p q p.natDegree q.natDegree r ≠ 0 ∧ ∀ i < r, psc p q p.natDegree q.natDegree i = 0 := by
  rw [← natDegree_gcd_eq_card_roots_inter_of_splits hp hq hsplit, natDegree_gcd_eq_iff_psc]

/-- For nonzero polynomials `p` and `q` over a field `k`, `r` is the number of their common roots
in an algebraically closed field `K`, each counted with the minimum of its two multiplicities,
exactly when the principal subresultant coefficient over `k` at index `r` is the first nonzero
one. -/
theorem _root_.Polynomial.card_aroots_inter_eq_iff_psc [IsAlgClosed K] {k : Type*} [Field k]
    [Algebra k K] {p q : k[X]} (hp : p ≠ 0) (hq : q ≠ 0) (r : ℕ) :
    Multiset.card (p.aroots K ∩ q.aroots K) = r ↔
      psc p q p.natDegree q.natDegree r ≠ 0 ∧ ∀ i < r, psc p q p.natDegree q.natDegree i = 0 := by
  classical
  rw [← natDegree_gcd_eq_card_aroots_inter hp hq, natDegree_gcd_eq_iff_psc]

end CommonRoots

variable [CharZero K]

/-- For a split polynomial, `r` is the number of distinct roots exactly when the principal
subresultant coefficient at index `degree - r` is the first nonzero one. -/
theorem _root_.Polynomial.card_roots_toFinset_eq_iff_psc_of_splits {p : K[X]} (hp : p ≠ 0)
    (hsplit : p.Splits) (r : ℕ) (hr : r ≤ p.natDegree) :
    p.roots.toFinset.card = r ↔
      psc p p.derivative p.natDegree p.derivative.natDegree (p.natDegree - r) ≠ 0 ∧
        ∀ i < p.natDegree - r,
          psc p p.derivative p.natDegree p.derivative.natDegree i = 0 := by
  rw [← natDegree_gcd_eq_iff_psc]
  have hg : (EuclideanDomain.gcd p p.derivative).natDegree ≤ p.natDegree :=
    natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_left p p.derivative) hp
  have hcount :=
    natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset_of_splits hp hsplit
  omega

section IsAlgClosed

variable [IsAlgClosed K]

/-- Over an algebraically closed field, `r` is the number of distinct roots exactly when the
principal subresultant coefficient at index `degree - r` is the first nonzero one. -/
theorem _root_.Polynomial.card_roots_toFinset_eq_iff_psc {p : K[X]} (hp : p ≠ 0)
    (r : ℕ) (hr : r ≤ p.natDegree) :
    p.roots.toFinset.card = r ↔
      psc p p.derivative p.natDegree p.derivative.natDegree (p.natDegree - r) ≠ 0 ∧
        ∀ i < p.natDegree - r,
          psc p p.derivative p.natDegree p.derivative.natDegree i = 0 :=
  card_roots_toFinset_eq_iff_psc_of_splits hp (IsAlgClosed.splits p) r hr

end IsAlgClosed

end TauCeti

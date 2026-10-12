/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Roots
public import TauCeti.RingTheory.Polynomial.Subresultant.GCD

/-!
# Counting distinct roots with principal subresultant coefficients

For a polynomial that splits in a characteristic-zero field, this file characterizes any proposed
number of distinct roots by the principal subresultant coefficients of the polynomial and its
derivative.  The first nonzero principal coefficient occurs at the degree of the derivative gcd;
subtracting that index from the polynomial's degree gives the number of distinct roots.

This is the root-count form of the principal-subresultant gcd criterion.  It keeps actual degrees
in the coefficient bounds, as required by the fixed-bound subresultant convention.

## Main results

* `Polynomial.card_roots_toFinset_eq_iff_psc_of_splits`: the principal-coefficient
  characterization for any split polynomial.
* `Polynomial.card_roots_toFinset_eq_iff_psc`: the specialization to an algebraically closed
  coefficient field.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapter 4, Proposition 4.25 and Corollary 4.26.
-/

public section

namespace TauCeti

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

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

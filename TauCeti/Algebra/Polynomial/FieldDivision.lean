/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.LinearCombination

/-!
# Linear relations between polynomials over a field

A relation `A * q + B * p = 0` between polynomials over a field says that `p` divides `A * q`;
by the Bézout identity for the gcd, `p` then divides `A * gcd p q`.  So a nonzero `A` in such a
relation has degree at least `deg p - deg (gcd p q)`: this is the degree bound behind the
nonvanishing of the principal subresultant coefficient at the degree of the gcd.
-/

public section

namespace TauCeti

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- In a relation `A * q + B * p = 0`, if `A` has degree below `deg p - deg (gcd p q)`, then
`A = 0`. -/
theorem _root_.Polynomial.eq_zero_of_mul_add_mul_eq_zero_of_degree_lt {p q A B : K[X]}
    (hAB : A * q + B * p = 0)
    (hA : A.degree < ((p.natDegree - (EuclideanDomain.gcd p q).natDegree : ℕ) : WithBot ℕ)) :
    A = 0 := by
  by_contra hA0
  have hlt := (natDegree_lt_iff_degree_lt hA0).mpr hA
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hlt
  have hg : EuclideanDomain.gcd p q ≠ 0 := fun h => hp (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  -- Bézout: `A * gcd p q = A * (p * gcdA p q + q * gcdB p q)` is a multiple of `p`.
  have hdvd : p ∣ A * EuclideanDomain.gcd p q :=
    ⟨A * EuclideanDomain.gcdA p q - B * EuclideanDomain.gcdB p q, by
      rw [EuclideanDomain.gcd_eq_gcd_ab]
      linear_combination EuclideanDomain.gcdB p q * hAB⟩
  have := (natDegree_le_of_dvd hdvd (mul_ne_zero hA0 hg)).trans natDegree_mul_le
  omega

end TauCeti

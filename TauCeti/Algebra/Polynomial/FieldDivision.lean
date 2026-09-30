/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.LinearCombination

/-!
# Polynomial remainders and linear relations over a field

A relation `A * q + B * p = 0` between polynomials over a field says that `A * q` is divisible by
`p`; dividing by the gcd of `p` and `q` leaves coprime quotients, so in fact `p / gcd p q` divides
`A`.  So a nonzero `A` in such a relation has degree at least `deg p - deg (gcd p q)`: this is the
degree bound behind the nonvanishing of the principal subresultant coefficient at the degree of
the gcd.

At a root of the divisor, evaluating a field remainder gives the same value as evaluating the
dividend. This supplies the remainder evaluation used in the local sign-change law for Sturm
variations.
-/

public section

namespace TauCeti

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- In a relation `A * q + B * p = 0` with `p ≠ 0`, if `A` has degree below
`deg p - deg (gcd p q)`, then `A = 0`: dividing by the gcd leaves coprime quotients, so
`p / gcd p q` divides `A`. -/
theorem _root_.Polynomial.eq_zero_of_mul_add_mul_eq_zero_of_degree_lt {p q A B : K[X]}
    (hp : p ≠ 0) (hAB : A * q + B * p = 0)
    (hA : A.degree < ((p.natDegree - (EuclideanDomain.gcd p q).natDegree : ℕ) : WithBot ℕ)) :
    A = 0 := by
  set g := EuclideanDomain.gcd p q
  have hg0 : g ≠ 0 := fun h => hp (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hp' : g * (p / g) = p :=
    EuclideanDomain.mul_div_cancel' hg0 (EuclideanDomain.gcd_dvd_left p q)
  have hq' : g * (q / g) = q :=
    EuclideanDomain.mul_div_cancel' hg0 (EuclideanDomain.gcd_dvd_right p q)
  -- Mathlib states the coprimality of the gcd quotients for `GCDMonoid.gcd`; the `GCDMonoid`
  -- structure `EuclideanDomain.gcdMonoid` has `GCDMonoid.gcd = EuclideanDomain.gcd` by definition.
  have hcop : IsCoprime (p / g) (q / g) :=
    letI := EuclideanDomain.gcdMonoid K[X]
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
  have hrel : A * (q / g) + B * (p / g) = 0 := by
    refine mul_left_cancel₀ hg0 ?_
    calc g * (A * (q / g) + B * (p / g)) = A * (g * (q / g)) + B * (g * (p / g)) := by ring
      _ = A * q + B * p := by rw [hp', hq']
      _ = g * 0 := by rw [hAB, mul_zero]
  have hpA : p / g ∣ A := hcop.dvd_of_dvd_mul_right ⟨-B, by linear_combination hrel⟩
  have hp'0 : p / g ≠ 0 := by
    intro h
    rw [h, mul_zero] at hp'
    exact hp hp'.symm
  refine eq_zero_of_dvd_of_degree_lt hpA (hA.trans_le ?_)
  rw [degree_eq_natDegree hp'0]
  have := natDegree_mul hg0 hp'0
  rw [hp'] at this
  exact WithBot.coe_le_coe.mpr (by omega : p.natDegree - g.natDegree ≤ (p / g).natDegree)

end TauCeti

namespace TauCeti.Polynomial

open _root_.Polynomial

variable {K : Type*} [Field K]

/-- At a root of the divisor, the remainder and dividend have the same value. -/
theorem eval_mod_of_eval_eq_zero {p q : K[X]} {x : K} (hq : q.eval x = 0) :
    (p % q).eval x = p.eval x := by
  simp [EuclideanDomain.mod_eq_sub_mul_div, hq]

end TauCeti.Polynomial

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Polynomial.Degree.Operations

/-!
# Linear relations between polynomials over a field

A relation `A * q + B * p = 0` between polynomials over a field says that `p` divides `A * q`;
by the Bézout identity for the gcd, `p` then divides `A * gcd p q`.  So a nonzero `A` in such a
relation has degree at least `deg p - deg (gcd p q)`: this is the degree bound behind the
nonvanishing of the principal subresultant coefficient at the degree of the gcd.

A relation of this form is also forced by the vanishing of a window of coefficients
(`Polynomial.mul_add_mul_eq_zero_of_coeff_window`).
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

omit [DecidableEq K] in
/-- A relation `A * q + B * p = 0` is forced by the vanishing of the window of coefficients in
degrees `d, …, m + n - d - 1`, where `d` is the degree of a common divisor `g` of `p` and `q` and
`A`, `B` have degrees below `m - d` and `n - d`: the combination then has degree below `d`, so
the divisor `g` forces it to vanish. -/
theorem _root_.Polynomial.mul_add_mul_eq_zero_of_coeff_window {p q A B g : K[X]}
    {m n : ℕ} (hp : p ≠ 0)
    (hm : p.natDegree = m) (hn : q.natDegree ≤ n) (hgp : g ∣ p) (hgq : g ∣ q) (hg0 : g ≠ 0)
    (hAdeg : A.degree < (m - g.natDegree : ℕ)) (hBdeg : B.degree < (n - g.natDegree : ℕ))
    (hwin : ∀ i : Fin ((m - g.natDegree) + (n - g.natDegree)),
      (A * q + B * p).coeff (i + g.natDegree) = 0) :
    A * q + B * p = 0 := by
  set d := g.natDegree with hd
  have hdm : d ≤ m := hm ▸ natDegree_le_of_dvd hgp hp
  have hsumdeg : (A * q + B * p).degree < ((m - d) + (n - d) + d : ℕ) := by
    rcases eq_or_ne q 0 with rfl | hq0
    · rw [mul_zero, zero_add]
      exact (degree_mul_lt_of_degree_lt_of_natDegree_le hBdeg hm.le).trans_le
        (WithBot.coe_le_coe.mpr (by omega : n - d + m ≤ m - d + (n - d) + d))
    · exact degree_mul_add_mul_lt_of_degree_lt_of_natDegree_le hm.le hn hdm
        ((natDegree_le_of_dvd hgq hq0).trans hn) hAdeg hBdeg
  have hdeg : (A * q + B * p).degree < d := by
    rw [degree_lt_iff_coeff_zero]
    intro e he
    by_cases hlt : e < (m - d) + (n - d) + d
    · have := hwin ⟨e - d, by omega⟩
      rwa [Nat.sub_add_cancel he] at this
    · apply coeff_eq_zero_of_degree_lt
      exact hsumdeg.trans_le (WithBot.coe_le_coe.mpr
        (by omega : (m - d) + (n - d) + d ≤ e))
  exact eq_zero_of_dvd_of_degree_lt
    (dvd_add (dvd_mul_of_dvd_right hgq _) (dvd_mul_of_dvd_right hgp _))
    (by rw [degree_eq_natDegree hg0]; exact hdeg)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import TauCeti.RingTheory.Polynomial.Subresultant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import TauCeti.Algebra.Polynomial.Degree.Operations
import TauCeti.Algebra.Polynomial.FieldDivision
import TauCeti.Algebra.Polynomial.OfFn

/-!
# The subresultant gcd criterion

Over a field, the principal subresultant coefficients of two polynomials locate the degree of
their greatest common divisor: taken at the actual degree of the nonzero left polynomial and at
any bound dominating the degree of the right one, they vanish at every index below the degree
of the gcd and are nonzero at that degree.  Hence, at the actual degrees of any two polynomials,
the degree of the gcd is the least index with a nonzero principal subresultant coefficient.

Both halves read the principal subresultant matrix as the linear map `(A, B) ↦ A * q + B * p` on
polynomials of bounded degree, through `Polynomial.subresultantMatrix_mulVec`.  A common factor
of degree `d > j` supplies the kernel vector `(p / g, -(q / g))` at index `j`; at index `d`, a
kernel vector is a relation `A * q + B * p = 0` whose degrees are too small for a nonzero
solution, by the Bézout identity for the gcd.

## Main results

* `Polynomial.psc_eq_zero_of_mul_add_mul_eq_zero`: a nontrivial relation `A * q + B * p = 0` with
  `A` and `B` of degrees below `m - j` and `n - j` forces the principal coefficient at `j` to
  vanish.
* `Polynomial.psc_eq_zero_of_lt_natDegree_gcd`: the principal coefficients vanish below the
  degree of the gcd.
* `Polynomial.psc_natDegree_gcd_ne_zero`: the principal coefficient at the degree of the gcd is
  nonzero.
* `Polynomial.natDegree_gcd_eq_iff_psc`: the degree of the gcd is the least index with a nonzero
  principal subresultant coefficient.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapter 4, Proposition 4.25 and Corollary 4.26.
* Q. Vermande, *Cylindrical Algebraic Decomposition in Coq/Rocq*, §3.
-/

public section

namespace TauCeti

open _root_.Polynomial

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A nontrivial relation `A * q + B * p = 0`, with `A` and `B` of degrees below `m - j` and
`n - j`, is a kernel vector of the principal subresultant matrix at index `j`, so the principal
subresultant coefficient vanishes there. -/
theorem _root_.Polynomial.psc_eq_zero_of_mul_add_mul_eq_zero {p q A B : R[X]} {m n j : ℕ}
    (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hA : A.degree < (m - j : ℕ)) (hB : B.degree < (n - j : ℕ))
    (hAB : A * q + B * p = 0) (hne : A ≠ 0 ∨ B ≠ 0) :
    psc p q m n j = 0 := by
  classical
  rw [psc_def, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨Fin.append (toFn (m - j) A) (toFn (n - j) B), fun h0 => ?_, ?_⟩
  · have hA0 : toFn (m - j) A = 0 := funext fun k => by
      simpa using congrFun h0 (Fin.castAdd (n - j) k)
    have hB0 : toFn (n - j) B = 0 := funext fun k => by
      simpa using congrFun h0 (Fin.natAdd (m - j) k)
    rcases hne with hne | hne
    · exact hne (by rw [← ofFn_comp_toFn_eq_id_of_degree_lt hA, hA0, map_zero])
    · exact hne (by rw [← ofFn_comp_toFn_eq_id_of_degree_lt hB, hB0, map_zero])
  · funext i
    rw [subresultantMatrix_mulVec hm hn]
    simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]
    rw [ofFn_comp_toFn_eq_id_of_degree_lt hA, ofFn_comp_toFn_eq_id_of_degree_lt hB, hAB, coeff_zero]

end Domain

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- Below the degree of the gcd, the principal subresultant coefficients vanish, at any formal
degree bounds dominating the actual degrees. -/
theorem _root_.Polynomial.psc_eq_zero_of_lt_natDegree_gcd {p q : K[X]}
    {m n j : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (hj : j < (EuclideanDomain.gcd p q).natDegree) : psc p q m n j = 0 := by
  set g := EuclideanDomain.gcd p q
  have hg0 : g ≠ 0 := by
    rintro h
    rw [h, natDegree_zero] at hj
    exact absurd hj (Nat.not_lt_zero j)
  have hpg : g * (p / g) = p :=
    EuclideanDomain.mul_div_cancel' hg0 (EuclideanDomain.gcd_dvd_left p q)
  have hqg : g * (q / g) = q :=
    EuclideanDomain.mul_div_cancel' hg0 (EuclideanDomain.gcd_dvd_right p q)
  -- The degree of a quotient by `g` drops by `g.natDegree`, so both quotients fit the bounds.
  have hdeg : ∀ {r : K[X]} {k : ℕ}, r.natDegree ≤ k → g * (r / g) = r →
      (r / g).degree < (k - j : ℕ) := by
    intro r k hk hrg
    rcases eq_or_ne r 0 with rfl | hr
    · rw [EuclideanDomain.zero_div, degree_zero]
      exact WithBot.bot_lt_coe _
    · have hrg0 : r / g ≠ 0 := by
        rintro h
        rw [h, mul_zero] at hrg
        exact hr hrg.symm
      have := natDegree_mul hg0 hrg0
      rw [hrg] at this
      exact (natDegree_lt_iff_degree_lt hrg0).mp (by omega)
  refine psc_eq_zero_of_mul_add_mul_eq_zero (A := p / g) (B := -(q / g)) hm hn (hdeg hm hpg)
    (by rw [degree_neg]; exact hdeg hn hqg) ?_ ?_
  · rw [neg_mul, ← sub_eq_add_neg, sub_eq_zero]
    calc p / g * q = p / g * (g * (q / g)) := by rw [hqg]
      _ = q / g * (g * (p / g)) := by ring
      _ = q / g * p := by rw [hpg]
  · rcases eq_or_ne p 0 with rfl | hp
    · have hq : q ≠ 0 := fun h => hg0 (EuclideanDomain.gcd_eq_zero_iff.mpr ⟨rfl, h⟩)
      refine Or.inr (neg_ne_zero.mpr fun h => hq ?_)
      rw [h, mul_zero] at hqg
      exact hqg.symm
    · refine Or.inl fun h => hp ?_
      rw [h, mul_zero] at hpg
      exact hpg.symm

/-- At the degree of the gcd, the principal subresultant coefficient is nonzero, provided the left
bound is the actual degree of the nonzero left polynomial and the right bound dominates the degree
of the right polynomial. -/
theorem _root_.Polynomial.psc_natDegree_gcd_ne_zero {p q : K[X]} {m n : ℕ}
    (hp : p ≠ 0) (hm : p.natDegree = m) (hn : q.natDegree ≤ n) :
    psc p q m n (EuclideanDomain.gcd p q).natDegree ≠ 0 := by
  set g := EuclideanDomain.gcd p q with hg
  clear_value g
  set d := g.natDegree with hd
  clear_value d
  have hgp : g ∣ p := hg ▸ EuclideanDomain.gcd_dvd_left p q
  have hgq : g ∣ q := hg ▸ EuclideanDomain.gcd_dvd_right p q
  have hg0 : g ≠ 0 := fun h => hp (EuclideanDomain.gcd_eq_zero_iff.mp (hg ▸ h)).1
  have hdm : d ≤ m := hd ▸ hm ▸ natDegree_le_of_dvd hgp hp
  rw [psc_def, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv, hMv⟩
  -- The kernel vector encodes a relation `A * q + B * p` with no coefficients in degrees
  -- `d, …, m + n - d - 1` and degree below `m + n - d`, hence of degree below `d = deg g`.
  have hwin (i : Fin ((m - d) + (n - d))) :
      (ofFn (m - d) (fun k => v (Fin.castAdd (n - d) k)) * q +
        ofFn (n - d) (fun k => v (Fin.natAdd (m - d) k)) * p).coeff (i + d) = 0 := by
    rw [← subresultantMatrix_mulVec hm.le hn, hMv, Pi.zero_apply]
  generalize hA : ofFn (m - d) (fun k => v (Fin.castAdd (n - d) k)) = A at hwin
  generalize hB : ofFn (n - d) (fun k => v (Fin.natAdd (m - d) k)) = B at hwin
  have hAdeg : A.degree < (m - d : ℕ) := hA ▸ ofFn_degree_lt _
  have hBdeg : B.degree < (n - d : ℕ) := hB ▸ ofFn_degree_lt _
  have hdeg : (A * q + B * p).degree < d := by
    rw [degree_lt_iff_coeff_zero]
    intro e he
    by_cases hlt : e < (m - d) + (n - d) + d
    · have := hwin ⟨e - d, by omega⟩
      rwa [Nat.sub_add_cancel he] at this
    · apply coeff_eq_zero_of_degree_lt
      refine lt_of_lt_of_le ((degree_add_le _ _).trans_lt (max_lt ?_ ?_)) (WithBot.coe_le_coe.mpr
        (by omega : (m - d) + (n - d) + d ≤ e))
      · rcases eq_or_ne q 0 with rfl | hq0
        · simp
        · have hdn : d ≤ n := hd ▸ (natDegree_le_of_dvd hgq hq0).trans hn
          exact (degree_mul_lt_of_degree_lt_of_natDegree_le hAdeg hn).trans_le
            (WithBot.coe_le_coe.mpr (by omega : m - d + n ≤ m - d + (n - d) + d))
      · exact (degree_mul_lt_of_degree_lt_of_natDegree_le hBdeg hm.le).trans_le
          (WithBot.coe_le_coe.mpr (by omega : n - d + m ≤ m - d + (n - d) + d))
  have hzero : A * q + B * p = 0 :=
    eq_zero_of_dvd_of_degree_lt (dvd_add (dvd_mul_of_dvd_right hgq _) (dvd_mul_of_dvd_right hgp _))
      (by rw [degree_eq_natDegree hg0, ← hd]; exact hdeg)
  -- Divide the relation by `g` and use Bézout to see that `A = 0`, then `B = 0`.
  have hA0 : A = 0 :=
    eq_zero_of_mul_add_mul_eq_zero_of_degree_lt hp hzero (by rw [hm, ← hg, ← hd]; exact hAdeg)
  have hB0 : B = 0 := by
    rw [hA0, zero_mul, zero_add] at hzero
    exact (mul_eq_zero.mp hzero).resolve_right hp
  -- Both coefficient blocks of `v` vanish.
  apply hv
  rw [hA0] at hA
  rw [hB0] at hB
  have h1 := injective_ofFn (m - d) (hA.trans (map_zero _).symm)
  have h2 := injective_ofFn (n - d) (hB.trans (map_zero _).symm)
  funext i
  induction i using Fin.addCases with
  | left k => exact congrFun h1 k
  | right k => exact congrFun h2 k

/-- The subresultant gcd criterion: at the actual degrees, the degree of the gcd of `p` and `q`
is the least index with nonzero principal subresultant coefficient.  When `p = 0`, the gcd is `q`
and the criterion reads off the empty terminal determinant at `q.natDegree`. -/
theorem _root_.Polynomial.natDegree_gcd_eq_iff_psc (p q : K[X]) (j : ℕ) :
    (EuclideanDomain.gcd p q).natDegree = j ↔
      psc p q p.natDegree q.natDegree j ≠ 0 ∧
        ∀ i < j, psc p q p.natDegree q.natDegree i = 0 := by
  have hne : psc p q p.natDegree q.natDegree (EuclideanDomain.gcd p q).natDegree ≠ 0 := by
    rcases eq_or_ne p 0 with rfl | hp
    · rw [EuclideanDomain.gcd_zero_left, natDegree_zero, psc_right_bound, Nat.zero_sub, pow_zero]
      exact one_ne_zero
    · exact psc_natDegree_gcd_ne_zero hp rfl le_rfl
  constructor
  · rintro rfl
    exact ⟨hne, fun i hi => psc_eq_zero_of_lt_natDegree_gcd le_rfl le_rfl hi⟩
  · rintro ⟨hj, hlt⟩
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · exact hne (hlt _ h)
    · exact hj (psc_eq_zero_of_lt_natDegree_gcd le_rfl le_rfl h)

end Field

end TauCeti

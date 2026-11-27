/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.LinearCombination

/-!
# The twisted product of two polynomials

For polynomials `P Q : R[X]` and a unit `u : Rˣ`, the twisted product
`Polynomial.weightedProduct P Q u = P(u⁻¹ X) · Q(u X)` scales the two factors by opposite
powers of `u`. Comparing it with the plain product `P · Q` separates the two factors: this is
the character-twist computation by which a Levi factor of a determinant is separated from its
dual (Scholze, *On torsion in the cohomology of locally symmetric varieties*, Ann. of Math. 182
(2015), proof of Lemma 5.3.4).

The coefficient of `X ^ j` of the twisted product is `∑_{a + b = j} P_a Q_b u^(b - a)`
(`Polynomial.coeff_weightedProduct`). If the coefficients of two factorisations agree below
degree `j` and all four factors have constant term `1`, the coefficients of `X ^ j` of the
products and of the twisted products give `δP_j + δQ_j = 0` and `u^(-j) δP_j + u^j δQ_j = 0`
for the differences, hence `(1 - u^(2j)) δQ_j = 0`. When every `1 - u^(2j)` is a unit, an
induction on `j` shows that the factors agree.

No domain or characteristic hypothesis is needed: the separation hypothesis is invertibility of
each `1 - u^(2j)`, not `u^(2j) ≠ 1`. Over `ZMod 9` with `u = 2`, the pairs `(1 + 3X, 1)` and
`(1, 1 + 3X)` have the same product and the same twisted product, while `1 - u^2 = 6` is nonzero
but not a unit.

## Main definitions

* `Polynomial.weightedProduct P Q u`: the twisted product `P(u⁻¹ X) · Q(u X)`.

## Main results

* `Polynomial.weightedProduct_one`: at `u = 1` the twisted product is `P * Q`.
* `Polynomial.coeff_zero_weightedProduct`: the constant coefficient is `P(0) · Q(0)`.
* `Polynomial.map_weightedProduct`: compatibility with coefficient change along a ring map.
* `Polynomial.weightedProduct_inv`: exchanging the factors inverts the unit.
* `Polynomial.eq_and_eq_of_mul_eq_of_weightedProduct_eq`: twisted-product separation.
-/

public section

namespace Polynomial

section CommSemiring

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The twisted product `P(u⁻¹ X) · Q(u X)` of two polynomials, scaling the variable of the two
factors by opposite powers of the unit `u`. -/
noncomputable def weightedProduct (P Q : R[X]) (u : Rˣ) : R[X] :=
  P.comp (C (↑u⁻¹ : R) * X) * Q.comp (C (u : R) * X)

theorem weightedProduct_def (P Q : R[X]) (u : Rˣ) :
    P.weightedProduct Q u = P.comp (C (↑u⁻¹ : R) * X) * Q.comp (C (u : R) * X) :=
  (rfl)

/-- At `u = 1` the twisted product is the ordinary product. -/
@[simp]
theorem weightedProduct_one (P Q : R[X]) : P.weightedProduct Q 1 = P * Q := by
  simp [weightedProduct_def]

/-- The coefficient of `X ^ n` of the twisted product is `∑_{a + b = n} P_a Q_b u^(-a) u^b`. -/
theorem coeff_weightedProduct (P Q : R[X]) (u : Rˣ) (n : ℕ) :
    (P.weightedProduct Q u).coeff n =
      ∑ x ∈ Finset.antidiagonal n,
        P.coeff x.1 * Q.coeff x.2 * ((↑u⁻¹ : R) ^ x.1 * (u : R) ^ x.2) := by
  simp only [weightedProduct_def, coeff_mul, comp_C_mul_X_coeff]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The constant coefficient of the twisted product is `P(0) · Q(0)`. -/
@[simp]
theorem coeff_zero_weightedProduct (P Q : R[X]) (u : Rˣ) :
    (P.weightedProduct Q u).coeff 0 = P.coeff 0 * Q.coeff 0 := by
  simp [coeff_weightedProduct]

/-- The twisted product commutes with coefficient change along a ring map. -/
@[simp]
theorem map_weightedProduct (f : R →+* S) (P Q : R[X]) (u : Rˣ) :
    (P.weightedProduct Q u).map f =
      (P.map f).weightedProduct (Q.map f) (Units.map (f : R →* S) u) := by
  simp [weightedProduct_def, Polynomial.map_mul, map_comp]

/-- Exchanging the two factors of a twisted product inverts the unit. -/
theorem weightedProduct_inv (P Q : R[X]) (u : Rˣ) :
    P.weightedProduct Q u⁻¹ = Q.weightedProduct P u := by
  rw [weightedProduct_def, weightedProduct_def, inv_inv, mul_comm]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- If two pairs of polynomials with constant term `1` have the same coefficients below degree
`j ≠ 0`, the weighted sum over `a + b = j` of the differences `P_a Q_b - P'_a Q'_b` only sees
the two extreme terms `(j, 0)` and `(0, j)`. -/
private theorem sum_antidiagonal_coeff_sub_mul {P Q P' Q' : R[X]} {j : ℕ} (hj : j ≠ 0)
    (hcP : P.coeff 0 = 1) (hcQ : Q.coeff 0 = 1) (hcP' : P'.coeff 0 = 1) (hcQ' : Q'.coeff 0 = 1)
    (hlt : ∀ i < j, P.coeff i = P'.coeff i ∧ Q.coeff i = Q'.coeff i) (w : ℕ × ℕ → R) :
    ∑ x ∈ Finset.antidiagonal j, (P.coeff x.1 * Q.coeff x.2 - P'.coeff x.1 * Q'.coeff x.2) * w x =
      (P.coeff j - P'.coeff j) * w (j, 0) + (Q.coeff j - Q'.coeff j) * w (0, j) := by
  rw [Finset.sum_eq_add_of_mem (j, 0) (0, j) (by simp) (by simp) (by simp [hj])]
  · simp [hcP, hcQ, hcP', hcQ']
  · rintro ⟨a, b⟩ hab ⟨ha, hb⟩
    rw [Finset.mem_antidiagonal] at hab
    simp only [ne_eq, Prod.mk.injEq] at ha hb
    rw [(hlt a (by omega)).1, (hlt b (by omega)).2, sub_self, zero_mul]

/-- **Twisted-product separation.** Let `P, Q, P', Q'` be polynomials of degree at most `n` with
constant term `1` over any commutative ring. If `P * Q = P' * Q'`, the twisted products by a unit
`u` agree, and `1 - u ^ (2 * j)` is a unit for every `1 ≤ j ≤ n`, then `P = P'` and `Q = Q'`
(Scholze, proof of Lemma 5.3.4). -/
theorem eq_and_eq_of_mul_eq_of_weightedProduct_eq {n : ℕ} {u : Rˣ} {P Q P' Q' : R[X]}
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n) (hP' : P'.natDegree ≤ n)
    (hQ' : Q'.natDegree ≤ n) (hcP : P.coeff 0 = 1) (hcQ : Q.coeff 0 = 1)
    (hcP' : P'.coeff 0 = 1) (hcQ' : Q'.coeff 0 = 1) (hprod : P * Q = P' * Q')
    (htwist : P.weightedProduct Q u = P'.weightedProduct Q' u)
    (hsep : ∀ j, 1 ≤ j → j ≤ n → IsUnit (1 - (u : R) ^ (2 * j))) :
    P = P' ∧ Q = Q' := by
  suffices key : ∀ j, P.coeff j = P'.coeff j ∧ Q.coeff j = Q'.coeff j by
    constructor <;> ext j
    exacts [(key j).1, (key j).2]
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact ⟨hcP.trans hcP'.symm, hcQ.trans hcQ'.symm⟩
  rcases lt_or_ge n j with hjn | hjn
  · simp [coeff_eq_zero_of_natDegree_lt, hP.trans_lt hjn, hQ.trans_lt hjn, hP'.trans_lt hjn,
      hQ'.trans_lt hjn]
  -- The coefficients of `X ^ j` of the products and of the twisted products give two linear
  -- equations for the differences `δP_j` and `δQ_j`.
  have hsum := sum_antidiagonal_coeff_sub_mul hj0.ne' hcP hcQ hcP' hcQ' ih
  have e1 : (P.coeff j - P'.coeff j) + (Q.coeff j - Q'.coeff j) = 0 := by
    have h := congrArg (fun p => p.coeff j) hprod
    simp only [coeff_mul] at h
    simpa [Finset.sum_sub_distrib, h] using (hsum fun _ => 1).symm
  have e2 : (P.coeff j - P'.coeff j) * (↑u⁻¹ : R) ^ j + (Q.coeff j - Q'.coeff j) * (u : R) ^ j =
      0 := by
    have h := congrArg (fun p => p.coeff j) htwist
    simp only [coeff_weightedProduct] at h
    simpa [Finset.sum_sub_distrib, sub_mul, h] using
      (hsum fun x => (↑u⁻¹ : R) ^ x.1 * (u : R) ^ x.2).symm
  have hu : (↑u⁻¹ : R) ^ j * (u : R) ^ j = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  -- Eliminating `δP_j` gives `δQ_j * (1 - u ^ (2 * j)) = 0`.
  have hQj : Q.coeff j - Q'.coeff j = 0 := by
    refine (hsep j hj0 hjn).mul_left_eq_zero.mp ?_
    linear_combination ((u : R) ^ j * (↑u⁻¹ : R) ^ j) * e1 - (u : R) ^ j * e2 -
      (Q.coeff j - Q'.coeff j) * hu
  rw [hQj, add_zero] at e1
  exact ⟨sub_eq_zero.mp e1, sub_eq_zero.mp hQj⟩

end CommRing

end Polynomial

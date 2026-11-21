/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Coefficient maps, variable swaps, and evaluation of bivariate polynomials

Evaluating a bivariate polynomial at a point `(x, y)` is `eval₂` of the evaluation at `x`
of its coefficients, read at `y`. The bivariate-to-multivariate equivalence also commutes
with coefficient maps and evaluation. The coefficients of `f(X + Y)` are binomial multiples of
those of `f`.

This file also provides coefficient and degree formulas for `Bivariate.swap`, nonzero
specialization of irreducible bivariate polynomials of positive degree, and factorization
of bivariate polynomials over a UFD into `Y`-content and positive-degree irreducibles.

## Main results

* `Polynomial.aevalAeval_eq_eval₂`: `φ(x, y) = eval₂ (aeval x) y φ`.
* `Polynomial.coeff_coeff_aeval_C_X_add_Y`: the coefficient of `X ^ a * Y ^ b` in `f(X + Y)` is
  `(a + b).choose b * f_{a+b}`.
* `Polynomial.coeff_coeff_swap`: coefficients of `Bivariate.swap P` swap indices.
* `Polynomial.natDegree_swap_le_iff`: degree of `Bivariate.swap P` bounds the coefficient degrees.
* `Polynomial.natDegree_swap_C`, `Polynomial.natDegree_swap_mul`: swap degrees of constants and
  products.
* `Polynomial.map_evalRingHom_ne_zero_of_irreducible`: specializations of positive-degree
  irreducible bivariate polynomials are nonzero.
* `Polynomial.exists_C_mul_list_prod_irreducible`: factorization into `Y`-content and
  positive-degree irreducible factors over a unique factorization domain.
-/

public section

open scoped Polynomial.Bivariate

namespace Polynomial

/-- Evaluating a bivariate polynomial at `(x, y)` evaluates its coefficients at `x` and the
resulting polynomial at `y`. -/
theorem aevalAeval_eq_eval₂ {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (x y : A) (p : R[X][Y]) : aevalAeval x y p = eval₂ (aeval x).toRingHom y p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, eval₂_add]
  | monomial n a => simp [← C_mul_X_pow_eq_monomial]

/-- The bivariate-to-multivariate equivalence commutes with coefficient maps. -/
@[simp]
theorem Bivariate.equivMvPolynomial_symm_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (φ : MvPolynomial (Fin 2) R) :
    (Bivariate.equivMvPolynomial S).symm (φ.map f) =
      ((Bivariate.equivMvPolynomial R).symm φ).map (mapRingHom f) := by
  induction φ using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => fin_cases i <;> simp [hp]

/-- Evaluation is unchanged by converting a two-variable polynomial to bivariate form. -/
@[simp]
theorem Bivariate.aevalAeval_comp_equivMvPolynomial_symm {R A : Type*}
    [CommSemiring R] [CommSemiring A] [Algebra R A] (x y : A) :
    (aevalAeval x y).comp
        ((Bivariate.equivMvPolynomial R).symm : MvPolynomial (Fin 2) R →ₐ[R] R[X][Y]) =
      MvPolynomial.aeval ![x, y] :=
  MvPolynomial.algHom_ext fun i ↦ by fin_cases i <;> simp

/-- The coefficient of `X ^ a * Y ^ b` in `f(X + Y)` is `(a + b).choose b * f_{a+b}`. -/
@[simp]
theorem coeff_coeff_aeval_C_X_add_Y {R : Type*} [CommSemiring R] (f : R[X]) (a b : ℕ) :
    ((aeval (C X + Y : R[X][Y]) f).coeff b).coeff a =
      ((a + b).choose b : R) * f.coeff (a + b) := by
  -- `f(X + Y)` is the Taylor expansion of `f(Y)` at `X`, whose coefficients are the Hasse
  -- derivatives of `f`.
  have h : aeval (C X + Y : R[X][Y]) f = taylor X (f.map C) := by
    rw [taylor_apply, comp, eval₂_map, aeval_def, add_comm,
      IsScalarTower.algebraMap_eq R R[X] R[X][X], algebraMap_eq, algebraMap_eq]
  rw [h, taylor_coeff, hasseDeriv_map, eval_map, eval₂_C_X, hasseDeriv_coeff]

/-- Swapping the two variables of a bivariate polynomial transposes its coefficient indices. -/
@[simp]
theorem coeff_coeff_swap {R : Type*} [CommSemiring R] (P : R[X][Y]) (r s : ℕ) :
    ((Bivariate.swap P).coeff s).coeff r = (P.coeff r).coeff s := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | monomial k p =>
    rw [Bivariate.swap_monomial, mul_comm, coeff_C_mul, coeff_map, mul_comm, coeff_C_mul,
      coeff_X_pow]
    by_cases hkr : r = k
    · subst hkr
      simp
    · simp [hkr]

/-- The degree of `Bivariate.swap P` is at most `d` if and only if every coefficient of `P` has
degree at most `d`. -/
theorem natDegree_swap_le_iff {R : Type*} [CommSemiring R] (P : R[X][Y]) (d : ℕ) :
    (Bivariate.swap P).natDegree ≤ d ↔ ∀ i, (P.coeff i).natDegree ≤ d := by
  constructor
  · intro h i
    refine natDegree_le_iff_coeff_eq_zero.mpr fun s hs ↦ ?_
    rw [← coeff_coeff_swap, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h hs), coeff_zero]
  · intro h
    refine natDegree_le_iff_coeff_eq_zero.mpr fun s hs ↦ ?_
    ext r
    rw [coeff_coeff_swap, coeff_zero]
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (h r) hs)

/-- The degree of `Bivariate.swap (C p)` equals `p.natDegree`. -/
@[simp]
theorem natDegree_swap_C {R : Type*} [CommSemiring R] (p : R[X]) :
    (Bivariate.swap (C p)).natDegree = p.natDegree := by
  rw [Bivariate.swap_C, natDegree_map_eq_of_injective C_injective]

/-- Over a ring without zero divisors, the degree of `Bivariate.swap` is additive on products of
nonzero bivariate polynomials. -/
theorem natDegree_swap_mul {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    {A B : R[X][Y]} (hA : A ≠ 0) (hB : B ≠ 0) :
    (Bivariate.swap (A * B)).natDegree =
      (Bivariate.swap A).natDegree + (Bivariate.swap B).natDegree := by
  rw [map_mul, natDegree_mul (by simpa using hA) (by simpa using hB)]

/-- Over an integral domain, specializing an irreducible bivariate polynomial of positive outer
degree at any scalar yields a nonzero univariate polynomial. -/
theorem map_evalRingHom_ne_zero_of_irreducible {R : Type*} [CommRing R] [IsDomain R]
    {F : R[X][Y]} (hF : Irreducible F) (hdeg : 0 < F.natDegree) (b : R) :
    F.map (evalRingHom b) ≠ 0 := by
  intro h0
  have hdvd : C (X - C b) ∣ F := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [dvd_iff_isRoot, IsRoot]
    have hi : (F.map (evalRingHom b)).coeff i = 0 := by rw [h0, coeff_zero]
    simpa [coeff_map] using hi
  obtain ⟨Q, hQ⟩ := hdvd
  rcases hF.isUnit_or_isUnit hQ with hU | hU
  · have hU' : IsUnit (X - C b) := isUnit_C.mp hU
    have hdeg0 : (X - C b).natDegree = 0 := natDegree_eq_zero_of_isUnit hU'
    simp at hdeg0
  · have hQ0 : Q.natDegree = 0 := natDegree_eq_zero_of_isUnit hU
    have hF0 : F.natDegree = 0 := by
      rw [hQ]
      exact Nat.eq_zero_of_le_zero ((natDegree_C_mul_le _ _).trans (by omega))
    omega

/-- Every nonzero bivariate polynomial over a unique factorization domain factors as `C c * l.prod`,
where `c : R[X]` is nonzero and every factor in `l` is irreducible of positive degree in the
outer variable. -/
theorem exists_C_mul_list_prod_irreducible {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (P : R[X][Y]) (hP : P ≠ 0) :
    ∃ (c : R[X]) (l : List R[X][Y]), c ≠ 0 ∧
      (∀ F ∈ l, Irreducible F ∧ 0 < F.natDegree) ∧ P = C c * l.prod := by
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => exact absurd rfl hP
  | unit u hu =>
    refine ⟨u.coeff 0, [], ?_, by simp, ?_⟩
    · intro h0
      exact hu.ne_zero (by rw [eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hu), h0,
        map_zero])
    · rw [List.prod_nil, mul_one]
      exact eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hu)
  | mul a b ha hb ih =>
    obtain ⟨c, l, hc0, hl, haeq⟩ := ih ha
    by_cases hbdeg : b.natDegree = 0
    · have hb0 : b.coeff 0 ≠ 0 := fun h0 ↦
        hb.ne_zero (by rw [eq_C_of_natDegree_eq_zero hbdeg, h0, map_zero])
      refine ⟨b.coeff 0 * c, l, mul_ne_zero hb0 hc0, hl, ?_⟩
      rw [haeq, map_mul, mul_assoc]
      congr 1
      exact eq_C_of_natDegree_eq_zero hbdeg
    · refine ⟨c, b :: l, hc0, ?_, ?_⟩
      · simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨⟨hb, Nat.pos_of_ne_zero hbdeg⟩, hl⟩
      · rw [haeq, List.prod_cons]
        ring

end Polynomial

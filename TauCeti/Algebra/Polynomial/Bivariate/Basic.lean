/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Coefficient maps, variable swaps, and evaluation of bivariate polynomials

Evaluating a bivariate polynomial at a point `(x, y)` is `eval₂` of the evaluation at `x`
of its coefficients, read at `y`. The bivariate-to-multivariate equivalence also commutes
with coefficient maps, evaluation, and total-degree bounds. The coefficients of `f(X + Y)` are
binomial multiples of those of `f`.

This file also provides coefficient and natural-degree formulas for `Bivariate.swap`.

## Main results

* `Polynomial.aevalAeval_eq_eval₂`: `φ(x, y) = eval₂ (aeval x) y φ`.
* `Polynomial.Bivariate.eval_equivMvPolynomial`: evaluating `equivMvPolynomial R F` at `v`
  evaluates `F` at `(v 0, v 1)` via `Polynomial.evalEval`.
* `Polynomial.Bivariate.totalDegree_equivMvPolynomial_le`: total-degree bound for
  `equivMvPolynomial R F` from outer and coefficient natural-degree bounds.
* `Polynomial.coeff_coeff_aeval_C_X_add_Y`: the coefficient of `X ^ a * Y ^ b` in `f(X + Y)` is
  `(a + b).choose b * f_{a+b}`.
* `Polynomial.coeff_coeff_swap`: coefficients of `Bivariate.swap P` swap indices.
* `Polynomial.natDegree_swap_le_iff`: natural degree of `Bivariate.swap P` bounds the coefficient
  natural degrees.
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

/-- Evaluating `Bivariate.equivMvPolynomial R F` at `v : Fin 2 → R` equals `F.evalEval (v 0) (v 1)`
(evaluating the inner variable at `v 0` and the outer variable at `v 1`). -/
@[simp]
theorem Bivariate.eval_equivMvPolynomial {R : Type*} [CommSemiring R] (F : R[X][Y])
    (v : Fin 2 → R) :
    MvPolynomial.eval v (Bivariate.equivMvPolynomial R F) = F.evalEval (v 0) (v 1) := by
  have h := AlgHom.congr_fun (Bivariate.aevalAeval_comp_equivMvPolynomial_symm (R := R) (v 0) (v 1))
    (Bivariate.equivMvPolynomial R F)
  have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> simp
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
    aevalAeval_eq_eval₂, eval₂_eq_eval_map, hv] at h
  simpa [coe_evalRingHom, map_evalRingHom_eval] using h.symm

/-- If `F : R[X][Y]` has outer natural degree at most `a` and every coefficient `F.coeff i` has
natural degree at most `b`, then `Bivariate.equivMvPolynomial R F` has total degree at most
`a + b`. -/
theorem Bivariate.totalDegree_equivMvPolynomial_le {R : Type*} [CommSemiring R] (F : R[X][Y])
    {a b : ℕ} (ha : F.natDegree ≤ a) (hb : ∀ i, (F.coeff i).natDegree ≤ b) :
    (Bivariate.equivMvPolynomial R F).totalDegree ≤ a + b := by
  rcases subsingleton_or_nontrivial R with _ | _
  · rw [Subsingleton.elim (Bivariate.equivMvPolynomial R F) 0, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  rw [F.as_sum_support_C_mul_X_pow, map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun r hr ↦ ?_)
  have hr_le : r ≤ a := (le_natDegree_of_mem_supp r hr).trans ha
  rw [map_mul, map_pow, Bivariate.equivMvPolynomial_X]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hC : (Bivariate.equivMvPolynomial R (C (F.coeff r))).totalDegree ≤ b := by
    rw [(F.coeff r).as_sum_support_C_mul_X_pow, map_sum, map_sum]
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs ↦ ?_)
    have hs_le : s ≤ b := (le_natDegree_of_mem_supp s hs).trans (hb r)
    rw [map_mul, map_mul, map_pow, map_pow, Bivariate.equivMvPolynomial_C_X]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have hcoeff :
        (Bivariate.equivMvPolynomial R (C (C ((F.coeff r).coeff s)))).totalDegree = 0 := by
      rw [Bivariate.equivMvPolynomial_C_C, MvPolynomial.totalDegree_C]
    rw [hcoeff, zero_add]
    exact (MvPolynomial.totalDegree_pow _ s).trans (by
      simpa [MvPolynomial.totalDegree_X] using hs_le)
  have hX : ((MvPolynomial.X 1 : MvPolynomial (Fin 2) R) ^ r).totalDegree ≤ r :=
    (MvPolynomial.totalDegree_pow _ r).trans (by simp [MvPolynomial.totalDegree_X])
  exact (Nat.add_le_add hC hX).trans (by omega)

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

/-- The natural degree of `Bivariate.swap P` is at most `d` if and only if every coefficient of
`P` has natural degree at most `d`. -/
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

end Polynomial

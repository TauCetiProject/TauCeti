/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Coefficient maps and evaluation of bivariate polynomials

Evaluating a bivariate polynomial at a point `(x, y)` is `eval₂` of the evaluation at `x`
of its coefficients, read at `y`. The bivariate-to-multivariate equivalence also commutes
with coefficient maps and evaluation. The coefficients of `f(X + Y)` are binomial multiples of
those of `f`.

## Main results

* `Polynomial.aevalAeval_eq_eval₂`: `φ(x, y) = eval₂ (aeval x) y φ`.
* `Polynomial.coeff_coeff_aeval_C_X_add_Y`: the coefficient of `X ^ a * Y ^ b` in `f(X + Y)` is
  `(a + b).choose b * f_{a+b}`.
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

end Polynomial

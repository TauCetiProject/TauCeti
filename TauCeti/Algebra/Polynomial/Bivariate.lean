/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Polynomial.Bivariate
public import TauCeti.Algebra.Polynomial.Units

/-!
# Coefficient maps and evaluation of bivariate polynomials

A plane curve over a field `K` is given by a polynomial `φ ∈ K[X][Y]`, and it is *absolutely
irreducible* when `φ` stays irreducible over an algebraic closure of `K`. This file records two
facts about such polynomials that do not depend on the curve.

* Mapping coefficients along an injective local homomorphism into a semiring without zero
  divisors reflects units of the polynomial ring. Applied twice, an embedding of fields `K → L`
  reflects units of `K[X][Y]`, so a bivariate polynomial whose image over `L` is irreducible is
  already irreducible over `K`.
* Evaluating `φ` at a point `(x, y)` of an algebra is `eval₂` of the evaluation at `x` of its
  coefficients, read at `y`.

## Main results

* `Polynomial.irreducible_of_irreducible_map_mapRingHom`: irreducibility of a bivariate polynomial
  descends along an injective local homomorphism, such as a homomorphism of fields.
* `Polynomial.aevalAeval_eq_eval₂`: `φ(x, y) = eval₂ (aeval x) y φ`.
-/

public section

open scoped Polynomial.Bivariate

namespace Polynomial

/-- **Irreducibility of a bivariate polynomial descends along an injective local homomorphism**
into a semiring without zero divisors, for instance along any homomorphism of fields: if the image
of `p ∈ R[X][Y]` in `S[X][Y]` is irreducible, then so is `p`. In particular an absolutely
irreducible polynomial over a field is irreducible over every field between it and an algebraic
closure. -/
theorem irreducible_of_irreducible_map_mapRingHom {R S : Type*} [Semiring R] [Semiring S]
    [NoZeroDivisors S] {f : R →+* S} [IsLocalHom f] (hf : Function.Injective f) {p : R[X][Y]}
    (h : Irreducible (p.map (mapRingHom f))) : Irreducible p :=
  have := isLocalHom_mapRingHom hf
  have := isLocalHom_mapRingHom (f := mapRingHom f) (map_injective f hf)
  h.of_map (f := mapRingHom (mapRingHom f))

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

end Polynomial

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.HeckePolynomial.Basic
public import TauCeti.RingTheory.PolynomialLaw.Determinant

import Mathlib.Tactic.LinearCombination

/-!
# The determinant coefficient of a `GL n` parameter

Let `D` be an `n`-dimensional determinant (in the sense of Chenevier) on an `A`-algebra `R`, and
let `r ∈ R` be an element, typically a Frobenius element, whose characteristic polynomial is the
integral Hecke polynomial `P(X) = ∑ (-1)^i q^{i(i-1)/2} Tᵢ X^{n-i}`. Comparing constant terms
shows that the value of the determinant at `r` is `q^{n(n-1)/2} Tₙ`. With normalized Satake
parameters, `q = s²` and `Tᵢ = s^{i(n-i)} eᵢ(z)`, this value is `s^{n(n-1)} ∏ zⱼ`.

These are equalities at the given element `r`; identifying the determinant character globally is
not addressed here.

If `r` is a unit, read as an arithmetic Frobenius element, its inverse is the geometric Frobenius
element, and the characteristic polynomial at `r⁻¹` is the normalized reciprocal of `P`. In ranks
one and two this is explicit: `X - T₁` becomes `X - T₁⁻¹`, and `X² - T₁ X + q T₂` becomes
`X² - T₁ (q T₂)⁻¹ X + (q T₂)⁻¹`. A source that specifies the Hecke polynomial at geometric
Frobenius, as ACC23 does, is converted to the arithmetic convention in the same way.

## Main results

* `TauCeti.Determinant.apply_eq_of_charpoly_eq_glnHeckePolynomial`: `D r = q^{n(n-1)/2} Tₙ`.
* `TauCeti.Determinant.apply_eq_of_charpoly_eq_glnHeckePolynomial_satake`: with normalized
  Satake parameters, `D r = s^{n(n-1)} ∏ zⱼ`.
* `TauCeti.Determinant.leading_eq_one_of_charpoly_eq_glnHeckePolynomial`: then `T₀ = 1`.
* `TauCeti.Determinant.charpoly_inv_eq_of_charpoly_eq_glnHeckePolynomial_one` and
  `TauCeti.Determinant.charpoly_inv_eq_of_charpoly_eq_glnHeckePolynomial_two`: the
  characteristic polynomial at the inverse Frobenius element in ranks one and two.

## References

* P. Allen, F. Calegari, A. Caraiani, T. Gee, D. Helm, B. Le Hung, J. Newton, P. Scholze,
  R. Taylor and J. Thorne, *Potential automorphy over CM fields*, Ann. of Math. 197 (2023),
  §2.2.5, equation (2.2.6), and §2.2.20.
-/

public section

open Polynomial

namespace TauCeti

namespace Determinant

variable {A : Type*} [CommRing A] {R : Type*} [Semiring R] [Algebra A R] {n : ℕ}

/-- **Determinant coefficient of a `GL n` parameter.** If the characteristic polynomial of an
`n`-dimensional determinant `D` at `r` is the integral Hecke polynomial with parameters `q` and
`T₀, …, Tₙ`, then `D r = q^{n(n-1)/2} Tₙ`. -/
theorem apply_eq_of_charpoly_eq_glnHeckePolynomial (D : Determinant A R n) {r : R} {q : A}
    {T : Fin (n + 1) → A} (h : D.charpoly r = glnHeckePolynomial n q T) :
    D r = q ^ n.choose 2 * T (Fin.last n) := by
  refine (isUnit_neg_one.pow n).mul_left_cancel ?_
  rw [← eval_zero_charpoly, h, ← coeff_zero_eq_eval_zero, coeff_zero_glnHeckePolynomial,
    mul_assoc]

/-- **Determinant coefficient with normalized Satake parameters.** For `q = s²` and
`Tᵢ = s^{i(n-i)} eᵢ(z₁, …, zₙ)`, a determinant whose characteristic polynomial at `r` is the
Hecke polynomial takes the value `s^{n(n-1)} ∏ⱼ zⱼ` at `r`. -/
theorem apply_eq_of_charpoly_eq_glnHeckePolynomial_satake (D : Determinant A R n) {r : R} (s : A)
    (z : Fin n → A)
    (h : D.charpoly r = glnHeckePolynomial n (s ^ 2)
      (fun i => s ^ ((i : ℕ) * (n - i)) * (Finset.univ.val.map z).esymm i)) :
    D r = s ^ (n * (n - 1)) * ∏ j, z j := by
  rw [glnHeckePolynomial_pow_mul_esymm] at h
  rw [D.apply_eq_prod_of_charpoly_eq_prod h, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm (n - 1)]

/-- A characteristic polynomial is monic, so if it is the Hecke polynomial then `T₀ = 1`. -/
theorem leading_eq_one_of_charpoly_eq_glnHeckePolynomial (D : Determinant A R n) {r : R} {q : A}
    {T : Fin (n + 1) → A} (h : D.charpoly r = glnHeckePolynomial n q T) : T 0 = 1 := by
  rw [← coeff_glnHeckePolynomial_self q T, ← h, coeff_charpoly_dim]

/-- **Rank-one Frobenius conversion.** If a one-dimensional determinant has the Hecke polynomial
`X - T₁` as characteristic polynomial at a unit `u`, and `t` is the inverse of `T₁`, then its
characteristic polynomial at `u⁻¹` is `X - t`. -/
theorem charpoly_inv_eq_of_charpoly_eq_glnHeckePolynomial_one (D : Determinant A R 1) {u : Rˣ}
    {q t : A} {T : Fin 2 → A} (h : D.charpoly u = glnHeckePolynomial 1 q T)
    (ht : T 1 * t = 1) : D.charpoly ↑u⁻¹ = X - C t := by
  have hT := D.leading_eq_one_of_charpoly_eq_glnHeckePolynomial h
  have hu : D u = T 1 := by
    simpa using D.apply_eq_of_charpoly_eq_glnHeckePolynomial h
  have hinv : D ↑u⁻¹ = t := by
    simpa only [Units.coe_map_inv, coe_toMonoidHom] using
      (Units.map D.toMonoidHom u).inv_eq_of_mul_eq_one_right
        (by rwa [Units.coe_map, coe_toMonoidHom, hu])
  have hC : C t * C (T 1) = 1 := by rw [← C_mul, mul_comm, ht, C_1]
  rw [charpoly_inv, h, hinv, glnHeckePolynomial_one, hT, C_1, one_mul, reflect_sub,
    reflect_C, reflect_one_X]
  simp only [C_mul, C_neg, C_1, pow_one]
  linear_combination X * hC

/-- **Rank-two Frobenius conversion.** If a two-dimensional determinant has the Hecke polynomial
`X² - T₁ X + q T₂` as characteristic polynomial at a unit `u`, and `c` is the inverse of `q T₂`,
then its characteristic polynomial at `u⁻¹` is the normalized reciprocal `X² - T₁ c X + c`. -/
theorem charpoly_inv_eq_of_charpoly_eq_glnHeckePolynomial_two (D : Determinant A R 2) {u : Rˣ}
    {q c : A} {T : Fin 3 → A} (h : D.charpoly u = glnHeckePolynomial 2 q T)
    (hc : q * T 2 * c = 1) : D.charpoly ↑u⁻¹ = X ^ 2 - C (T 1 * c) * X + C c := by
  have hT := D.leading_eq_one_of_charpoly_eq_glnHeckePolynomial h
  have hu : D u = q * T 2 := by
    simpa using D.apply_eq_of_charpoly_eq_glnHeckePolynomial h
  have hinv : D ↑u⁻¹ = c := by
    simpa only [Units.coe_map_inv, coe_toMonoidHom] using
      (Units.map D.toMonoidHom u).inv_eq_of_mul_eq_one_right
        (by rwa [Units.coe_map, coe_toMonoidHom, hu])
  have hC : C c * (C q * C (T 2)) = 1 := by rw [← C_mul, ← C_mul, mul_comm, hc, C_1]
  rw [charpoly_inv, h, hinv, glnHeckePolynomial_two, hT, C_1, one_mul]
  have hX : reflect 2 (X : A[X]) = X := by simpa using reflect_monomial (R := A) 2 1
  simp only [even_two, Even.neg_pow, one_pow, one_mul, _root_.map_mul, reflect_add, reflect_sub,
    reflect_monomial, revAt_le le_rfl, tsub_self, pow_zero, reflect_C_mul, hX, reflect_C]
  linear_combination (X ^ 2 : A[X]) * hC

end Determinant

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.HeckePolynomial
public import TauCeti.RingTheory.PolynomialLaw.Determinant

/-!
# The determinant coefficient of a `GL n` parameter

Let `D` be an `n`-dimensional determinant (in the sense of Chenevier) on an `A`-algebra `R`, and
let `r ∈ R` be an element, typically a Frobenius element, whose characteristic polynomial is the
integral Hecke polynomial `P(X) = ∑ (-1)^i q^{i(i-1)/2} Tᵢ X^{n-i}`. Comparing constant terms
shows that the value of the determinant at `r` is `q^{n(n-1)/2} Tₙ`. With normalized Satake
parameters, `q = s²` and `Tᵢ = s^{i(n-i)} eᵢ(z)`, this value is `s^{n(n-1)} ∏ zⱼ`.

These are equalities at the given element `r`; identifying the determinant character globally is
not addressed here.

## Main results

* `TauCeti.Determinant.apply_eq_of_charpoly_eq_glnHeckePolynomial`: `D r = q^{n(n-1)/2} Tₙ`.
* `TauCeti.Determinant.apply_eq_prod_of_charpoly_eq_prod`: a determinant whose characteristic
  polynomial at `r` is `∏ⱼ (X - aⱼ)` takes the value `∏ⱼ aⱼ` at `r`.
* `TauCeti.Determinant.apply_eq_of_charpoly_eq_glnHeckePolynomial_satake`: with normalized
  Satake parameters, `D r = s^{n(n-1)} ∏ zⱼ`.

## References

* P. Allen, F. Calegari, A. Caraiani, T. Gee, D. Helm, B. Le Hung, J. Newton, P. Scholze,
  R. Taylor and J. Thorne, *Potential automorphy over CM fields*, Ann. of Math. 197 (2023),
  §2.2.5, equation (2.2.6).
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
  have h₀ := D.eval_zero_charpoly r
  rw [h, ← coeff_zero_eq_eval_zero, coeff_zero_glnHeckePolynomial, mul_assoc] at h₀
  have hsq : ((-1 : A) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  calc D r = (-1) ^ n * (-1) ^ n * D r := by rw [hsq, one_mul]
    _ = q ^ n.choose 2 * T (Fin.last n) := by rw [mul_assoc, ← h₀, ← mul_assoc, hsq, one_mul]

/-- A determinant whose characteristic polynomial at `r` is `∏ⱼ (X - aⱼ)` takes the value
`∏ⱼ aⱼ` at `r`. -/
theorem apply_eq_prod_of_charpoly_eq_prod (D : Determinant A R n) {r : R} {a : Fin n → A}
    (h : D.charpoly r = ∏ j, (X - C (a j))) : D r = ∏ j, a j := by
  have h₀ := D.eval_zero_charpoly r
  rw [h, eval_prod] at h₀
  simp only [eval_sub, eval_X, eval_C, zero_sub, Finset.prod_neg, Finset.card_univ,
    Fintype.card_fin] at h₀
  have hsq : ((-1 : A) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  calc D r = (-1) ^ n * (-1) ^ n * D r := by rw [hsq, one_mul]
    _ = ∏ j, a j := by rw [mul_assoc, ← h₀, ← mul_assoc, hsq, one_mul]

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

end Determinant

end TauCeti

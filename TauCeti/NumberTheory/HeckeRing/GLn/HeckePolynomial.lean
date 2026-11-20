/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import TauCeti.Data.Nat.Choose.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.LinearCombination

/-!
# The integral Hecke polynomial of `GL_n`

At an unramified place `v` of a number field, with residue cardinality `q`, the spherical Hecke
algebra of `GL_n` contains the double cosets `T_i = [K diag(ϖ, …, ϖ, 1, …, 1) K]`, with `ϖ`
repeated `i` times. The Frobenius polynomial attached to an unramified representation, or to a
Hecke eigensystem, is

`P(X) = ∑_{i=0}^n (-1)^i q^{i(i-1)/2} T_i X^{n-i}`.

This file defines this polynomial `TauCeti.glnHeckePolynomial n q T` as a formal expression in
arbitrary elements `q, T_0, …, T_n` of a commutative ring `A`. Nothing about double cosets is
used, so the coefficient ring may be a Hecke algebra itself, a field of eigenvalues, or any
quotient of either, including the zero ring. The polynomial needs no square root of `q`, which
is what makes it transportable along arbitrary coefficient maps (`map_glnHeckePolynomial`).

The exponent `i(i-1)/2` is written `i.choose 2`.

The **Satake factorization** explains the normalization: if `q = s²` and the `T_i` take the
Satake values `s^{i(n-i)} e_i(z_1, …, z_n)`, then `P(X) = ∏_j (X - s^{n-1} z_j)`. So the roots
of `P` are the Satake parameters in the arithmetic normalization `q^{(n-1)/2} z_j`. Two further
identities record how `P` changes under the operations on the Hecke side.

* Scaling `T_i` by `a^i`, the effect of a twist by a character taking the value `a` at `ϖ`,
  scales the roots of `P` by `a`: `P'(aX) = a^n P(X)`.
* The involution `T_i ↦ T_{n-i} / T_n` of the spherical Hecke algebra, induced by `g ↦ g⁻¹`
  and computing the Hecke eigenvalues of the contragredient, replaces `P` by `q^{n(n-1)}` times
  its normalized reciprocal at `q^{1-n} X`. Its roots are `q^{n-1} / β` for the roots `β` of
  `P`. The statement here clears the constant coefficient of `P`, so it needs no unit
  hypotheses.

## Main definitions

* `TauCeti.glnHeckePolynomial n q T`: the integral Hecke polynomial
  `∑_{i=0}^n (-1)^i q^{i(i-1)/2} T_i X^{n-i}`.

## Main results

* `TauCeti.coeff_glnHeckePolynomial_sub`: the coefficient of `X^{n-i}` is
  `(-1)^i q^{i(i-1)/2} T_i`; in particular the constant coefficient is
  `(-1)^n q^{n(n-1)/2} T_n` (`TauCeti.coeff_zero_glnHeckePolynomial`).
* `TauCeti.monic_glnHeckePolynomial`: `P` is monic when `T_0 = 1`, and
  `TauCeti.natDegree_glnHeckePolynomial` gives its degree `n` when `T_0 ≠ 0`.
* `TauCeti.map_glnHeckePolynomial`: compatibility with every ring homomorphism.
* `TauCeti.glnHeckePolynomial_eq_prod_X_sub_C`: the Satake factorization.
* `TauCeti.glnHeckePolynomial_pow_mul_comp_C_mul_X`: the twist identity.
* `TauCeti.coeff_glnHeckePolynomial_sub_mul_coeff_zero` and
  `TauCeti.C_coeff_zero_mul_glnHeckePolynomial_comp_C_mul_X`: the inversion identity,
  coefficientwise and as an identity of polynomials.

## References

* P. B. Allen, F. Calegari, E. Caraiani, T. Gee, D. Helm, B. V. Le Hung, J. Newton, P. Scholze,
  R. Taylor and J. A. Thorne, *Potential automorphy over CM fields*, Ann. of Math. 197 (2023),
  §2.2.5, equation (2.2.6), and §2.2.20.
-/

public section

noncomputable section

open Polynomial

namespace TauCeti

variable {A B : Type*} [CommRing A] [CommRing B] {n : ℕ}

/-- The **integral Hecke polynomial of `GL_n`**,
`P(X) = ∑_{i=0}^n (-1)^i q^{i(i-1)/2} T_i X^{n-i}`, for elements `q, T_0, …, T_n` of a
commutative ring. When `T_i` are the eigenvalues of the spherical double cosets at a place of
residue cardinality `q`, this is the polynomial against which the characteristic polynomial of
Frobenius at that place is compared, for a Galois representation attached to the eigensystem. -/
def glnHeckePolynomial (n : ℕ) (q : A) (T : Fin (n + 1) → A) : A[X] :=
  ∑ i : Fin (n + 1), C ((-1) ^ (i : ℕ) * q ^ (i : ℕ).choose 2 * T i) * X ^ (n - i)

/-- The defining sum of the Hecke polynomial. -/
theorem glnHeckePolynomial_def (n : ℕ) (q : A) (T : Fin (n + 1) → A) :
    glnHeckePolynomial n q T =
      ∑ i : Fin (n + 1), C ((-1) ^ (i : ℕ) * q ^ (i : ℕ).choose 2 * T i) * X ^ (n - i) :=
  (rfl)

variable (q : A) (T : Fin (n + 1) → A)

/-- The coefficient of `X^{n-i}` in the Hecke polynomial is `(-1)^i q^{i(i-1)/2} T_i`. -/
@[simp]
theorem coeff_glnHeckePolynomial_sub (i : Fin (n + 1)) :
    (glnHeckePolynomial n q T).coeff (n - i) = (-1) ^ (i : ℕ) * q ^ (i : ℕ).choose 2 * T i := by
  rw [glnHeckePolynomial, finsetSum_coeff, Finset.sum_eq_single i]
  · simp only [coeff_C_mul_X_pow, ↓reduceIte]
  · intro j _ hji
    have := j.is_le
    have := i.is_le
    rw [coeff_C_mul_X_pow, ite_eq_right_iff]
    exact fun h => absurd (Fin.ext (by omega)) hji
  · simp

/-- The Hecke polynomial has no coefficients beyond degree `n`. -/
theorem coeff_glnHeckePolynomial_of_lt {k : ℕ} (hk : n < k) :
    (glnHeckePolynomial n q T).coeff k = 0 := by
  rw [glnHeckePolynomial, finsetSum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [coeff_C_mul_X_pow, ite_eq_right_iff]
  omega

/-- The coefficient of `X^n` is `T_0`. -/
@[simp]
theorem coeff_glnHeckePolynomial_self : (glnHeckePolynomial n q T).coeff n = T 0 := by
  simpa using coeff_glnHeckePolynomial_sub q T 0

/-- The **determinant coefficient**: the constant coefficient of the Hecke polynomial is
`(-1)^n q^{n(n-1)/2} T_n`. -/
@[simp]
theorem coeff_zero_glnHeckePolynomial :
    (glnHeckePolynomial n q T).coeff 0 = (-1) ^ n * q ^ n.choose 2 * T (Fin.last n) := by
  simpa using coeff_glnHeckePolynomial_sub q T (Fin.last n)

/-- The Hecke polynomial has degree at most `n`. -/
theorem natDegree_glnHeckePolynomial_le : (glnHeckePolynomial n q T).natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hk =>
    coeff_glnHeckePolynomial_of_lt q T hk

/-- The Hecke polynomial has degree `n` as soon as `T_0 ≠ 0`. -/
theorem natDegree_glnHeckePolynomial (h : T 0 ≠ 0) : (glnHeckePolynomial n q T).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_glnHeckePolynomial_le q T)
    (by rwa [coeff_glnHeckePolynomial_self])

/-- The Hecke polynomial is monic when `T_0 = 1`, over every commutative ring, including the
zero ring. -/
theorem monic_glnHeckePolynomial (h : T 0 = 1) : (glnHeckePolynomial n q T).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one n (natDegree_glnHeckePolynomial_le q T)
    (by rw [coeff_glnHeckePolynomial_self, h])

/-- The Hecke polynomial is compatible with every ring homomorphism of coefficients. -/
@[simp]
theorem map_glnHeckePolynomial (f : A →+* B) :
    (glnHeckePolynomial n q T).map f = glnHeckePolynomial n (f q) (fun i => f (T i)) := by
  simp [glnHeckePolynomial, Polynomial.map_sum]

/-- In rank zero the Hecke polynomial is the constant `T_0`. -/
theorem glnHeckePolynomial_zero (T : Fin 1 → A) : glnHeckePolynomial 0 q T = C (T 0) := by
  simp [glnHeckePolynomial]

/-- In rank one the Hecke polynomial is `T_0 X - T_1`: no power of `q` appears. -/
theorem glnHeckePolynomial_one (T : Fin 2 → A) :
    glnHeckePolynomial 1 q T = C (T 0) * X - C (T 1) := by
  simp [glnHeckePolynomial, Fin.sum_univ_two, sub_eq_add_neg]

/-- In rank two the Hecke polynomial is `T_0 X² - T_1 X + q T_2`. -/
theorem glnHeckePolynomial_two (T : Fin 3 → A) :
    glnHeckePolynomial 2 q T = C (T 0) * X ^ 2 - C (T 1) * X + C (q * T 2) := by
  simp [glnHeckePolynomial, Fin.sum_univ_three, sub_eq_add_neg]

/-- The **Satake factorization** of the Hecke polynomial: if `q = s²` and the Hecke operators
take the Satake values `T_i = s^{i(n-i)} e_i(z_1, …, z_n)`, then
`P(X) = ∏_j (X - s^{n-1} z_j)`. -/
theorem glnHeckePolynomial_eq_prod_X_sub_C (s : A) (z : Fin n → A) :
    glnHeckePolynomial n (s ^ 2)
        (fun i => s ^ ((i : ℕ) * (n - i)) * (Finset.univ.val.map z).esymm i) =
      ∏ j, (X - C (s ^ (n - 1) * z j)) := by
  have hprod : ∏ j, (X - C (s ^ (n - 1) * z j)) =
      (((Finset.univ.val.map z).map (s ^ (n - 1) • ·)).map fun t => X - C t).prod := by
    simp [Finset.prod_eq_multiset_prod, Function.comp_def]
  rw [hprod, Multiset.prod_X_sub_X_eq_sum_esymm, glnHeckePolynomial]
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hexp : 2 * (i : ℕ).choose 2 + i * (n - i) = (n - 1) * i := by
    rw [Nat.two_mul_choose_two_add_mul, Nat.add_sub_cancel' i.is_le, mul_comm]
  rw [← Multiset.pow_smul_esymm, smul_eq_mul, ← pow_mul s (n - 1), ← hexp]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

/-- The **twist identity**: multiplying each `T_i` by `a^i`, the effect on Hecke eigenvalues of
twisting by a character taking the value `a` at the uniformizer, replaces the Hecke polynomial
`P` by the polynomial `P'` with `P'(aX) = a^n P(X)`. When `a` is a unit, the roots of `P'` are
`a` times those of `P`. -/
theorem glnHeckePolynomial_pow_mul_comp_C_mul_X (a : A) :
    (glnHeckePolynomial n q fun i => a ^ (i : ℕ) * T i).comp (C a * X) =
      C (a ^ n) * glnHeckePolynomial n q T := by
  simp only [glnHeckePolynomial, sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (i : ℕ) + (n - i) = n := Nat.add_sub_cancel' i.is_le
  simp only [mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul]
  congr 2
  have ha : a ^ (i : ℕ) * a ^ (n - i) = a ^ n := by rw [← pow_add, hi]
  rw [← ha]
  ring

/-- The **inversion identity**, coefficientwise: if `T'_i T_n = T_{n-i}` for every `i` (as for
the images `T_{n-i} / T_n` of the `T_i` under the involution `g ↦ g⁻¹` of the spherical Hecke
algebra), then the coefficient of `X^{n-i}` in the Hecke polynomial of `T'`, multiplied by the
constant coefficient `P(0)` of the Hecke polynomial `P` of `T`, is `q^{i(n-1)}` times the
coefficient of `X^i` in `P`. -/
theorem coeff_glnHeckePolynomial_sub_mul_coeff_zero {T' : Fin (n + 1) → A}
    (hT' : ∀ i, T' i * T (Fin.last n) = T i.rev) (i : Fin (n + 1)) :
    (glnHeckePolynomial n q T').coeff (n - i) * (glnHeckePolynomial n q T).coeff 0 =
      q ^ ((i : ℕ) * (n - 1)) * (glnHeckePolynomial n q T).coeff i := by
  have hi : (glnHeckePolynomial n q T).coeff i = (glnHeckePolynomial n q T).coeff (n - i.rev) := by
    congr 1
    rw [Fin.val_rev]
    have := i.is_le
    omega
  rw [hi, coeff_glnHeckePolynomial_sub, coeff_glnHeckePolynomial_sub,
    coeff_zero_glnHeckePolynomial, ← hT' i]
  obtain ⟨j, hj⟩ : ∃ j, n = i + j := Nat.exists_eq_add_of_le i.is_le
  have hrev : ((i.rev : Fin (n + 1)) : ℕ) = j := by rw [Fin.val_rev]; omega
  rw [hrev]
  have hsign : (-1 : A) ^ (i : ℕ) * (-1) ^ (i + j : ℕ) = (-1) ^ j := by
    simp [pow_add, ← mul_assoc, ← sq, ← pow_mul]
  have hexp : (i : ℕ).choose 2 + (i + j).choose 2 = i * (i + j - 1) + j.choose 2 := by
    rw [Nat.add_choose_two, ← Nat.two_mul_choose_two_add_mul]
    ring
  rw [← hj] at hsign hexp
  calc (-1) ^ (i : ℕ) * q ^ (i : ℕ).choose 2 * T' i * ((-1) ^ n * q ^ n.choose 2 * T (Fin.last n))
      = ((-1) ^ (i : ℕ) * (-1) ^ n) * q ^ ((i : ℕ).choose 2 + n.choose 2) *
          (T' i * T (Fin.last n)) := by rw [pow_add]; ring
    _ = _ := by rw [hsign, hexp, pow_add]; ring

/-- The **inversion identity** as an identity of polynomials: if `T'_i T_n = T_{n-i}` for every
`i`, then `P(0) P'(q^{n-1} X) = q^{n(n-1)} X^n P(1/X)`, where `P` and `P'` are the Hecke
polynomials of `T` and `T'` and `X^n P(1/X)` is the reflection `reflect n P`. When `q` and
`P(0)` are units, this says that `P'(X) = q^{n(n-1)} P^rec(q^{1-n} X)` for the normalized
reciprocal `P^rec(X) = X^n P(1/X) / P(0)`, whose roots are the inverses of those of `P`. -/
theorem C_coeff_zero_mul_glnHeckePolynomial_comp_C_mul_X {T' : Fin (n + 1) → A}
    (hT' : ∀ i, T' i * T (Fin.last n) = T i.rev) :
    C ((glnHeckePolynomial n q T).coeff 0) *
        (glnHeckePolynomial n q T').comp (C (q ^ (n - 1)) * X) =
      C (q ^ (n * (n - 1))) * (glnHeckePolynomial n q T).reflect n := by
  ext k
  rw [coeff_C_mul, coeff_C_mul, comp_C_mul_X_coeff, coeff_reflect]
  rcases le_or_gt k n with hk | hk
  · obtain ⟨i, rfl⟩ : ∃ i : Fin (n + 1), k = n - i := ⟨⟨n - k, by omega⟩, by rw [Fin.val_mk]; omega⟩
    have hi := i.is_le
    have h := coeff_glnHeckePolynomial_sub_mul_coeff_zero q T hT' i
    have hexp : (i : ℕ) * (n - 1) + (n - 1) * (n - i) = n * (n - 1) := by
      rw [mul_comm (n - 1), ← add_mul, Nat.add_sub_cancel' hi]
    rw [revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hi, ← pow_mul, ← hexp, pow_add]
    linear_combination q ^ ((n - 1) * (n - i)) * h
  · rw [revAt_eq_self_of_lt hk, coeff_glnHeckePolynomial_of_lt q T' hk,
      coeff_glnHeckePolynomial_of_lt q T hk, zero_mul, mul_zero, mul_zero]

end TauCeti

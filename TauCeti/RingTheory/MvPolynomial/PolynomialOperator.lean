/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Transvection
public import TauCeti.Algebra.MvPolynomial.Monomial
public import TauCeti.Algebra.MvPolynomial.PolynomialOperator
public import TauCeti.RingTheory.MvPolynomial.BinaryMonomial
import TauCeti.Algebra.Module.Rat

/-!
# Powers of the operators `X a ∂_b` and the `sl₂`-ladder on binary forms

For variables `a` and `b`, `TauCeti.polynomialOperator R a b` is the derivation `X a ∂_b` of
`R[Xᵢ : i ∈ σ]` (defined in `TauCeti.Algebra.MvPolynomial.PolynomialOperator`, together with its
action on variables and monomials, the preservation of homogeneous degrees and the commutation
relations of the elementary matrices). This file computes its powers, as linear endomorphisms, on
monomials. They make `X a ∂_b` the infinitesimal form of the substitution of standard vectors
`TauCeti.polynomialAction`: for `a ≠ b` the transvection `1 + t E_ab` acts as the finite
exponential series `∑ₖ tᵏ / k! (X a ∂_b)ᵏ`.

In two variables, with `x = X 0` and `y = X 1`, the raising operator `E = x ∂_y`, the lowering
operator `F = y ∂_x` and `H = ⁅E, F⁆ = x ∂_x - y ∂_y` form an `sl₂`-triple. On the binary monomials
`e_i = x ^ (d - i) * y ^ i` they act by the ladder formulas

`E e_i = i e_(i-1)`, `F e_i = (d - i) e_(i+1)`, `H e_i = (d - 2i) e_i`,

with zero endpoints. The transvections `!![1, t; 0, 1]` and `!![1, 0; t, 1]` act as the
exponentials of `t E` and `t F`. The `sl₂`-triple itself and the primitive vector `x ^ d` are in
`TauCeti/Algebra/Lie/Sl2/BinaryForm.lean`.

## Main results

* `TauCeti.polynomialOperator_mul`: `X a ∂_b` satisfies the Leibniz rule.
* `TauCeti.pow_polynomialOperator_X_pow`: for `a ≠ b`,
  `(X a ∂_b)ᵏ (X b ^ m) = m(m-1)⋯(m-k+1) X a ^ k X b ^ (m-k)`.
* `TauCeti.pow_polynomialOperator_monomial`: for `a ≠ b`, the same formula on a monomial `r X^s`.
* `TauCeti.polynomialAction_transvection_monomial`: the transvection `1 + t E_ab` on a monomial,
  with binomial coefficients, in every characteristic.
* `TauCeti.polynomialAction_transvection`: the transvection `1 + t E_ab` acts as
  `∑ₖ tᵏ / k! (X a ∂_b)ᵏ`.
* `TauCeti.pow_polynomialOperator_zero_one_polynomialMonomial`,
  `TauCeti.pow_polynomialOperator_one_zero_polynomialMonomial`: the ladder formulas on the binary
  monomials.
* `TauCeti.polynomialAction_transvection_zero_one_polynomialMonomial`,
  `TauCeti.polynomialAction_transvection_one_zero_polynomialMonomial`: the transvections
  `!![1, t; 0, 1]` and `!![1, 0; t, 1]` on the binary monomials, with binomial coefficients, in
  every characteristic.
* `TauCeti.lie_polynomialOperator_zero_one_one_zero`: `⁅x ∂_y, y ∂_x⁆ = x ∂_x - y ∂_y`.

## References

* P. Etingof, *Lie Groups and Lie Algebras*, arXiv:2201.09397v5, §11.4, pp. 62–64: the
  representations of `sl₂` on homogeneous polynomials in two variables and their ladder.
-/

public section

open MvPolynomial Matrix

namespace TauCeti

section Operator

variable {σ R : Type*} [CommSemiring R]

/-- `X a ∂_b` satisfies the Leibniz rule. -/
theorem polynomialOperator_mul (a b : σ) (p q : MvPolynomial σ R) :
    polynomialOperator R a b (p * q) =
      polynomialOperator R a b p * q + p * polynomialOperator R a b q := by
  simp only [polynomialOperator_apply, pderiv_mul]
  ring

theorem polynomialOperator_C (a b : σ) (r : R) : polynomialOperator R a b (C r) = 0 := by
  simp

/-- `X a ∂_a` multiplies a monomial by its degree in `a`. This takes precedence over
`polynomialOperator_monomial` on the diagonal. -/
@[simp high]
theorem polynomialOperator_self_monomial (a : σ) (s : σ →₀ ℕ) (r : R) :
    polynomialOperator R a a (monomial s r) = s a • monomial s r := by
  rw [polynomialOperator_apply]
  exact X_mul_pderiv_monomial

end Operator

section Power

variable {σ R : Type*} [CommSemiring R] {a b : σ}

/-- For `a ≠ b`, `(X a ∂_b)ᵏ (X b ^ m) = m(m-1)⋯(m-k+1) X a ^ k X b ^ (m - k)`. -/
theorem pow_polynomialOperator_X_pow (hab : a ≠ b) (k m : ℕ) :
    ((polynomialOperator R a b).toLinearMap ^ k) (X b ^ m) =
      (m.descFactorial k : R) • (X a ^ k * X b ^ (m - k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih]
    simp [polynomialOperator_apply, pderiv_X_of_ne hab, Nat.descFactorial_succ, Nat.sub_sub,
      smul_eq_C_mul]
    ring

/-- If `X a ∂_b` kills `q`, then it commutes with multiplication by `q`. -/
private theorem pow_polynomialOperator_mul_of_eq_zero {q : MvPolynomial σ R}
    (hq : polynomialOperator R a b q = 0) (k : ℕ) (p : MvPolynomial σ R) :
    ((polynomialOperator R a b).toLinearMap ^ k) (p * q) =
      ((polynomialOperator R a b).toLinearMap ^ k) p * q := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, Derivation.coeFn_coe, polynomialOperator_mul,
      hq, mul_zero, add_zero, mul_apply_eq_comp, Derivation.coeFn_coe]

/-- For `a ≠ b`, `(X a ∂_b)ᵏ` sends the monomial `r X^s` to
`s_b(s_b-1)⋯(s_b-k+1) X a ^ k X b ^ (s_b - k) r X^(s - s_b e_b)`. -/
theorem pow_polynomialOperator_monomial (hab : a ≠ b) (k : ℕ) (s : σ →₀ ℕ) (r : R) :
    ((polynomialOperator R a b).toLinearMap ^ k) (monomial s r) =
      ((s b).descFactorial k : R) • (X a ^ k * X b ^ (s b - k) * monomial (s.erase b) r) := by
  have hkill : polynomialOperator R a b (monomial (s.erase b) r) = 0 := by
    simp
  rw [monomial_eq_X_pow_mul_monomial_erase b s r, pow_polynomialOperator_mul_of_eq_zero hkill,
    pow_polynomialOperator_X_pow hab, smul_mul_assoc]

end Power

section Transvection

variable {σ R : Type*} [CommRing R] {a b : σ} [Fintype σ] [DecidableEq σ]

/-- The transvection `1 + t E_ab` substitutes `X b ↦ X b + t X a` and fixes the other variables. -/
theorem polynomialAction_transvection_X (t : R) (j : σ) :
    polynomialAction (transvection a b t) (X j) = X j + if j = b then C t * X a else 0 := by
  simp only [polynomialAction_X, transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, map_add, add_mul, Finset.sum_add_distrib]
  rcases eq_or_ne b j with rfl | h
  · simp [apply_ite C, ite_mul]
  · simp [h, Ne.symm h]

/-- The transvection `1 + t E_ab` fixes the monomials not involving `X b`. -/
private theorem polynomialAction_transvection_monomial_of_eq_zero (t : R) {s : σ →₀ ℕ}
    (hs : s b = 0) (r : R) :
    polynomialAction (transvection a b t) (monomial s r) = monomial s r := by
  rw [monomial_eq, map_mul, algHom_C, map_finsuppProd]
  congr 1
  refine Finsupp.prod_congr fun j hj ↦ ?_
  have hjb : j ≠ b := by rintro rfl; exact Finsupp.mem_support_iff.mp hj hs
  rw [map_pow, polynomialAction_transvection_X]
  simp [hjb]

/-- **The transvection on a monomial**, the characteristic-free form of the exponential formula:
`1 + t E_ab` substitutes `X b ↦ X b + t X a`, so it sends `r X^s` to
`∑_{k ≤ s b} (s b choose k) tᵏ X a ^ k X b ^ (s b - k) r X^s'`, where `s'` is `s` with the
exponent of `X b` erased. -/
theorem polynomialAction_transvection_monomial (t : R) (s : σ →₀ ℕ)
    (r : R) :
    polynomialAction (transvection a b t) (monomial s r) =
      ∑ k ∈ Finset.range (s b + 1), ((s b).choose k * t ^ k : R) •
        (X a ^ k * X b ^ (s b - k) * monomial (s.erase b) r) := by
  rw [monomial_eq_X_pow_mul_monomial_erase b, map_mul,
    polynomialAction_transvection_monomial_of_eq_zero t (Finsupp.erase_same),
    map_pow, polynomialAction_transvection_X]
  simp only [↓reduceIte]
  rw [add_comm, add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_pow, smul_eq_C_mul, map_mul, map_pow, map_natCast]
  ring

/-- The transvection `1 + t E_ab` on `X a ^ p * X b ^ q`, for `a ≠ b`: the binomial expansion of
`X a ^ p * (X b + t X a) ^ q`, summed over any range `k ≤ N` with `q ≤ N`, since the terms with
`k > q` vanish. -/
private theorem polynomialAction_transvection_X_pow_mul_X_pow (hab : a ≠ b) (t : R) (p : ℕ)
    {q N : ℕ} (hq : q ≤ N) :
    polynomialAction (transvection a b t) (X a ^ p * X b ^ q) =
      ∑ k ∈ Finset.range (N + 1), ((q.choose k : R) * t ^ k) • (X a ^ (p + k) * X b ^ (q - k)) := by
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : q + 1 ≤ N + 1)),
    X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul,
    polynomialAction_transvection_monomial]
  · refine Finset.sum_congr (by simp [hab]) fun k _ ↦ ?_
    simp [hab, Finsupp.erase_add, ← X_pow_eq_monomial, mul_right_comm _ (X b ^ _), ← pow_add,
      add_comm k p]
  · intro k _ hk
    simp [Nat.choose_eq_zero_of_lt (by simpa using hk : q < k)]

/-- **The exponential formula for a transvection**: over a `ℚ`-algebra, for `a ≠ b` the
transvection `1 + t E_ab` acts on a polynomial of degree at most `N` in `X b` as the finite
exponential series `∑_{k ≤ N} tᵏ / k! (X a ∂_b)ᵏ`. -/
theorem polynomialAction_transvection [Algebra ℚ R] (hab : a ≠ b) (t : R) {N : ℕ}
    {p : MvPolynomial σ R} (hp : p.degreeOf b ≤ N) :
    polynomialAction (transvection a b t) p =
      ∑ k ∈ Finset.range (N + 1),
        ((k.factorial : ℚ)⁻¹ • t ^ k) • ((polynomialOperator R a b).toLinearMap ^ k) p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hsN : s b ≤ N := (monomial_le_degreeOf b hs).trans hp
  -- The coefficient `tᵏ / k!` times the descending factorial is the binomial term.
  have hcoef (k : ℕ) :
      ((k.factorial : ℚ)⁻¹ • t ^ k) * ((s b).descFactorial k : R) =
        ((s b).choose k : R) * t ^ k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, smul_mul_assoc, mul_left_comm,
      inv_natCast_smul_natCast_mul k.factorial_ne_zero]
    ring
  rw [polynomialAction_transvection_monomial, ← Finset.sum_range_add_sum_Ico _
    (Nat.succ_le_succ hsN), Finset.sum_eq_zero (s := Finset.Ico _ _), add_zero]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [pow_polynomialOperator_monomial hab, smul_smul, hcoef]
  · intro k hk
    rw [pow_polynomialOperator_monomial hab,
      Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_Ico.mp hk).1, Nat.cast_zero, zero_smul,
      smul_zero]

end Transvection

section Binary

/-! ### The `sl₂`-ladder on binary forms -/

variable {R : Type*} [CommSemiring R] {d i : ℕ}

/-- **The raising ladder**: for `i ≤ d`, the `k`-th power of `E = x ∂_y` sends the binary
monomial `e_i` to `i(i-1)⋯(i-k+1) e_(i-k)`. -/
@[simp]
theorem pow_polynomialOperator_zero_one_polynomialMonomial (h : i ≤ d) (k : ℕ) :
    ((polynomialOperator R (0 : Fin 2) 1).toLinearMap ^ k) (polynomialMonomial R d i) =
      (i.descFactorial k : R) • polynomialMonomial R d (i - k) := by
  have hkill : polynomialOperator R (0 : Fin 2) 1 (X 0 ^ (d - i)) = 0 := by
    simp [polynomialOperator_apply]
  rw [polynomialMonomial_of_le h, mul_comm, pow_polynomialOperator_mul_of_eq_zero hkill,
    pow_polynomialOperator_X_pow (by decide), smul_mul_assoc]
  rcases le_or_gt k i with hk | hk
  · rw [polynomialMonomial_of_le (by omega), show d - (i - k) = k + (d - i) by omega]
    congr 1
    ring
  · simp [Nat.descFactorial_eq_zero_iff_lt.mpr hk]

/-- **The lowering ladder**: the `k`-th power of `F = y ∂_x` sends the binary monomial `e_i` to
`(d-i)(d-i-1)⋯(d-i-k+1) e_(i+k)`. -/
@[simp]
theorem pow_polynomialOperator_one_zero_polynomialMonomial (k : ℕ) :
    ((polynomialOperator R (1 : Fin 2) 0).toLinearMap ^ k) (polynomialMonomial R d i) =
      ((d - i).descFactorial k : R) • polynomialMonomial R d (i + k) := by
  rcases le_or_gt i d with h | h
  · have hkill : polynomialOperator R (1 : Fin 2) 0 (X 1 ^ i) = 0 := by
      simp [polynomialOperator_apply]
    rw [polynomialMonomial_of_le h, pow_polynomialOperator_mul_of_eq_zero hkill,
      pow_polynomialOperator_X_pow (by decide), smul_mul_assoc]
    rcases le_or_gt (i + k) d with hk | hk
    · rw [polynomialMonomial_of_le hk, Nat.sub_sub]
      congr 1
      ring
    · simp [Nat.descFactorial_eq_zero_iff_lt.mpr (show d - i < k by omega)]
  · rw [polynomialMonomial_of_lt h, polynomialMonomial_of_lt (by omega), map_zero, smul_zero]

/-- `E = x ∂_y` sends `e_i` to `i e_(i-1)` for `i ≤ d`; in particular it kills `e_0 = x ^ d`. -/
@[simp]
theorem polynomialOperator_zero_one_polynomialMonomial (h : i ≤ d) :
    polynomialOperator R (0 : Fin 2) 1 (polynomialMonomial R d i) =
      (i : R) • polynomialMonomial R d (i - 1) := by
  simpa only [pow_one, Nat.descFactorial_one, Derivation.coeFn_coe] using
    pow_polynomialOperator_zero_one_polynomialMonomial (R := R) h 1

/-- `F = y ∂_x` sends `e_i` to `(d - i) e_(i+1)`; in particular it kills `e_d = y ^ d`. -/
@[simp]
theorem polynomialOperator_one_zero_polynomialMonomial :
    polynomialOperator R (1 : Fin 2) 0 (polynomialMonomial R d i) =
      ((d - i : ℕ) : R) • polynomialMonomial R d (i + 1) := by
  simpa only [pow_one, Nat.descFactorial_one, Derivation.coeFn_coe] using
    pow_polynomialOperator_one_zero_polynomialMonomial (R := R) (d := d) (i := i) 1

/-- `x ∂_x` multiplies `e_i` by its degree `d - i` in `x`. -/
@[simp]
theorem polynomialOperator_zero_zero_polynomialMonomial :
    polynomialOperator R (0 : Fin 2) 0 (polynomialMonomial R d i) =
      ((d - i : ℕ) : R) • polynomialMonomial R d i := by
  rcases le_or_gt i d with h | h
  · rw [polynomialMonomial_eq_monomial h, polynomialOperator_self_monomial, Nat.cast_smul_eq_nsmul]
    simp
  · simp [polynomialMonomial_of_lt h]

/-- `y ∂_y` multiplies `e_i` by its degree `i` in `y`. -/
@[simp]
theorem polynomialOperator_one_one_polynomialMonomial :
    polynomialOperator R (1 : Fin 2) 1 (polynomialMonomial R d i) =
      (i : R) • polynomialMonomial R d i := by
  rcases le_or_gt i d with h | h
  · rw [polynomialMonomial_eq_monomial h, polynomialOperator_self_monomial, Nat.cast_smul_eq_nsmul]
    simp
  · simp [polynomialMonomial_of_lt h]

end Binary

section BinaryTransvection

variable {R : Type*} [CommRing R] {d i : ℕ}

/-- **The upper unitriangular matrix on binary monomials**: `!![1, t; 0, 1]` substitutes
`y ↦ y + t x`, so it sends `e_i = x ^ (d - i) * y ^ i` to `∑ₖ (i choose k) tᵏ e_(i-k)`, in every
characteristic. The terms with `k > i` vanish. -/
theorem polynomialAction_transvection_zero_one_polynomialMonomial (t : R) (h : i ≤ d) :
    polynomialAction (transvection (0 : Fin 2) 1 t) (polynomialMonomial R d i) =
      ∑ k ∈ Finset.range (d + 1), ((i.choose k : R) * t ^ k) • polynomialMonomial R d (i - k) := by
  rw [polynomialMonomial_of_le h, polynomialAction_transvection_X_pow_mul_X_pow (by decide) t _ h]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rcases le_or_gt k i with hk | hk
  · rw [polynomialMonomial_of_le (by omega), show d - (i - k) = d - i + k by omega]
  · simp [Nat.choose_eq_zero_of_lt hk]

/-- **The lower unitriangular matrix on binary monomials**: `!![1, 0; t, 1]` substitutes
`x ↦ x + t y`, so it sends `e_i = x ^ (d - i) * y ^ i` to `∑ₖ (d - i choose k) tᵏ e_(i+k)`, in
every characteristic. The terms with `i + k > d` vanish. -/
theorem polynomialAction_transvection_one_zero_polynomialMonomial (t : R) (h : i ≤ d) :
    polynomialAction (transvection (1 : Fin 2) 0 t) (polynomialMonomial R d i) =
      ∑ k ∈ Finset.range (d + 1),
        (((d - i).choose k : R) * t ^ k) • polynomialMonomial R d (i + k) := by
  rw [polynomialMonomial_of_le h, mul_comm,
    polynomialAction_transvection_X_pow_mul_X_pow (by decide) t _ (Nat.sub_le d i)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rcases le_or_gt k (d - i) with hk | hk
  · rw [polynomialMonomial_of_le (by omega), Nat.sub_sub, mul_comm (X 0 ^ _)]
  · simp [Nat.choose_eq_zero_of_lt hk]

end BinaryTransvection

section Lie

variable (R : Type*) [CommRing R]

/-- `H = ⁅x ∂_y, y ∂_x⁆` is `x ∂_x - y ∂_y`. -/
theorem lie_polynomialOperator_zero_one_one_zero :
    ⁅polynomialOperator R (0 : Fin 2) 1, polynomialOperator R (1 : Fin 2) 0⁆ =
      polynomialOperator R (0 : Fin 2) 0 - polynomialOperator R (1 : Fin 2) 1 := by
  simp [lie_polynomialOperator]

end Lie

end TauCeti

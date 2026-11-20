/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import TauCeti.Algebra.MvPolynomial.Monomial
public import TauCeti.RingTheory.MvPolynomial.BinaryMonomial
import TauCeti.Algebra.Module.Rat

/-!
# The operators `X a ∂_b` on polynomials

For variables `a` and `b`, `TauCeti.polynomialOperator a b` is the derivation `X a ∂_b` of
`R[Xᵢ : i ∈ σ]`. These operators preserve every homogeneous degree and satisfy the commutation
relations of the elementary matrices,

`⁅X a ∂_b, X c ∂_d⁆ = δ_bc X a ∂_d - δ_da X c ∂_b`,

so `E_ab ↦ X a ∂_b` is the action of `gl_σ` on polynomials. It is the infinitesimal form of the
substitution of standard vectors `TauCeti.polynomialAction`: for `a ≠ b` the transvection
`1 + t E_ab` acts as the finite exponential series `∑ₖ tᵏ / k! (X a ∂_b)ᵏ`.

In two variables, with `x = X 0` and `y = X 1`, the raising operator `E = x ∂_y`, the lowering
operator `F = y ∂_x` and `H = ⁅E, F⁆ = x ∂_x - y ∂_y` form an `sl₂`-triple. On the binary monomials
`e_i = x ^ (d - i) * y ^ i` they act by the ladder formulas

`E e_i = i e_(i-1)`, `F e_i = (d - i) e_(i+1)`, `H e_i = (d - 2i) e_i`,

with zero endpoints. The transvections `!![1, t; 0, 1]` and `!![1, 0; t, 1]` act as the
exponentials of `t E` and `t F`. The `sl₂`-triple itself and the primitive vector `x ^ d` are in
`TauCeti/Algebra/Lie/Sl2/BinaryForm.lean`.

On a tensor product of two polynomial rings, `X a ∂_b` acts by the Leibniz rule on both factors;
over a ring this is Mathlib's tensor product of Lie modules. Multiplication of polynomials
intertwines this action with the action on the product.

## Main definitions

* `TauCeti.polynomialOperator`: the operator `X a ∂_b`.
* `TauCeti.tensorPolynomialOperator`: the action of `X a ∂_b` on `R[X_σ] ⊗ R[X_σ]`.

## Main results

* `TauCeti.polynomialOperator_def`: `X a ∂_b` is the derivation `X a • pderiv b`.
* `TauCeti.polynomialOperator_mul`: `X a ∂_b` satisfies the Leibniz rule.
* `MvPolynomial.IsHomogeneous.polynomialOperator`: `X a ∂_b` preserves homogeneous degrees.
* `TauCeti.lie_polynomialOperator`: the commutation relations of the elementary matrices.
* `TauCeti.pow_polynomialOperator_X_pow`: for `a ≠ b`,
  `(X a ∂_b)ᵏ (X b ^ m) = m(m-1)⋯(m-k+1) X a ^ k X b ^ (m-k)`.
* `TauCeti.pow_polynomialOperator_monomial`: for `a ≠ b`, the same formula on a monomial `r X^s`.
* `TauCeti.polynomialAction_transvection`: the transvection `1 + t E_ab` acts as
  `∑ₖ tᵏ / k! (X a ∂_b)ᵏ`.
* `TauCeti.pow_polynomialOperator_zero_one_polynomialMonomial`,
  `TauCeti.pow_polynomialOperator_one_zero_polynomialMonomial`: the ladder formulas on the binary
  monomials.
* `TauCeti.lie_polynomialOperator_zero_one_one_zero`: `⁅x ∂_y, y ∂_x⁆ = x ∂_x - y ∂_y`.
* `TauCeti.polynomialOperator_X_pow_mul_X_pow_succ` and
  `TauCeti.polynomialOperator_self_sub_polynomialOperator_self_X_pow_mul_X_pow`: the action of
  `x ∂_y` and of `x ∂_x - y ∂_y` on the monomials `x ^ i y ^ j` in two distinct variables.
* `TauCeti.tensorPolynomialOperator_tmul` and `TauCeti.lie_tensorPolynomialOperator`: the
  Leibniz rule on pure tensors and the `gl_σ` relations on the tensor product.

## References

* P. Etingof, *Lie Groups and Lie Algebras*, arXiv:2201.09397v5, §11.4, pp. 62–64: the
  representations of `sl₂` on homogeneous polynomials in two variables and their ladder.
-/

public section

open MvPolynomial Matrix

namespace TauCeti

section Operator

variable {σ R : Type*} [CommSemiring R]

variable (R) in
/-- The operator `X a ∂_b` on polynomials: the partial derivative in the variable `b` followed by
multiplication by the variable `a`. -/
noncomputable def polynomialOperator (a b : σ) : Module.End R (MvPolynomial σ R) :=
  ((X a : MvPolynomial σ R) • pderiv b : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))

variable (R) in
/-- `X a ∂_b` is the derivation `X a • pderiv b`, viewed as a linear map. -/
theorem polynomialOperator_def (a b : σ) :
    polynomialOperator R a b =
      (((X a : MvPolynomial σ R) • pderiv b : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) :
        Module.End R (MvPolynomial σ R)) :=
  (rfl)

theorem polynomialOperator_apply (a b : σ) (p : MvPolynomial σ R) :
    polynomialOperator R a b p = X a * pderiv b p :=
  (rfl)

/-- `X a ∂_b` satisfies the Leibniz rule. -/
theorem polynomialOperator_mul (a b : σ) (p q : MvPolynomial σ R) :
    polynomialOperator R a b (p * q) =
      polynomialOperator R a b p * q + p * polynomialOperator R a b q := by
  simp only [polynomialOperator_apply, pderiv_mul]
  ring

@[simp]
theorem polynomialOperator_C (a b : σ) (r : R) : polynomialOperator R a b (C r) = 0 := by
  simp [polynomialOperator_apply]

@[simp]
theorem polynomialOperator_X [DecidableEq σ] (a b c : σ) :
    polynomialOperator R a b (X c) = if c = b then X a else 0 := by
  simp [polynomialOperator_apply, Pi.single_apply]

@[simp]
theorem polynomialOperator_X_self (a b : σ) : polynomialOperator R a b (X b) = X a := by
  simp [polynomialOperator_apply]

@[simp]
theorem polynomialOperator_X_of_ne {a b c : σ} (h : c ≠ b) :
    polynomialOperator R a b (X c) = 0 := by
  simp [polynomialOperator_apply, h]

/-- `X a ∂_b` sends the monomial `r X^s` to `s_b r X^(s - e_b + e_a)`. -/
@[simp]
theorem polynomialOperator_monomial (a b : σ) (s : σ →₀ ℕ) (r : R) :
    polynomialOperator R a b (monomial s r) =
      monomial (Finsupp.single a 1 + (s - Finsupp.single b 1)) (r * s b) := by
  rw [polynomialOperator_apply, pderiv_monomial, X, monomial_mul_monomial, one_mul]

/-- `X a ∂_a` multiplies a monomial by its degree in `a`. This takes precedence over
`polynomialOperator_monomial` on the diagonal. -/
@[simp high]
theorem polynomialOperator_self_monomial (a : σ) (s : σ →₀ ℕ) (r : R) :
    polynomialOperator R a a (monomial s r) = s a • monomial s r := by
  rw [polynomialOperator_apply]
  exact X_mul_pderiv_monomial

end Operator

/-- `X a ∂_b` preserves the homogeneous polynomials of each degree. -/
theorem _root_.MvPolynomial.IsHomogeneous.polynomialOperator {σ R : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) (a b : σ) :
    (TauCeti.polynomialOperator R a b p).IsHomogeneous n := by
  rw [polynomialOperator_apply]
  obtain _ | n := n
  · rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hp
    rw [hp, pderiv_C, mul_zero]
    exact isHomogeneous_zero _ _ _
  · simpa [add_comm] using (isHomogeneous_X R a).mul (IsHomogeneous.pderiv (i := b) hp)

section Lie

variable {σ R : Type*} [CommRing R]

/-- **The commutation relations of the elementary matrices**:
`⁅X a ∂_b, X c ∂_d⁆ = δ_bc X a ∂_d - δ_da X c ∂_b`, so `E_ab ↦ X a ∂_b` is a Lie algebra action
of `gl_σ` on polynomials. -/
theorem lie_polynomialOperator [DecidableEq σ] (a b c d : σ) :
    ⁅polynomialOperator R a b, polynomialOperator R c d⁆ =
      (if b = c then polynomialOperator R a d else 0) -
        if d = a then polynomialOperator R c b else 0 := by
  -- Both sides are derivations, so it suffices to compare them on the variables.
  let D : σ → σ → Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
    fun a b ↦ (X a : MvPolynomial σ R) • pderiv b
  have hD : ⁅D a b, D c d⁆ = (if b = c then D a d else 0) - if d = a then D c b else 0 := by
    refine derivation_ext fun i ↦ ?_
    simp only [D, Derivation.commutator_apply, smul_apply, sub_apply, pderiv_X, smul_eq_mul,
      Pi.single_apply]
    split_ifs <;> simp_all
  rw [polynomialOperator_def, polynomialOperator_def, ← Derivation.commutator_coe_linear_map, hD,
    Derivation.coe_sub_linearMap]
  split_ifs <;> simp [D, polynomialOperator_def]

end Lie

section Power

variable {σ R : Type*} [CommSemiring R] {a b : σ}

/-- For `a ≠ b`, `(X a ∂_b)ᵏ (X b ^ m) = m(m-1)⋯(m-k+1) X a ^ k X b ^ (m - k)`. -/
theorem pow_polynomialOperator_X_pow (hab : a ≠ b) (k m : ℕ) :
    (polynomialOperator R a b ^ k) (X b ^ m) =
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
    (polynomialOperator R a b ^ k) (p * q) = (polynomialOperator R a b ^ k) p * q := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, polynomialOperator_mul, hq, mul_zero,
      add_zero, mul_apply_eq_comp]

/-- For `a ≠ b`, `(X a ∂_b)ᵏ` sends the monomial `r X^s` to
`s_b(s_b-1)⋯(s_b-k+1) X a ^ k X b ^ (s_b - k) r X^(s - s_b e_b)`. -/
theorem pow_polynomialOperator_monomial (hab : a ≠ b) (k : ℕ) (s : σ →₀ ℕ) (r : R) :
    (polynomialOperator R a b ^ k) (monomial s r) =
      ((s b).descFactorial k : R) • (X a ^ k * X b ^ (s b - k) * monomial (s.erase b) r) := by
  have hkill : polynomialOperator R a b (monomial (s.erase b) r) = 0 := by
    simp
  rw [monomial_eq_X_pow_mul_monomial_erase b s r, pow_polynomialOperator_mul_of_eq_zero hkill,
    pow_polynomialOperator_X_pow hab, smul_mul_assoc]

/-- For distinct variables `x = X a` and `y = X b`,
`x ∂_y (x ^ i y ^ (j + 1)) = (j + 1) x ^ (i + 1) y ^ j`. -/
theorem polynomialOperator_X_pow_mul_X_pow_succ (hab : a ≠ b) (i j : ℕ) :
    polynomialOperator R a b (X a ^ i * X b ^ (j + 1)) =
      ((j : R) + 1) • (X a ^ (i + 1) * X b ^ j) := by
  simp [polynomialOperator_apply, pderiv_X_of_ne hab, Algebra.smul_def]
  ring

end Power

section Weight

variable {σ R : Type*} [CommRing R] {a b : σ}

/-- For distinct variables `x = X a` and `y = X b`, `x ∂_x - y ∂_y` acts on `x ^ i y ^ j` by the
weight `i - j`. -/
theorem polynomialOperator_self_sub_polynomialOperator_self_X_pow_mul_X_pow (hab : a ≠ b)
    (i j : ℕ) :
    (polynomialOperator R a a - polynomialOperator R b b) (X a ^ i * X b ^ j) =
      ((i : R) - j) • (X a ^ i * X b ^ j) := by
  rcases i with _ | i <;> rcases j with _ | j <;>
    simp [polynomialOperator_apply, pderiv_X_of_ne hab, pderiv_X_of_ne hab.symm,
      Algebra.smul_def] <;> ring

end Weight

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

/-- The exponential formula on a monomial: the characteristic-free form, with binomial
coefficients. -/
private theorem polynomialAction_transvection_monomial (t : R) (s : σ →₀ ℕ)
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

/-- **The exponential formula for a transvection**: over a `ℚ`-algebra, for `a ≠ b` the
transvection `1 + t E_ab` acts on a polynomial of degree at most `N` in `X b` as the finite
exponential series `∑_{k ≤ N} tᵏ / k! (X a ∂_b)ᵏ`. -/
theorem polynomialAction_transvection [Algebra ℚ R] (hab : a ≠ b) (t : R) {N : ℕ}
    {p : MvPolynomial σ R} (hp : p.degreeOf b ≤ N) :
    polynomialAction (transvection a b t) p =
      ∑ k ∈ Finset.range (N + 1),
        ((k.factorial : ℚ)⁻¹ • t ^ k) • (polynomialOperator R a b ^ k) p := by
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
    (polynomialOperator R (0 : Fin 2) 1 ^ k) (polynomialMonomial R d i) =
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
    (polynomialOperator R (1 : Fin 2) 0 ^ k) (polynomialMonomial R d i) =
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
  simpa only [pow_one, Nat.descFactorial_one] using
    pow_polynomialOperator_zero_one_polynomialMonomial (R := R) h 1

/-- `F = y ∂_x` sends `e_i` to `(d - i) e_(i+1)`; in particular it kills `e_d = y ^ d`. -/
@[simp]
theorem polynomialOperator_one_zero_polynomialMonomial :
    polynomialOperator R (1 : Fin 2) 0 (polynomialMonomial R d i) =
      ((d - i : ℕ) : R) • polynomialMonomial R d (i + 1) := by
  simpa only [pow_one, Nat.descFactorial_one] using
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

section Lie

variable (R : Type*) [CommRing R]

/-- `H = ⁅x ∂_y, y ∂_x⁆` is `x ∂_x - y ∂_y`. -/
theorem lie_polynomialOperator_zero_one_one_zero :
    ⁅polynomialOperator R (0 : Fin 2) 1, polynomialOperator R (1 : Fin 2) 0⁆ =
      polynomialOperator R (0 : Fin 2) 0 - polynomialOperator R (1 : Fin 2) 1 := by
  simp [lie_polynomialOperator]

end Lie

section Tensor

/-! ### The action on a tensor product -/

open TensorProduct

variable {σ : Type*}

section CommSemiring

variable (R : Type*) [CommSemiring R]

/-- The action of `X a ∂_b` on `R[X_σ] ⊗ R[X_σ]`: `X a ∂_b ⊗ 1 + 1 ⊗ X a ∂_b`. Over a ring, this
is the action of the tensor product of Lie modules, see
`TauCeti.tensorPolynomialOperator_eq_toEnd`. -/
noncomputable def tensorPolynomialOperator (a b : σ) :
    Module.End R (MvPolynomial σ R ⊗[R] MvPolynomial σ R) :=
  (polynomialOperator R a b).rTensor _ + (polynomialOperator R a b).lTensor _

/-- The action on the tensor product is `X a ∂_b ⊗ 1 + 1 ⊗ X a ∂_b`. -/
theorem tensorPolynomialOperator_def (a b : σ) :
    tensorPolynomialOperator R a b =
      (polynomialOperator R a b).rTensor _ + (polynomialOperator R a b).lTensor _ :=
  (rfl)

/-- **The Leibniz rule on pure tensors**: `X a ∂_b` acts on `p ⊗ q` through each factor in
turn. -/
@[simp]
theorem tensorPolynomialOperator_tmul (a b : σ) (p q : MvPolynomial σ R) :
    tensorPolynomialOperator R a b (p ⊗ₜ q) =
      polynomialOperator R a b p ⊗ₜ q + p ⊗ₜ polynomialOperator R a b q := by
  simp [tensorPolynomialOperator_def]

/-- Multiplication of polynomials intertwines the action of `X a ∂_b` on the tensor product with
its action on `R[X_σ]`: this is the Leibniz rule `D (p q) = D p q + p D q`. -/
theorem mul'_tensorPolynomialOperator (a b : σ) (x : MvPolynomial σ R ⊗[R] MvPolynomial σ R) :
    LinearMap.mul' R _ (tensorPolynomialOperator R a b x) =
      polynomialOperator R a b (LinearMap.mul' R _ x) := by
  have : LinearMap.mul' R _ ∘ₗ tensorPolynomialOperator R a b =
      polynomialOperator R a b ∘ₗ LinearMap.mul' R (MvPolynomial σ R) :=
    TensorProduct.ext' fun p q ↦ by simp [polynomialOperator_mul]
  exact congr($this x)

end CommSemiring

/- The commutator of two endomorphisms is the bracket of `LieRing.ofAssociativeRing`, which is a
local instance here, as in Mathlib. -/
attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

/-- The action of `X a ∂_b` on `R[X_σ] ⊗ R[X_σ]` is that of the tensor product of Lie modules
over the endomorphisms of `R[X_σ]`. -/
theorem tensorPolynomialOperator_eq_toEnd (a b : σ) :
    tensorPolynomialOperator R a b =
      LieModule.toEnd R (Module.End R (MvPolynomial σ R)) _ (polynomialOperator R a b) :=
  TensorProduct.ext' fun p q ↦ by simp [LieModule.toEnd_apply_apply]

/-- **The `gl_σ` relations on the tensor product**: the total operators commute like the
elementary matrices. -/
theorem lie_tensorPolynomialOperator [DecidableEq σ] (a b c d : σ) :
    ⁅tensorPolynomialOperator R a b, tensorPolynomialOperator R c d⁆ =
      (if b = c then tensorPolynomialOperator R a d else 0) -
        if d = a then tensorPolynomialOperator R c b else 0 := by
  simp only [tensorPolynomialOperator_eq_toEnd]
  rw [← LieHom.map_lie, lie_polynomialOperator, map_sub]
  split_ifs <;> simp only [map_zero]

end Tensor

end TauCeti

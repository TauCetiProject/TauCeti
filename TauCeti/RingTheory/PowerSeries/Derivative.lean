/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.CharP.Invertible

/-!
# Derivative identities for power series

For a power series `v` over a commutative semiring and `e, n : ℕ` with `e ≠ 0`,

`e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1) - 1) (v ^ n * v')`,

and for all `e, n : ℕ` (including `e = 0`),

`e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1)) (X * (v ^ n * v'))`.

Over a ring in which `n + 1` is not a zero divisor this is the coefficient of
`X ^ (e * (n + 1) - 1)` in `(v ^ (n + 1))' = (n + 1) v ^ n v'`, divided by `n + 1`. The identity
holds over every commutative semiring because both sides are polynomials with natural-number
coefficients in the coefficients of `v`; the proof specializes the generic power series with
coefficients the variables of `MvPolynomial ℕ ℕ`.

In positive characteristic `p` the division by `n + 1` is unavailable when `p ∣ n + 1`, and this
identity is what replaces it. Applied to the inverse of a unit `u ∈ R⟦X⟧ˣ` over a commutative ring,
since `(u⁻¹)' = -(u⁻¹)² u'`, it yields the universal coefficient identity

`(e : R) * coeff (e * k) (u ^ (-k)) + coeff (e * k - 1) (u ^ (-k - 1) * u') = 0`

for `e, k ≥ 1`, which governs the behaviour of residues under a substitution `X ↦ φ` of order `e`.

Substitution by a series satisfying `a' = w(a)` intertwines the weighted derivative
`w d/dX` to the ordinary derivative. The iterated chain rule then reads the constant coefficient
of an iterated weighted derivative as a factorial-scaled coefficient after substitution.

## Main results

* `PowerSeries.derivative_subst_of_derivative_eq_subst`: the weighted chain rule for a
  substitution satisfying `a' = w(a)`.
* `PowerSeries.iterate_derivative_subst`,
  `PowerSeries.constantCoeff_iterate_of_derivative_subst`: iteration and coefficient extraction
  for an operator intertwined with the derivative by substitution.
* `PowerSeries.derivative_map`: the derivative commutes with change of coefficients.
* `PowerSeries.iterate_derivative_coe`: iterated derivatives of a polynomial are computed as
  polynomials.
* `PowerSeries.coeff_iterate_derivative_eq_descFactorial`: the `M`-th coefficient of `f⁽ⁱ⁾` is
  `(M + i) (M + i - 1) ⋯ (M + 1)` times the `(M + i)`-th coefficient of `f`.
* `PowerSeries.coeff_X_pow_mul_iterate_derivative`: `Xⁱ f⁽ⁱ⁾` has `M`-th coefficient
  `M (M - 1) ⋯ (M - i + 1)` times that of `f`.
* `PowerSeries.derivative_algebraMap_polynomial`, `PowerSeries.derivative_polynomial_smul`: the
  derivative of the image of a polynomial, and the Leibniz rule for the action of `R[X]` on
  `A⟦X⟧`.
* `PowerSeries.polynomial_map_algebraMap_smul`: the actions of `R[X]` and `S[X]` on `A⟦X⟧` agree
  along a scalar tower `R → S → A`.
* `PowerSeries.polynomial_C_smul`, `PowerSeries.polynomial_X_smul`,
  `PowerSeries.polynomial_X_pow_smul`, `PowerSeries.polynomial_monomial_smul`: under the action
  of `R[X]` on `A⟦X⟧`, constants act as scalars, `Xʲ` as multiplication by `Xʲ`, and `a Xʲ` as
  `a` times multiplication by `Xʲ`.
* `PowerSeries.smul_derivative_mem`: a submodule over `R[X]` stable under `p • d⁄dX` contains
  `(p * r ^ 2) • x'` whenever it contains `r • x`.
* `PowerSeries.coeff_eq_zero_of_derivative_eq_zero`: in prime characteristic `p`, a series
  with zero derivative is supported on degrees divisible by `p`.
* `PowerSeries.nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative`,
  `PowerSeries.nsmul_coeff_mul_succ_pow_succ_eq_coeff_pow_mul_derivative`:
  `e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1) - 1) (v ^ n * v')` for `e ≠ 0`, and
  its `X *`-shifted form for all `e`.
* `PowerSeries.coeff_succ_pow_succ_eq_coeff_pow_mul_derivative`: the `e = 1` case
  `coeff (n + 1) (v ^ (n + 1)) = coeff n (v ^ n * v')`.
* `PowerSeries.mul_coeff_val_zpow_neg_add_coeff_val_zpow_neg_sub_one_mul_derivative_eq_zero`:
  for a unit `u : R⟦X⟧ˣ` over a commutative ring and `e, k ≥ 1`,
  `(e : R) * coeff (e * k) (u ^ (-k)) + coeff (e * k - 1) (u ^ (-k - 1) * u') = 0`.
-/

public section

namespace PowerSeries

section CommSemiring

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The derivative of power series commutes with change of coefficients. -/
@[simp]
theorem derivative_map (φ : R⟦X⟧) (f : R →+* S) : d⁄dX (map f φ) = map f (d⁄dX φ) := by
  ext n
  simp [coeff_derivative]

/-- Iterated derivatives of a polynomial, viewed as a power series, are computed as
polynomials. -/
theorem iterate_derivative_coe (p : Polynomial R) (m : ℕ) :
    (d⁄dX)^[m] (p : R⟦X⟧) = ((Polynomial.derivative^[m] p : Polynomial R) : R⟦X⟧) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, derivative_coe,
      Function.iterate_succ_apply']

/-- The `M`-th coefficient of the `i`-th derivative is the falling factorial
`(M + i) (M + i - 1) ⋯ (M + 1)` times the `(M + i)`-th coefficient. -/
theorem coeff_iterate_derivative_eq_descFactorial (f : R⟦X⟧) (i M : ℕ) :
    coeff M ((d⁄dX)^[i] f) = (M + i).descFactorial i * coeff (M + i) f := by
  rw [coeff_iterate_derivative, Nat.add_descFactorial_eq_ascFactorial]

/-- Multiplying the `i`-th derivative by `Xⁱ` multiplies the `M`-th coefficient by the falling
factorial `M (M - 1) ⋯ (M - i + 1)`. -/
theorem coeff_X_pow_mul_iterate_derivative (f : R⟦X⟧) (i M : ℕ) :
    coeff M (X ^ i * (d⁄dX)^[i] f) = M.descFactorial i * coeff M f := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_iterate_derivative_eq_descFactorial, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (not_le.mp h), Nat.cast_zero, zero_mul]

/-- The shifted coefficient identity when `n + 1` can be cancelled. -/
private theorem nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative_of_hasUniqueDiv
    [HasUniqueDiv R] (v : R⟦X⟧)
    (e n : ℕ) :
    e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1)) (X * (v ^ n * d⁄dX v)) := by
  rcases eq_or_ne e 0 with rfl | he
  · simp [coeff_zero_X_mul]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (mul_ne_zero he (Nat.succ_ne_zero n))
    rw [hm, coeff_succ_X_mul]
    have h := coeff_derivative (v ^ (n + 1)) m
    rw [derivative_pow, Nat.add_sub_cancel, mul_assoc, ← map_natCast (C (R := R)), coeff_C_mul,
      ← Nat.cast_add_one, ← hm] at h
    apply nsmul_right_injective (Nat.succ_ne_zero n)
    simp only [nsmul_eq_mul]
    rw [← hm, Nat.succ_eq_add_one, h]
    push_cast
    ring

/-- For a power series `v` over any commutative semiring and `e, n : ℕ`, `e` times the coefficient
of `X ^ (e * (n + 1))` in `v ^ (n + 1)` is the coefficient of `X ^ (e * (n + 1))` in
`X * (v ^ n * v')`. -/
theorem nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative
    (v : R⟦X⟧) (e n : ℕ) :
    e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1)) (X * (v ^ n * d⁄dX v)) := by
  -- Specialize the identity for the generic power series over `MvPolynomial ℕ ℕ`, which has
  -- no additive torsion.
  let V : (MvPolynomial ℕ ℕ)⟦X⟧ := mk fun i ↦ MvPolynomial.X i
  let f : MvPolynomial ℕ ℕ →+* R := MvPolynomial.eval₂Hom (Nat.castRingHom R) fun i ↦ coeff i v
  have hV : map f V = v := by
    ext i
    simp [V, f]
  have h := congrArg f
    (nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative_of_hasUniqueDiv V e n)
  rwa [map_nsmul, ← coeff_map, ← coeff_map, (map f).map_pow, (map f).map_mul, map_X,
    (map f).map_mul, (map f).map_pow, ← derivative_map, hV] at h

/-- For `e ≠ 0`, `e` times the coefficient of `X ^ (e * (n + 1))` in `v ^ (n + 1)` is the
coefficient of `X ^ (e * (n + 1) - 1)` in `v ^ n * v'`, over any commutative semiring. -/
theorem nsmul_coeff_mul_succ_pow_succ_eq_coeff_pow_mul_derivative (v : R⟦X⟧) {e : ℕ} (he : e ≠ 0)
    (n : ℕ) :
    e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1) - 1) (v ^ n * d⁄dX v) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (mul_ne_zero he (Nat.succ_ne_zero n))
  rw [nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative, hm, coeff_succ_X_mul,
    Nat.add_sub_cancel]

/-- The coefficient of `X ^ (n + 1)` in `v ^ (n + 1)` is the coefficient of `X ^ n` in
`v ^ n * v'`, over any commutative semiring. -/
theorem coeff_succ_pow_succ_eq_coeff_pow_mul_derivative (v : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (v ^ (n + 1)) = coeff n (v ^ n * d⁄dX v) := by
  simpa using nsmul_coeff_mul_succ_pow_succ_eq_coeff_pow_mul_derivative v one_ne_zero n

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- An operator intertwined with the derivative by substitution satisfies the iterated chain
rule. -/
theorem iterate_derivative_subst {a : R⟦X⟧} {D : R⟦X⟧ → R⟦X⟧}
    (hD : ∀ f, d⁄dX (subst a f) = subst a (D f)) (f : R⟦X⟧) (n : ℕ) :
    d⁄dX^[n] (subst a f) = subst a (D^[n] f) := by
  have h : Function.Semiconj (subst a) D derivative := fun f ↦ (hD f).symm
  exact (h.iterate_right n f).symm

/-- If substitution by a series with zero constant coefficient intertwines an operator with the
ordinary derivative, the constant coefficient of its `n`-th iterate is `n !` times the `n`-th
coefficient after substitution. -/
theorem constantCoeff_iterate_of_derivative_subst {a : R⟦X⟧} {D : R⟦X⟧ → R⟦X⟧}
    (ha : constantCoeff a = 0) (hD : ∀ f, d⁄dX (subst a f) = subst a (D f))
    (f : R⟦X⟧) (n : ℕ) :
    constantCoeff (D^[n] f) = n.factorial * coeff n (subst a f) := by
  have hconst : constantCoeff (subst a (D^[n] f)) = constantCoeff (D^[n] f) := by
    rw [constantCoeff_eq, constantCoeff_subst_of_constantCoeff_zero ha,
      Algebra.algebraMap_self, RingHom.id_apply]
  rw [← hconst, ← iterate_derivative_subst hD, constantCoeff_iterate_derivative]

/-- If `a' = w(a)`, substitution by `a` intertwines the weighted derivative `w d/dX` with the
ordinary derivative. -/
theorem derivative_subst_of_derivative_eq_subst {a w : R⟦X⟧} (ha : HasSubst a)
    (ha' : d⁄dX a = subst a w) (f : R⟦X⟧) :
    d⁄dX (subst a f) = subst a (w * d⁄dX f) := by
  rw [derivative_subst ha, ha', subst_mul ha, mul_comm]

/-- Universal coefficient identity for a unit `u : R⟦X⟧ˣ` over a commutative ring, in shifted form
for all `e, n : ℕ`:
`e • coeff (e * (n + 1)) (u⁻¹ ^ (n + 1)) + coeff (e * (n + 1)) (X * (u⁻¹ ^ (n + 2) * u')) = 0`. -/
theorem nsmul_coeff_val_inv_pow_succ_add_coeff_X_mul_val_inv_pow_add_two_mul_derivative_eq_zero
    (u : R⟦X⟧ˣ) (e n : ℕ) :
    e • coeff (e * (n + 1)) ((↑u⁻¹ : R⟦X⟧) ^ (n + 1)) +
      coeff (e * (n + 1)) (X * ((↑u⁻¹ : R⟦X⟧) ^ (n + 2) * d⁄dX (u : R⟦X⟧))) = 0 := by
  have hd : (↑u⁻¹ : R⟦X⟧) ^ (n + 2) * d⁄dX (u : R⟦X⟧) =
      -((↑u⁻¹ : R⟦X⟧) ^ n * d⁄dX (↑u⁻¹ : R⟦X⟧)) := by
    rw [(d⁄dX).leibniz_of_mul_eq_one (Units.inv_mul u), smul_eq_mul]
    ring
  rw [hd, mul_neg, map_neg, nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative,
    add_neg_cancel]

/-- **Universal coefficient identity for negative powers of a unit power series.** For a commutative
ring `R`, a unit `u : R⟦X⟧ˣ`, and `e, k ≥ 1`,
`(e : R) * coeff (e * k) (u ^ (-k)) + coeff (e * k - 1) (u ^ (-k - 1) * u') = 0`. -/
theorem mul_coeff_val_zpow_neg_add_coeff_val_zpow_neg_sub_one_mul_derivative_eq_zero
    (u : R⟦X⟧ˣ) {e k : ℕ}
    (he : e ≠ 0) (hk : k ≠ 0) :
    (e : R) * coeff (e * k) (↑(u ^ (-(k : ℤ))) : R⟦X⟧) +
      coeff (e * k - 1) ((↑(u ^ (-(k : ℤ) - 1)) : R⟦X⟧) * d⁄dX (u : R⟦X⟧)) = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk
  have hk1 : (↑(u ^ (-((n + 1 : ℕ) : ℤ))) : R⟦X⟧) = (↑u⁻¹ : R⟦X⟧) ^ (n + 1) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  have hk2 : (↑(u ^ (-((n + 1 : ℕ) : ℤ) - 1)) : R⟦X⟧) = (↑u⁻¹ : R⟦X⟧) ^ (n + 2) := by
    rw [show -((n + 1 : ℕ) : ℤ) - 1 = -((n + 2 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  rw [hk1, hk2]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (mul_ne_zero he (Nat.succ_ne_zero n))
  simpa [nsmul_eq_mul, hm, coeff_succ_X_mul] using
    nsmul_coeff_val_inv_pow_succ_add_coeff_X_mul_val_inv_pow_add_two_mul_derivative_eq_zero
      u e n

end CommRing

section Algebra

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The image of a polynomial under `PowerSeries.algebraPolynomial` is differentiated as a
polynomial. -/
@[simp]
theorem derivative_algebraMap_polynomial (p : Polynomial R) :
    d⁄dX (algebraMap (Polynomial R) A⟦X⟧ p) =
      algebraMap (Polynomial R) A⟦X⟧ (Polynomial.derivative p) := by
  rw [algebraMap_apply', algebraMap_apply', derivative_map, derivative_coe]

/-- Iterated derivatives of the image of a polynomial under `PowerSeries.algebraPolynomial`. -/
theorem iterate_derivative_algebraMap_polynomial (p : Polynomial R) (m : ℕ) :
    (d⁄dX)^[m] (algebraMap (Polynomial R) A⟦X⟧ p) =
      algebraMap (Polynomial R) A⟦X⟧ (Polynomial.derivative^[m] p) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, derivative_algebraMap_polynomial,
      Function.iterate_succ_apply']

/-- The Leibniz rule for the action of `R[X]` on `A⟦X⟧` given by
`PowerSeries.algebraPolynomial`. -/
theorem derivative_polynomial_smul (p : Polynomial R) (f : A⟦X⟧) :
    d⁄dX (p • f) = Polynomial.derivative p • f + p • d⁄dX f := by
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Derivation.leibniz,
    derivative_algebraMap_polynomial, smul_eq_mul, smul_eq_mul, mul_comm f, add_comm]

/-- A constant polynomial acts on `A⟦X⟧` through `PowerSeries.algebraPolynomial` as the
corresponding scalar. -/
@[simp]
theorem polynomial_C_smul (a : R) (f : A⟦X⟧) : (Polynomial.C a : Polynomial R) • f = a • f := by
  rw [Algebra.smul_def, Algebra.smul_def, algebraMap_apply', Polynomial.coe_C, map_C,
    algebraMap_apply]

/-- The polynomial `Xʲ` acts on `A⟦X⟧` through `PowerSeries.algebraPolynomial` as multiplication
by the power series `Xʲ`. -/
@[simp]
theorem polynomial_X_pow_smul (j : ℕ) (f : A⟦X⟧) :
    (Polynomial.X ^ j : Polynomial R) • f = X ^ j * f := by
  rw [Algebra.smul_def, algebraMap_apply', Polynomial.coe_pow, Polynomial.coe_X, map_pow, map_X]

/-- The polynomial `X` acts on `A⟦X⟧` through `PowerSeries.algebraPolynomial` as multiplication
by the power series `X`. -/
@[simp]
theorem polynomial_X_smul (f : A⟦X⟧) : (Polynomial.X : Polynomial R) • f = X * f := by
  simpa using polynomial_X_pow_smul (R := R) 1 f

/-- The monomial `a Xʲ` acts on `A⟦X⟧` through `PowerSeries.algebraPolynomial` as the scalar `a`
times multiplication by the power series `Xʲ`. -/
@[simp]
theorem polynomial_monomial_smul (j : ℕ) (a : R) (f : A⟦X⟧) :
    (Polynomial.monomial j a : Polynomial R) • f = a • (X ^ j * f) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_smul, polynomial_X_pow_smul, polynomial_C_smul]

/-- Along a scalar tower `R → S → A`, a polynomial over `R` acts on `A⟦X⟧` as its image in
`S[X]` does. -/
theorem polynomial_map_algebraMap_smul {S : Type*} [CommSemiring S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] (q : Polynomial R) (f : A⟦X⟧) :
    q.map (algebraMap R S) • f = q • f := by
  rw [Algebra.smul_def, Algebra.smul_def, algebraMap_apply', algebraMap_apply',
    ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq]

end Algebra

section AlgebraCommRing

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- If a submodule `S` over `R[X]` is stable under `p • d⁄dX` and contains `r • x`, then it
contains `(p * r ^ 2) • x'`. This is the induction step showing that nonzero multiples of all
derivatives of a series lie in a fixed submodule. -/
theorem smul_derivative_mem {S : Submodule (Polynomial R) A⟦X⟧} {p : Polynomial R}
    (hS : ∀ y ∈ S, p • d⁄dX y ∈ S) {r : Polynomial R} {x : A⟦X⟧} (hx : r • x ∈ S) :
    (p * r ^ 2) • d⁄dX x ∈ S := by
  have key : (p * r ^ 2) • d⁄dX x =
      r • (p • d⁄dX (r • x)) - (p * Polynomial.derivative r) • (r • x) := by
    rw [derivative_polynomial_smul]
    module
  rw [key]
  exact S.sub_mem (S.smul_mem _ (hS _ hx)) (S.smul_mem _ hx)

end AlgebraCommRing

/-- In prime characteristic, a series with zero derivative has no coefficients outside the
multiples of the characteristic. -/
theorem coeff_eq_zero_of_derivative_eq_zero {R : Type*} [CommRing R] {p : ℕ}
    [Fact p.Prime] [CharP R p] {f : PowerSeries R}
    (hf : derivative f = 0) {n : ℕ} (hn : ¬ p ∣ n) : coeff n f = 0 := by
  have hn0 : n ≠ 0 := fun h ↦ hn (h ▸ dvd_zero p)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn0
  have h := congrArg (coeff m) hf
  simp only [coeff_derivative, map_zero] at h
  exact (CharP.isUnit_natCast_iff (R := R) (Fact.out : p.Prime)).mpr hn |>.mul_right_eq_zero.mp
    (by simpa [Nat.cast_add, Nat.cast_one, mul_comm] using h)

end PowerSeries

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic

import Mathlib.Algebra.MvPolynomial.Coeff

/-!
# Polynomial products as power series

`MvPolynomial.coe_finsuppProd_pow` moves a finitely supported product of polynomial powers
through the coercion to multivariate power series. It lets coefficient computations for such
products use the polynomial API, for example when substituting polynomials into power series.
The coefficient semiring need only be commutative; no norm or topology is required.

`MvPowerSeries.isScalarTower_right` records that coefficientwise left scalar multiplication on
`MvPowerSeries σ A` forms a scalar tower with power-series multiplication, `MvPowerSeries.X_ne_zero`
records that every coordinate variable `X s` is nonzero over a nontrivial semiring,
`MvPowerSeries.coeff_X_add_X_pow` is the binomial formula for the coefficients of `(X + Y) ^ n` in
`R⟦X, Y⟧` (the power-series counterpart of `MvPolynomial.coeff_add_pow`, over any semiring), and
`MvPowerSeries.mem_support` together with `support_zero`, `support_add`, `support_smul_subset`,
`support_neg`, and `support_sub` bridges `Function.support` with `MvPowerSeries.coeff` and the
algebraic operations on `MvPowerSeries`.
-/

public section

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-- The coercion of polynomials to power series commutes with products of powers. -/
@[simp, norm_cast]
theorem coe_finsuppProd_pow (a : σ → MvPolynomial τ R) (d : σ →₀ ℕ) :
    ((d.prod fun s n ↦ a s ^ n : MvPolynomial τ R) : MvPowerSeries τ R) =
      d.prod fun s n ↦ (a s : MvPowerSeries τ R) ^ n := by
  simpa only [map_pow, coeToMvPowerSeries.ringHom_apply] using
    map_finsuppProd (coeToMvPowerSeries.ringHom (σ := τ) (R := R)) d (fun s n ↦ a s ^ n)

end MvPolynomial

namespace MvPowerSeries

variable {R : Type*} [Semiring R]

/-- Left scalar multiplication by `R` on `MvPowerSeries σ A` forms a scalar tower with
multiplication in `MvPowerSeries σ A`. -/
instance isScalarTower_right {σ A : Type*} [Semiring A] [Module R A] [IsScalarTower R A A] :
    IsScalarTower R (MvPowerSeries σ A) (MvPowerSeries σ A) where
  smul_assoc r f g := by
    classical
    ext n
    simp [(coeff _).map_smul_of_tower r, coeff_mul, Finset.smul_sum, smul_mul_assoc]

/-- Over a nontrivial semiring, every coordinate indeterminate `X s` is nonzero. -/
@[simp]
theorem X_ne_zero {σ : Type*} [Nontrivial R] (s : σ) : (X s : MvPowerSeries σ R) ≠ 0 := fun h ↦ by
  classical
  have h1 := congrArg (coeff (Finsupp.single s 1)) h
  rw [coeff_X, ite_eq_left rfl, map_zero] at h1
  exact one_ne_zero h1

/-- The coefficient of `X^(d 0) Y^(d 1)` in `(X + Y) ^ n` is `n.choose (d 0)` if
`d 0 + d 1 = n`, and `0` otherwise. -/
theorem coeff_X_add_X_pow (d : Fin 2 →₀ ℕ) (n : ℕ) :
    coeff d ((X 0 + X 1 : MvPowerSeries (Fin 2) R) ^ n) =
      if d 0 + d 1 = n then (n.choose (d 0) : R) else 0 := by
  -- Over `ℕ` this is `MvPolynomial.coeff_add_pow`; it maps to any semiring.
  have hnat : coeff d ((X 0 + X 1 : MvPowerSeries (Fin 2) ℕ) ^ n) =
      if d 0 + d 1 = n then n.choose (d 0) else 0 := by
    simpa [← MvPolynomial.coeff_coe] using MvPolynomial.coeff_add_pow (R := ℕ) d n
  simpa only [← coeff_map, map_pow, map_add, map_X, Nat.coe_castRingHom, apply_ite,
    Nat.cast_zero] using congrArg (Nat.castRingHom R) hnat

/-- An exponent `α` belongs to `f.support` if and only if `coeff α f ≠ 0`. -/
theorem mem_support {σ : Type*} {f : MvPowerSeries σ R} {α : σ →₀ ℕ} :
    α ∈ f.support ↔ coeff α f ≠ 0 := by
  simp only [coeff_apply]
  exact Function.mem_support

/-- The zero power series has empty support. -/
@[simp]
theorem support_zero {σ : Type*} : (0 : MvPowerSeries σ R).support = ∅ := by
  ext α
  simp [mem_support]

/-- The support of a sum of power series is contained in the union of their supports. -/
theorem support_add {σ : Type*} (f g : MvPowerSeries σ R) :
    (f + g).support ⊆ f.support ∪ g.support := by
  intro α hα
  simpa only [Set.mem_union, Function.mem_support, ← mem_support] using
    Function.support_add (coeff · f) (coeff · g)
      (by rwa [Function.mem_support, ← map_add, ← mem_support])

/-- Scalar multiplication shrinks the support of a power series. -/
theorem support_smul_subset {σ : Type*} (c : R) (f : MvPowerSeries σ R) :
    (c • f).support ⊆ f.support := by
  intro α hα
  rw [mem_support]
  exact Function.support_const_smul_subset c (coeff · f)
    (by rwa [Function.mem_support, Pi.smul_apply, ← map_smul, ← mem_support])

/-- Negation preserves the support of a power series. -/
@[simp]
theorem support_neg {σ S : Type*} [Ring S] (f : MvPowerSeries σ S) :
    (-f).support = f.support := by
  ext α
  simp [mem_support]

/-- The support of a difference of power series is contained in the union of their supports. -/
theorem support_sub {σ S : Type*} [Ring S] (f g : MvPowerSeries σ S) :
    (f - g).support ⊆ f.support ∪ g.support := by
  intro α hα
  simpa only [Set.mem_union, Function.mem_support, ← mem_support] using
    Function.support_sub (coeff · f) (coeff · g)
      (by rwa [Function.mem_support, ← map_sub, ← mem_support])

end MvPowerSeries

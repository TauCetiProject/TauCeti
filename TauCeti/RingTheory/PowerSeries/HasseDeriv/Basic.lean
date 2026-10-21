/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Hasse derivatives of power series

The `k`th Hasse derivative of a power series `f = ∑ aₙ Xⁿ` is

```text
D⁽ᵏ⁾ f = ∑ₙ (n + k).choose k • aₙ₊ₖ Xⁿ.
```

It is defined coefficientwise over any semiring. Only natural-number multiples of coefficients
occur, so the coefficients need not commute; this allows Hasse derivatives of series with
coefficients in a noncommutative algebra, such as an algebra of operators. Over a commutative
semiring, `k! • D⁽ᵏ⁾ = (d/dX)^[k]`. Unlike `(d/dX)^[k] / k!`, the Hasse derivative needs no division
by `k!`, so it keeps its meaning in positive characteristic.

The definitions and lemmas parallel Mathlib's `Polynomial.hasseDeriv`, and on polynomials the two
agree (`PowerSeries.hasseDeriv_coe`). Since a coefficient of a Hasse derivative of `f` only sees
finitely many coefficients of `f` (`PowerSeries.trunc_hasseDeriv`), the Leibniz rule is deduced
from Mathlib's polynomial Leibniz rule `Polynomial.hasseDeriv_mul`.

## Main definitions

* `PowerSeries.hasseDeriv`: the `k`th Hasse derivative, an `R`-linear map `R⟦X⟧ → R⟦X⟧`.

## Main results

* `PowerSeries.coeff_hasseDeriv`: `coeff n (D⁽ᵏ⁾ f) = (n + k).choose k * coeff (n + k) f`.
* `PowerSeries.hasseDeriv_coe` and `PowerSeries.trunc_hasseDeriv`: comparison with
  `Polynomial.hasseDeriv` on polynomials and on truncations.
* `PowerSeries.hasseDeriv_map`: Hasse derivatives commute with coefficient maps.
* `PowerSeries.hasseDeriv_comp`: `D⁽ᵏ⁾ ∘ D⁽ˡ⁾ = (k + l).choose k • D⁽ᵏ⁺ˡ⁾`.
* `PowerSeries.hasseDeriv_mul`: the Leibniz rule
  `D⁽ᵏ⁾ (f * g) = ∑_{i + j = k} D⁽ⁱ⁾ f * D⁽ʲ⁾ g`, with the factors in their original order.
* `PowerSeries.hasseDeriv_one_apply` and `PowerSeries.factorial_smul_hasseDeriv`: over a
  commutative semiring, `D⁽¹⁾ = d/dX` and `k! • D⁽ᵏ⁾ = (d/dX)^[k]`.

## References

* H. Hasse, *Theorie der höheren Differentiale in einem algebraischen Funktionenkörper mit
  vollkommenem Konstantenkörper bei beliebiger Charakteristik*, J. Reine Angew. Math. 175 (1936).
-/

public section

noncomputable section

namespace PowerSeries

open Finset (antidiagonal mem_antidiagonal)
open Nat
open scoped Polynomial

section Semiring

variable {R : Type*} [Semiring R] (k : ℕ)

/-- The `k`th Hasse derivative of a power series `∑ aₙ Xⁿ` is `∑ (n + k).choose k • aₙ₊ₖ Xⁿ`.
Over a commutative semiring, `k! • hasseDeriv k f` is the `k`th iterated derivative of `f`
(`PowerSeries.factorial_smul_hasseDeriv`). -/
def hasseDeriv : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun f := mk fun n ↦ ((n + k).choose k : R) * coeff (n + k) f
  map_add' f g := by
    ext n
    simp [mul_add]
  map_smul' a f := by
    ext n
    simp only [coeff_mk, coeff_smul, smul_eq_mul, RingHom.id_apply, ← mul_assoc,
      (Nat.cast_commute _ a).eq]

/-- The coefficients of a Hasse derivative:
`coeff n (D⁽ᵏ⁾ f) = (n + k).choose k * coeff (n + k) f`. -/
@[simp]
theorem coeff_hasseDeriv (f : R⟦X⟧) (n : ℕ) :
    coeff n (hasseDeriv k f) = ((n + k).choose k : R) * coeff (n + k) f := by
  simp [hasseDeriv]

/-- The `0`th Hasse derivative is the identity. -/
@[simp]
theorem hasseDeriv_zero : hasseDeriv 0 = (LinearMap.id : R⟦X⟧ →ₗ[R] R⟦X⟧) := by
  ext f n
  simp

/-- On polynomials, the Hasse derivative of power series is `Polynomial.hasseDeriv`. -/
@[simp]
theorem hasseDeriv_coe (p : R[X]) : hasseDeriv k (p : R⟦X⟧) = (p.hasseDeriv k : R⟦X⟧) := by
  ext n
  simp [Polynomial.hasseDeriv_coeff]

/-- The coefficients of `D⁽ᵏ⁾ f` below `n` only depend on the coefficients of `f` below `n + k`. -/
theorem trunc_hasseDeriv (f : R⟦X⟧) (n : ℕ) :
    trunc n (hasseDeriv k f) = (trunc (n + k) f).hasseDeriv k := by
  ext m
  simp only [coeff_trunc, Polynomial.hasseDeriv_coeff, coeff_hasseDeriv]
  split_ifs with h₁ h₂ h₂
  · rfl
  · omega
  · omega
  · rw [mul_zero]

/-- The Hasse derivative of a monomial: `D⁽ᵏ⁾ (a Xⁿ) = n.choose k * a Xⁿ⁻ᵏ`. -/
@[simp]
theorem hasseDeriv_monomial (n : ℕ) (a : R) :
    hasseDeriv k (monomial n a) = monomial (n - k) ((n.choose k : R) * a) := by
  rw [← Polynomial.coe_monomial, hasseDeriv_coe, Polynomial.hasseDeriv_monomial,
    Polynomial.coe_monomial]

/-- Positive Hasse derivatives vanish on constants. -/
theorem hasseDeriv_C {k : ℕ} (hk : 0 < k) (a : R) : hasseDeriv k (C a) = 0 := by
  rw [← monomial_zero_eq_C_apply, hasseDeriv_monomial, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero,
    zero_mul, map_zero]

/-- Hasse derivatives commute with coefficient maps. -/
@[simp]
theorem hasseDeriv_map {S : Type*} [Semiring S] (φ : R →+* S) (f : R⟦X⟧) :
    hasseDeriv k (map φ f) = map φ (hasseDeriv k f) := by
  ext n
  simp

/-- The composition of Hasse derivatives: `D⁽ᵏ⁾ ∘ D⁽ˡ⁾ = (k + l).choose k • D⁽ᵏ⁺ˡ⁾`. -/
theorem hasseDeriv_comp (l : ℕ) :
    (hasseDeriv k).comp (hasseDeriv l) =
      (k + l).choose k • (hasseDeriv (k + l) : R⟦X⟧ →ₗ[R] R⟦X⟧) := by
  ext f n
  -- both sides are multiples of `coeff (n + k + l) f`, by the multinomial coefficient
  -- `(n + k + l)! / (n! k! l!)`, computed in two ways by `Nat.choose_mul`
  have key : (n + k).choose k * (n + (k + l)).choose l =
      (k + l).choose k * (n + (k + l)).choose (k + l) := by
    have h := Nat.choose_mul (n := n + k + l) (k := k + l) (s := l) (by omega)
    rw [show n + k + l - l = n + k by omega, show k + l - l = k by omega] at h
    rw [← add_assoc, Nat.choose_symm_add]
    linarith
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_nsmul, coeff_hasseDeriv, add_assoc]
  simp only [nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, key]

/-- The **Leibniz rule** for Hasse derivatives:
`D⁽ᵏ⁾ (f * g) = ∑_{i + j = k} D⁽ⁱ⁾ f * D⁽ʲ⁾ g`. The coefficients need not commute. -/
theorem hasseDeriv_mul (f g : R⟦X⟧) :
    hasseDeriv k (f * g) = ∑ ij ∈ antidiagonal k, hasseDeriv ij.1 f * hasseDeriv ij.2 g := by
  ext n
  -- Both sides only see the coefficients of `f` and `g` below `N`, so we may replace them by
  -- their truncations and apply the polynomial Leibniz rule.
  set N := n + k + 1
  have htrunc (h : R⟦X⟧) {m : ℕ} (hm : m < N) : coeff m (trunc N h : R⟦X⟧) = coeff m h := by
    simp [coeff_trunc, hm]
  have hcoeff (i : ℕ) (hi : i ≤ k) (h : R⟦X⟧) {m : ℕ} (hm : m ≤ n) :
      coeff m (hasseDeriv i h) = coeff m (hasseDeriv i (trunc N h : R⟦X⟧)) := by
    rw [coeff_hasseDeriv, coeff_hasseDeriv, htrunc h (by omega)]
  have hsum (ij : ℕ × ℕ) (hij : ij ∈ antidiagonal k) :
      coeff n (hasseDeriv ij.1 f * hasseDeriv ij.2 g) =
        coeff n (hasseDeriv ij.1 (trunc N f : R⟦X⟧) * hasseDeriv ij.2 (trunc N g : R⟦X⟧)) := by
    rw [mem_antidiagonal] at hij
    simp only [coeff_mul]
    refine Finset.sum_congr rfl fun ab hab ↦ ?_
    rw [mem_antidiagonal] at hab
    rw [hcoeff ij.1 (by omega) f (by omega), hcoeff ij.2 (by omega) g (by omega)]
  have hpoly : ∑ ij ∈ antidiagonal k,
      hasseDeriv ij.1 (trunc N f : R⟦X⟧) * hasseDeriv ij.2 (trunc N g : R⟦X⟧) =
        hasseDeriv k ((trunc N f * trunc N g : R[X]) : R⟦X⟧) := by
    rw [hasseDeriv_coe, Polynomial.hasseDeriv_mul]
    simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, map_mul]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, hasseDeriv_coe]
  rw [map_sum, Finset.sum_congr rfl hsum, ← map_sum, hpoly, coeff_hasseDeriv, coeff_hasseDeriv,
    Polynomial.coe_mul, coeff_mul, coeff_mul]
  congr 1
  refine Finset.sum_congr rfl fun ab hab ↦ ?_
  rw [mem_antidiagonal] at hab
  rw [htrunc f (by omega), htrunc g (by omega)]

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The first Hasse derivative is the derivative. -/
@[simp]
theorem hasseDeriv_one_apply (f : R⟦X⟧) : hasseDeriv 1 f = d⁄dX f := by
  ext n
  simp [coeff_derivative, mul_comm]

/-- `k!` times the `k`th Hasse derivative is the `k`th iterated derivative:
`k! • D⁽ᵏ⁾ f = (d/dX)^[k] f`. -/
theorem factorial_smul_hasseDeriv (k : ℕ) (f : R⟦X⟧) :
    k ! • hasseDeriv k f = d⁄dX^[k] f := by
  ext n
  simp [coeff_iterate_derivative, Nat.ascFactorial_eq_factorial_mul_choose, nsmul_eq_mul, mul_assoc]

end CommSemiring

end PowerSeries

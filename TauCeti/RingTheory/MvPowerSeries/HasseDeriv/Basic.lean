/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import TauCeti.Algebra.MvPolynomial.HasseDeriv.Basic

/-!
# Hasse derivatives of multivariate power series

For a multi-index `d : σ →₀ ℕ`, the `d`-th Hasse (divided) partial derivative of a multivariate
power series `f = ∑ₘ aₘ Xᵐ` is

```text
∂^d f = ∑ₘ (∏ⱼ (mⱼ + dⱼ choose dⱼ)) • aₘ₊d Xᵐ.
```

It is defined coefficientwise over any semiring. Only natural-number multiples of coefficients
occur, so the coefficients need not commute. Over a commutative semiring, `∂^(eᵢ)` is the partial
derivative `∂/∂Xᵢ` and `k! • ∂^(k eᵢ) = (∂/∂Xᵢ)^[k]`; since no division by `k!` is needed, Hasse
derivatives keep their meaning in positive characteristic, where `(∂/∂Xᵢ)^[k] / k!` does not.

The definitions and lemmas parallel `MvPolynomial.hasseDeriv`, with which `MvPowerSeries.hasseDeriv`
agrees on polynomials (`MvPowerSeries.hasseDeriv_coe`), and the one-variable
`PowerSeries.hasseDeriv`.

## Main definitions

* `MvPowerSeries.hasseDeriv d`: the `d`-th Hasse derivative, an `R`-linear endomorphism of
  `MvPowerSeries σ R`.

## Main results

* `MvPowerSeries.coeff_hasseDeriv`: `[Xᵐ] ∂^d f = (∏ⱼ (mⱼ + dⱼ choose dⱼ)) [Xᵐ⁺ᵈ] f`.
* `MvPowerSeries.hasseDeriv_zero`, `MvPowerSeries.hasseDeriv_C`, `MvPowerSeries.hasseDeriv_one`:
  `∂^0` is the identity and every other Hasse derivative kills constants.
* `MvPowerSeries.hasseDeriv_map`: Hasse derivatives commute with coefficient ring maps.
* `MvPowerSeries.hasseDeriv_comp`: `∂^a ∘ ∂^b = (∏ⱼ (aⱼ + bⱼ choose aⱼ)) • ∂^(a + b)`.
* `MvPowerSeries.hasseDeriv_coe`, `MvPowerSeries.hasseDeriv_monomial`: the comparison with
  `MvPolynomial.hasseDeriv` on polynomials, and the values on monomials.
* `MvPowerSeries.hasseDeriv_single_one`: `∂^(eᵢ)` is the partial derivative `pderiv i`.
* `MvPowerSeries.factorial_smul_hasseDeriv_single`: `k! • ∂^(k eᵢ) f = (∂/∂Xᵢ)^[k] f`.

## References

* H. Hasse, *Theorie der höheren Differentiale in einem algebraischen Funktionenkörper mit
  vollkommenem Konstantenkörper bei beliebiger Charakteristik*, J. Reine Angew. Math. 175 (1936).
-/

public section

noncomputable section

namespace MvPowerSeries

open Finsupp

section Semiring

variable {σ R : Type*} [Semiring R]

/-- The `d`-th Hasse derivative `∂^d` of a multivariate power series `∑ₘ aₘ Xᵐ` is
`∑ₘ (∏ⱼ (mⱼ + dⱼ choose dⱼ)) • aₘ₊d Xᵐ`. Over a commutative semiring, `k! • hasseDeriv (single i k)`
is the `k`-th iterated partial derivative in `Xᵢ`
(`MvPowerSeries.factorial_smul_hasseDeriv_single`). -/
def hasseDeriv (d : σ →₀ ℕ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R where
  toFun f m := ((d.prod fun j k ↦ (m j + k).choose k : ℕ) : R) * coeff (m + d) f
  -- After rewriting the coefficients of `f`, both sides agree coefficientwise by definition.
  map_add' f g := by
    ext m
    simp only [coeff_apply, map_add, mul_add]
    rfl
  map_smul' a f := by
    ext m
    simp only [coeff_apply, map_smul, smul_eq_mul, RingHom.id_apply, ← mul_assoc,
      (Nat.cast_commute _ a).eq]
    simp only [mul_assoc]
    -- As in `map_add'`, the remaining goal holds coefficientwise by definition: the scalar action
    -- on `MvPowerSeries σ R` is the pointwise action on coefficient functions.
    rfl

/-- The coefficients of a Hasse derivative:
`[Xᵐ] ∂^d f = (∏ⱼ (mⱼ + dⱼ choose dⱼ)) [Xᵐ⁺ᵈ] f`. -/
@[simp]
theorem coeff_hasseDeriv (d m : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    coeff m (hasseDeriv d f) =
      ((d.prod fun j k ↦ (m j + k).choose k : ℕ) : R) * coeff (m + d) f :=
  (rfl)

/-- The `0`-th Hasse derivative is the identity. -/
@[simp]
theorem hasseDeriv_zero :
    hasseDeriv 0 = (LinearMap.id : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R) := by
  ext f m
  simp

/-- Hasse derivatives of positive order vanish on constants. -/
@[simp]
theorem hasseDeriv_C {d : σ →₀ ℕ} (hd : d ≠ 0) (a : R) : hasseDeriv d (C a) = 0 := by
  classical
  ext m
  rw [coeff_hasseDeriv, coeff_C, ite_eq_right_iff.mpr fun h ↦ absurd (add_eq_zero.mp h).2 hd,
    mul_zero, map_zero]

/-- Hasse derivatives of positive order vanish on `1`. -/
@[simp]
theorem hasseDeriv_one {d : σ →₀ ℕ} (hd : d ≠ 0) : hasseDeriv d (1 : MvPowerSeries σ R) = 0 := by
  simpa only [map_one] using hasseDeriv_C (R := R) hd 1

/-- Hasse derivatives commute with coefficient maps. -/
@[simp]
theorem hasseDeriv_map {S : Type*} [Semiring S] (φ : R →+* S) (d : σ →₀ ℕ)
    (f : MvPowerSeries σ R) : hasseDeriv d (map φ f) = map φ (hasseDeriv d f) := by
  ext m
  simp

/-- The composition rule `∂^a ∘ ∂^b = (∏ⱼ (aⱼ + bⱼ choose aⱼ)) • ∂^(a + b)`. -/
theorem hasseDeriv_comp (a b : σ →₀ ℕ) :
    (hasseDeriv a).comp (hasseDeriv b) =
      (a.prod fun j k ↦ (k + b j).choose k) •
        (hasseDeriv (a + b) : MvPowerSeries σ R →ₗ[R] _) := by
  ext f m
  -- Both sides are multiples of `[Xᵐ⁺ᵃ⁺ᵇ] f`. The two multi-index coefficients agree by the
  -- composition rule for polynomials, read off at the monomial `Xᵐ⁺ᵃ⁺ᵇ` with coefficients in `ℕ`.
  have key : (a.prod fun j k ↦ (m j + k).choose k) * (b.prod fun j k ↦ ((m + a) j + k).choose k) =
      (a.prod fun j k ↦ (k + b j).choose k) * ((a + b).prod fun j k ↦ (m j + k).choose k) := by
    classical
    have h := congrArg (fun P : MvPolynomial σ ℕ ↦ P.coeff m) <|
      LinearMap.congr_fun (MvPolynomial.hasseDeriv_comp (R := ℕ) (σ := σ) a b)
        (MvPolynomial.monomial (m + a + b) 1)
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, MvPolynomial.hasseDeriv_coeff,
      MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, add_assoc, ↓reduceIte, mul_one,
      Nat.cast_id, smul_eq_mul, ← mul_assoc] using h
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_nsmul, coeff_hasseDeriv, add_assoc]
  simp only [nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, key]

end Semiring

section CommSemiring

variable {σ R : Type*} [CommSemiring R]

/-- On polynomials, the Hasse derivative of power series is `MvPolynomial.hasseDeriv`. -/
@[simp]
theorem hasseDeriv_coe (d : σ →₀ ℕ) (P : MvPolynomial σ R) :
    hasseDeriv d (P : MvPowerSeries σ R) = (MvPolynomial.hasseDeriv d P : MvPowerSeries σ R) := by
  ext m
  simp [MvPolynomial.coeff_coe]

/-- The Hasse derivative of a monomial: `∂^d (a Xᵐ) = (∏ⱼ (mⱼ choose dⱼ)) a Xᵐ⁻ᵈ`. The
coefficient vanishes unless `d ≤ m`. -/
@[simp]
theorem hasseDeriv_monomial (d m : σ →₀ ℕ) (a : R) :
    hasseDeriv d (monomial m a) =
      monomial (m - d) (((d.prod fun j k ↦ (m j).choose k : ℕ) : R) * a) := by
  rw [← MvPolynomial.coe_monomial, hasseDeriv_coe, MvPolynomial.hasseDeriv_monomial,
    MvPolynomial.coe_monomial]

/-- The first Hasse derivative in the variable `Xᵢ` is the partial derivative `∂/∂Xᵢ`. -/
@[simp]
theorem hasseDeriv_single_one (i : σ) (f : MvPowerSeries σ R) :
    hasseDeriv (single i 1) f = pderiv i f := by
  ext m
  simp [coeff_pderiv, mul_comm]

/-- Differentiating `∂^(k eᵢ)` with respect to `Xᵢ` gives `(k + 1) • ∂^((k + 1) eᵢ)`. -/
@[simp]
theorem pderiv_hasseDeriv_single (i : σ) (k : ℕ) (f : MvPowerSeries σ R) :
    pderiv i (hasseDeriv (single i k) f) = (k + 1) • hasseDeriv (single i (k + 1)) f := by
  rw [← hasseDeriv_single_one, ← LinearMap.comp_apply, hasseDeriv_comp, ← single_add,
    add_comm 1 k, LinearMap.smul_apply, prod_single_index (by simp)]
  simp [add_comm 1 k]

/-- The Hasse derivative `∂^(k eᵢ)` is the `k`-th partial derivative in `Xᵢ` divided by `k!`:
`k! • ∂^(k eᵢ) f = (∂/∂Xᵢ)^[k] f`. -/
theorem factorial_smul_hasseDeriv_single (i : σ) (k : ℕ) (f : MvPowerSeries σ R) :
    k.factorial • hasseDeriv (single i k) f = (pderiv i)^[k] f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih, map_nsmul, pderiv_hasseDeriv_single, smul_smul,
      Nat.factorial_succ, mul_comm]

end CommSemiring

end MvPowerSeries

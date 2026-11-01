/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# The derivative of Laurent polynomials

Over a ring `R`, the formal derivative `d/dT` of Laurent polynomials sends `a Tⁿ` to `n a Tⁿ⁻¹`
for every integer `n`, so the coefficient of `Tⁿ` in `f'` is `n + 1` times the coefficient of
`Tⁿ⁺¹` in `f`. It satisfies the product rule, extends `Polynomial.derivative` along
`Polynomial.toLaurent`, and kills the constants; without additive torsion its kernel is exactly
the constants. For commutative `R` it is bundled as a derivation `LaurentPolynomial.derivative'`,
following `Polynomial.derivative'`.

The residue of the form `f dT` is the coefficient of `T⁻¹` in `f`. Since `n Tⁿ⁻¹` has residue zero
for every `n`, every derivative has residue zero, and the product rule gives integration by parts
`Res(f dg) = -Res((df) g)`. These are the Laurent-polynomial counterparts of the derivative and
residue of Laurent series: the embedding of Laurent polynomials into Laurent series commutes with
the derivatives (`LaurentPolynomial.toLaurentSeries_derivative`) and carries the residue
`Res(f dg)` of Laurent polynomials to the Laurent-series residue pairing
(`LaurentSeries.residuePairing_toLaurentSeries`).

## Main definitions

* `LaurentPolynomial.derivative`: the formal derivative of Laurent polynomials.
* `LaurentPolynomial.derivative'`: the formal derivative as a derivation, for commutative `R`.

## Main results

* `LaurentPolynomial.derivative_C_mul_T`: the derivative of `a Tⁿ` is `n a Tⁿ⁻¹`.
* `LaurentPolynomial.coeff_derivative`: the coefficient formula for the derivative.
* `LaurentPolynomial.derivative_mul`: the product rule.
* `LaurentPolynomial.derivative_toLaurent`: compatibility with `Polynomial.derivative`.
* `LaurentPolynomial.derivative_eq_zero_iff_exists_C`: without additive torsion, the kernel of the
  derivative consists of the constants.
* `LaurentPolynomial.coeff_neg_one_derivative`: a derivative has residue zero.
* `LaurentPolynomial.coeff_neg_one_mul_derivative`: integration by parts for residues.
-/

public section

open Polynomial (toLaurent)
open scoped Polynomial
open scoped LaurentPolynomial

namespace LaurentPolynomial

section Ring

variable {R : Type*} [Ring R]

/-- The **formal derivative** `d/dT` of Laurent polynomials, sending `a Tⁿ` to `n a Tⁿ⁻¹` for every
integer `n`. -/
noncomputable def derivative : R[T;T⁻¹] →ₗ[R] R[T;T⁻¹] :=
  (Finsupp.lsum ℕ fun n : ℤ ↦ n • AddMonoidAlgebra.lsingle (R := R) (n - 1)).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- The derivative of the monomial `a Tⁿ`, written with `AddMonoidAlgebra.single`. The `simp`
normal form of a Laurent monomial is `C a * T n`, handled by
`LaurentPolynomial.derivative_C_mul_T`. -/
theorem derivative_single (n : ℤ) (a : R) :
    derivative (.single n a : R[T;T⁻¹]) = .single (n - 1) (a * n) := by
  rw [derivative, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, AddMonoidAlgebra.coeffLinearEquiv_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.lsum_single, LinearMap.smul_apply,
    AddMonoidAlgebra.lsingle_apply]
  rw [AddMonoidAlgebra.smul_single, zsmul_eq_mul']

/-- The derivative of `a Tⁿ` is `n a Tⁿ⁻¹`, for every integer `n`. -/
@[simp]
theorem derivative_C_mul_T (a : R) (n : ℤ) :
    derivative (C a * T n) = C (a * n) * T (n - 1) := by
  rw [← single_eq_C_mul_T, ← single_eq_C_mul_T, derivative_single]

/-- The derivative of `Tⁿ` is `n Tⁿ⁻¹`, for every integer `n`. -/
@[simp]
theorem derivative_T (n : ℤ) : derivative (T n : R[T;T⁻¹]) = (n : R[T;T⁻¹]) * T (n - 1) := by
  simpa using derivative_C_mul_T (1 : R) n

/-- The derivative of a constant is zero. -/
@[simp]
theorem derivative_C (a : R) : derivative (C a : R[T;T⁻¹]) = 0 := by
  simpa using derivative_C_mul_T a 0

/-- The derivative of `1` is zero. -/
@[simp]
theorem derivative_one : derivative (1 : R[T;T⁻¹]) = 0 := by
  simpa using derivative_C (1 : R)

/-- The coefficient of `Tⁿ` in `f'` is `n + 1` times the coefficient of `Tⁿ⁺¹` in `f`. -/
@[simp]
theorem coeff_derivative (f : R[T;T⁻¹]) (n : ℤ) :
    (derivative f).coeff n = f.coeff (n + 1) * (n + 1) := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simp [hf, hg, add_mul]
  | C_mul_T m a =>
    rw [derivative_C_mul_T, ← single_eq_C_mul_T, ← single_eq_C_mul_T]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, sub_eq_iff_eq_add]
    split_ifs with h
    · rw [h, Int.cast_add, Int.cast_one]
    · rw [zero_mul]

/-- The coefficient of `Tⁿ⁻¹` in `f'` is `n` times the coefficient of `Tⁿ` in `f`. -/
theorem coeff_derivative_sub_one (f : R[T;T⁻¹]) (n : ℤ) :
    (derivative f).coeff (n - 1) = f.coeff n * n := by
  simp

/-- **A derivative has residue zero**: the coefficient of `T⁻¹` in `f'` vanishes. -/
theorem coeff_neg_one_derivative (f : R[T;T⁻¹]) : (derivative f).coeff (-1) = 0 := by
  simp

/-- **The product rule** for the derivative of Laurent polynomials. -/
theorem derivative_mul (f g : R[T;T⁻¹]) :
    derivative (f * g) = derivative f * g + f * derivative g := by
  induction f using LaurentPolynomial.induction_on' with
  | add f₁ f₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]; abel
  | C_mul_T m a =>
    induction g using LaurentPolynomial.induction_on' with
    | add g₁ g₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]; abel
    | C_mul_T n b =>
      simp only [← single_eq_C_mul_T, AddMonoidAlgebra.single_mul_single, derivative_single]
      -- Both terms of the right side are monomials of degree `m + n - 1`.
      rw [show m - 1 + n = m + n - 1 by abel, show m + (n - 1) = m + n - 1 by abel,
        ← AddMonoidAlgebra.single_add]
      -- Their coefficients add up to `a * b * (m + n)`, moving the integer cast `m` past `b`.
      congr 1
      simp only [Int.cast_add, mul_add, mul_assoc, (Int.cast_commute m b).eq]

/-- The derivative of Laurent polynomials extends the derivative of polynomials along
`Polynomial.toLaurent`. -/
@[simp]
theorem derivative_toLaurent (p : R[X]) :
    derivative (toLaurent p) = toLaurent (Polynomial.derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    -- The exponent `n - 1` is truncated subtraction in `ℕ`, so `n = 0` is treated separately.
    rcases n with _ | n <;> simp

/-- **The kernel of the derivative.** Without additive torsion in `R`, a Laurent
polynomial has derivative zero exactly when it is a constant. -/
theorem derivative_eq_zero_iff_exists_C [IsAddTorsionFree R] {f : R[T;T⁻¹]} :
    derivative f = 0 ↔ ∃ c : R, C c = f := by
  refine ⟨fun h ↦ ⟨f.coeff 0, LaurentPolynomial.ext fun n ↦ ?_⟩, ?_⟩
  · rw [C_apply]
    split_ifs with hn
    · rw [hn]
    · have hc : n • f.coeff n = 0 := by
        rw [zsmul_eq_mul', ← coeff_derivative_sub_one, h]
        simp
      exact ((IsAddTorsionFree.zsmul_eq_zero_iff_right hn).mp hc).symm
  · rintro ⟨c, rfl⟩
    exact derivative_C c

/-- **Integration by parts** for residues of Laurent polynomials: `Res(f dg) = -Res((df) g)`,
where the residue is the coefficient of `T⁻¹`. The factor order is kept, since `R` need not be
commutative. -/
theorem coeff_neg_one_mul_derivative (f g : R[T;T⁻¹]) :
    (f * derivative g).coeff (-1) = -(derivative f * g).coeff (-1) := by
  have h := coeff_neg_one_derivative (f * g)
  rw [derivative_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at h
  exact eq_neg_of_add_eq_zero_right h

end Ring

section CommRing

variable (R : Type*) [CommRing R]

/-- The formal derivative of Laurent polynomials over a commutative ring, as a derivation. -/
noncomputable def derivative' : Derivation R R[T;T⁻¹] R[T;T⁻¹] where
  __ := derivative
  map_one_eq_zero' := derivative_one
  leibniz' f g := by
    rw [derivative_mul, smul_eq_mul, smul_eq_mul, mul_comm (derivative f), add_comm]

variable {R}

/-- The derivation `LaurentPolynomial.derivative' R` evaluates as the formal derivative. -/
@[simp]
theorem derivative'_apply (f : R[T;T⁻¹]) : derivative' R f = derivative f := (rfl)

end CommRing

end LaurentPolynomial

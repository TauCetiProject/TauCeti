/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import TauCeti.NumberTheory.ModularForms.LevelOne.ModularPolynomial.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import TauCeti.NumberTheory.ModularForms.LevelOne.SingularModuli

/-!
# The diagonal modular polynomial

Along the diagonal `Y = X`, the modular polynomial `modularPolynomial n` specializes to
`diagModularPolynomial n = Φ_n(X, X) ∈ ℤ[X]`, whose evaluation at `j(τ)` is
`∏ (j(τ) - j(A • τ))` over `FixedDetMatrices.primitiveReps n`.

When `n` is not a square, `a d = n` prevents `a² = n`, so in every factor `j(τ) - j(A • τ)` one of
the two poles at `i∞` strictly dominates the other and the leading coefficient of `Φ_n(X, X)` is a
unit of the algebraic integers
(`TauCeti.ModularForm.isUnit_leadingCoeff_of_aeval_j_eq_eval_cyclicIsogenyPolynomial`). Since
`Φ_n(X, X)` has rational integer coefficients, its leading coefficient is `±1`
(`isUnit_leadingCoeff_diagModularPolynomial`), `Φ_n(X, X)` is nonzero
(`diagModularPolynomial_ne_zero`), and all of its roots in any commutative ring are integral over
`ℤ` (`isIntegral_of_aeval_diagModularPolynomial_eq_zero`).

## Main definitions

* `TauCeti.ModularForm.diagModularPolynomial n`: the diagonal specialization `Φ_n(X, X) ∈ ℤ[X]`.

## Main results

* `TauCeti.ModularForm.diagModularPolynomial_one`: `Φ_1(X, X) = 0`.
* `TauCeti.ModularForm.aeval_j_diagModularPolynomial_eq_zero_iff`: `Φ_n(j(τ), j(τ)) = 0` holds
  exactly when `τ` is fixed by some primitive integral matrix of determinant `n`.
* `TauCeti.ModularForm.isUnit_leadingCoeff_diagModularPolynomial`: when `n` is not a square, the
  leading coefficient of `Φ_n(X, X)` is a unit in `ℤ` (`±1`), so `Φ_n(X, X) ≠ 0`
  (`diagModularPolynomial_ne_zero`) and its roots in any commutative ring are integral over `ℤ`
  (`isIntegral_of_aeval_diagModularPolynomial_eq_zero`).

## References

* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §11.C and Theorem 11.18
  (`Φ_m(X, X)` has leading coefficient `±1` for non-square `m`).
* S. Lang, *Elliptic Functions*, 2nd ed., Graduate Texts in Mathematics 112, Springer, 1987,
  Chapter 5, §3 (`Φ_m(X, X)` for non-square `m`).
-/

public noncomputable section

open Polynomial
open UpperHalfPlane hiding I
open scoped MatrixGroups Polynomial.Bivariate

namespace TauCeti.ModularForm

open FixedDetMatrices

variable (n : ℕ) [NeZero n]

/-- **The diagonal modular polynomial `Φ_n(X, X) ∈ ℤ[X]`**, whose roots are the `j`-invariants of
elliptic curves admitting a cyclic `n`-endomorphism. -/
noncomputable def diagModularPolynomial : ℤ[X] :=
  (modularPolynomial n).eval X

/-- At `n = 1 = 1²`, the diagonal modular polynomial vanishes (`Y - X` evaluated at `Y = X`),
showing that the non-square hypothesis in `diagModularPolynomial_ne_zero` is sharp. -/
@[simp]
theorem diagModularPolynomial_one : diagModularPolynomial 1 = 0 := by
  simp [diagModularPolynomial]

/-- Evaluating `diagModularPolynomial n` at `z` evaluates `modularPolynomial n` at `(z, z)`. -/
@[simp]
theorem aeval_diagModularPolynomial {A : Type*} [CommRing A] (z : A) :
    aeval z (diagModularPolynomial n) = aevalAeval z z (modularPolynomial n) :=
  Polynomial.aeval_eval_X z (modularPolynomial n)

variable {n}

/-- `Φ_n(j(τ), j(τ)) = 0` holds exactly when `τ` is fixed by a primitive integral matrix of
determinant `n`. -/
theorem aeval_j_diagModularPolynomial_eq_zero_iff (τ : ℍ) :
    aeval (j τ) (diagModularPolynomial n) = 0 ↔
      ∃ A : FixedDetMatrix (Fin 2) ℤ n,
        TauCeti.IsPrimitive A.val ∧ toGLReal (NeZero.ne (n : ℤ)) A • τ = τ := by
  rw [aeval_diagModularPolynomial, aevalAeval_j_modularPolynomial_eq_zero_iff]

/-- **When `n` is not a square, the leading coefficient of `Φ_n(X, X)` is `±1`**, a unit in `ℤ`. -/
theorem isUnit_leadingCoeff_diagModularPolynomial (hn : ¬ IsSquare n) :
    IsUnit (diagModularPolynomial n).leadingCoeff := by
  set z : ℤ := (diagModularPolynomial n).leadingCoeff
  let P : (integralClosure ℤ ℂ)[X] :=
    (diagModularPolynomial n).map (algebraMap ℤ (integralClosure ℤ ℂ))
  have hP : ∀ τ : ℍ, aeval (j τ) P = (cyclicIsogenyPolynomial n j τ).eval (j τ) := fun τ ↦ by
    rw [aeval_map_algebraMap, aeval_diagModularPolynomial, aevalAeval_j_modularPolynomial]
  obtain ⟨u, hu⟩ := isUnit_leadingCoeff_of_aeval_j_eq_eval_cyclicIsogenyPolynomial hn hP
  have hinj : Function.Injective (algebraMap ℤ (integralClosure ℤ ℂ)) :=
    FaithfulSMul.algebraMap_injective ℤ (integralClosure ℤ ℂ)
  have hu_eq : (u : integralClosure ℤ ℂ) = algebraMap ℤ (integralClosure ℤ ℂ) z := by
    rw [hu, leadingCoeff_map_of_injective hinj]
  have hzC : ((u : integralClosure ℤ ℂ) : ℂ) = (z : ℂ) := by
    rw [hu_eq]; simp
  have hmul : (z : ℂ) * ((u⁻¹ : (integralClosure ℤ ℂ)ˣ) : ℂ) = 1 := by
    rw [← hzC, ← Subalgebra.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hmul
  have hwQ : (((u⁻¹ : (integralClosure ℤ ℂ)ˣ) : integralClosure ℤ ℂ) : ℂ) =
      algebraMap ℚ ℂ (z : ℚ)⁻¹ := by
    rw [eq_inv_of_mul_eq_one_right hmul, map_inv₀, eq_ratCast, Rat.cast_intCast]
  have hintQ : IsIntegral ℤ (z : ℚ)⁻¹ :=
    isIntegral_algebraMap_iff.mp
      (hwQ ▸ ((u⁻¹ : (integralClosure ℤ ℂ)ˣ) : integralClosure ℤ ℂ).property)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintQ
  rw [eq_intCast] at hy
  refine isUnit_iff_exists_inv.mpr ⟨y, ?_⟩
  exact_mod_cast (by rw [hy, mul_inv_cancel₀ (Int.cast_ne_zero.mpr hz0)] : (z : ℚ) * y = 1)

/-- When `n` is not a square, `diagModularPolynomial n` is nonzero. -/
theorem diagModularPolynomial_ne_zero (hn : ¬ IsSquare n) :
    diagModularPolynomial n ≠ 0 :=
  leadingCoeff_ne_zero.mp (isUnit_leadingCoeff_diagModularPolynomial hn).ne_zero

/-- **Every root of `Φ_n(X, X)` for non-square `n` is an algebraic integer.** -/
theorem isIntegral_of_aeval_diagModularPolynomial_eq_zero {A : Type*} [CommRing A]
    (hn : ¬ IsSquare n) {x : A} (hx : aeval x (diagModularPolynomial n) = 0) :
    IsIntegral ℤ x := by
  obtain ⟨u, hu⟩ := isUnit_leadingCoeff_diagModularPolynomial hn
  have h := (integralClosure ℤ A).smul_mem
    (isIntegral_leadingCoeff_smul (diagModularPolynomial n) x hx) (↑u⁻¹ : ℤ)
  rwa [smul_smul, ← hu, Units.inv_mul, one_smul] at h

end TauCeti.ModularForm

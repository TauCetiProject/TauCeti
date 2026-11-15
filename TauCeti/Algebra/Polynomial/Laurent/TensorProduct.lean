/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The Laurent expansion of a polynomial over an algebra

For an algebra `B` over a commutative semiring `R`, possibly noncommutative, the polynomial ring
`B[X]` embeds into the constant Laurent family `R[T;T⁻¹] ⊗[R] B` by the Laurent expansion
`∑ bₙ Xⁿ ↦ ∑ Tⁿ ⊗ bₙ`. Multiplication by a polynomial with scalar coefficients becomes
multiplication by the corresponding Laurent polynomial in the left factor. This is the map
through which a filtered family of submodules of `B` becomes constant once the parameter `X`
is inverted.

## Main definitions

* `TauCeti.laurentExpansion`: the algebra map `B[X] → R[T;T⁻¹] ⊗[R] B`.
* `TauCeti.laurentTensorCoeff`: the coefficients `R[T;T⁻¹] ⊗[R] B ≃ ℤ →₀ B` of an element of the
  constant family.

## Main results

* `TauCeti.laurentExpansion_monomial`: the expansion sends `b Xⁿ` to `Tⁿ ⊗ b`.
* `TauCeti.laurentExpansion_map_algebraMap_mul`: polynomials with scalar coefficients act
  through `Polynomial.toLaurent`.
* `TauCeti.laurentTensorCoeff_laurentExpansion`: the coefficient of `Tⁿ` of the expansion of `p`
  is the coefficient of `Xⁿ` of `p`.
* `TauCeti.laurentExpansion_injective`: the expansion is injective.
-/

public section

open Polynomial LaurentPolynomial
open scoped TensorProduct

namespace Algebra.TensorProduct

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [Semiring B]
  [Algebra R B]

/-- Multiplying by `a ⊗ 1` is the scalar action of `a` on `A ⊗[R] B`. -/
theorem tmul_one_mul_eq_smul (a : A) (y : A ⊗[R] B) : (a ⊗ₜ[R] (1 : B)) * y = a • y := by
  rw [Algebra.smul_def, algebraMap_apply, Algebra.algebraMap_self_apply]

end Algebra.TensorProduct

namespace TauCeti

variable {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]

variable (R B)

/-- The Laurent expansion `∑ bₙ Xⁿ ↦ ∑ Tⁿ ⊗ bₙ` of a polynomial over `B`, as an algebra map
into the constant family `R[T;T⁻¹] ⊗[R] B`. -/
noncomputable def laurentExpansion : B[X] →ₐ[R] R[T;T⁻¹] ⊗[R] B :=
  eval₂AlgHom Algebra.TensorProduct.includeRight (T 1 ⊗ₜ 1) fun b ↦ by
    rw [Algebra.TensorProduct.includeRight_apply]
    exact (Commute.one_left _).tmul (Commute.one_right b)

variable {R B}

/-- The Laurent expansion sends the monomial `b Xⁿ` to `Tⁿ ⊗ b`. -/
@[simp]
theorem laurentExpansion_monomial (n : ℕ) (b : B) :
    laurentExpansion R B (monomial n b) = T n ⊗ₜ b := by
  rw [laurentExpansion, eval₂AlgHom_apply, eval₂_monomial]
  simp [Algebra.TensorProduct.tmul_pow, T_pow]

/-- The Laurent expansion sends a constant `b` to `1 ⊗ b`. -/
@[simp]
theorem laurentExpansion_C (b : B) : laurentExpansion R B (C b) = 1 ⊗ₜ b := by
  rw [← monomial_zero_left, laurentExpansion_monomial, Nat.cast_zero, T_zero]

/-- The Laurent expansion sends the variable `X` to `T ⊗ 1`. -/
@[simp]
theorem laurentExpansion_X : laurentExpansion R B X = T 1 ⊗ₜ 1 := by
  rw [← monomial_one_one_eq_X, laurentExpansion_monomial, Nat.cast_one]

/-- The Laurent expansion of a polynomial with scalar coefficients is its image in the left
tensor factor. -/
theorem laurentExpansion_map_algebraMap (p : R[X]) :
    laurentExpansion R B (p.map (algebraMap R B)) = toLaurent p ⊗ₜ 1 := by
  have h : (laurentExpansion R B).comp (mapAlg R B) =
      (Algebra.TensorProduct.includeLeft (S := R)).comp (toLaurentAlg (R := R)) :=
    Polynomial.algHom_ext (by simp [mapAlg_eq_map])
  simpa [mapAlg_eq_map, toLaurentAlg_apply] using congrArg (· p) h

/-- Multiplying by a polynomial with scalar coefficients multiplies the Laurent expansion by the
corresponding Laurent polynomial. -/
theorem laurentExpansion_map_algebraMap_mul (g : R[X]) (p : B[X]) :
    laurentExpansion R B (g.map (algebraMap R B) * p) =
      toLaurent g • laurentExpansion R B p := by
  rw [map_mul, laurentExpansion_map_algebraMap, Algebra.TensorProduct.tmul_one_mul_eq_smul]

/-- Multiplying by `Xᵏ` multiplies the Laurent expansion by `Tᵏ`. -/
theorem laurentExpansion_X_pow_mul (k : ℕ) (p : B[X]) :
    laurentExpansion R B ((Polynomial.X : B[X]) ^ k * p) =
      (T k : R[T;T⁻¹]) • laurentExpansion R B p := by
  simpa using laurentExpansion_map_algebraMap_mul ((Polynomial.X : R[X]) ^ k) p

variable (R B) in
/-- The coefficients of an element of the constant family `R[T;T⁻¹] ⊗[R] B`: the coefficient of
`Tⁿ` in `∑ Tⁿ ⊗ bₙ` is `bₙ`. -/
noncomputable def laurentTensorCoeff : R[T;T⁻¹] ⊗[R] B ≃ₗ[R] ℤ →₀ B :=
  (AddMonoidAlgebra.coeffLinearEquiv R).rTensor B ≪≫ₗ TensorProduct.finsuppScalarLeft R B ℤ

/-- The coefficient of `Tⁿ` in `f ⊗ b` is the coefficient of `Tⁿ` in `f` times `b`. -/
@[simp]
theorem laurentTensorCoeff_tmul_apply (f : R[T;T⁻¹]) (b : B) (n : ℤ) :
    laurentTensorCoeff R B (f ⊗ₜ b) n = f.coeff n • b := by
  simp [laurentTensorCoeff]

/-- The coefficient of `Tⁿ` of the Laurent expansion of `p` is the coefficient of `Xⁿ` of `p`. -/
@[simp]
theorem laurentTensorCoeff_laurentExpansion (p : B[X]) (n : ℕ) :
    laurentTensorCoeff R B (laurentExpansion R B p) n = p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial m b =>
    rw [laurentExpansion_monomial, laurentTensorCoeff_tmul_apply, T_apply, coeff_monomial]
    split_ifs <;> simp_all

/-- The Laurent expansion is injective. -/
theorem laurentExpansion_injective : Function.Injective (laurentExpansion R B) := fun p q h ↦
  AddMonoidAlgebra.ext <| Finsupp.ext fun n ↦ by
    rw [← laurentTensorCoeff_laurentExpansion (R := R) p n,
      ← laurentTensorCoeff_laurentExpansion (R := R) q n, h]

end TauCeti

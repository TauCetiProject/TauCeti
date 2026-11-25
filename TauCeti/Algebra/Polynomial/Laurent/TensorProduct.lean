/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Algebra.TensorProduct.Mul

/-!
# Polynomials over an algebra in the constant Laurent family

For an algebra `B` over a commutative semiring `R`, possibly noncommutative, the polynomial ring
`B[X]` embeds into the constant Laurent family `R[T;T⁻¹] ⊗[R] B` by `∑ bₙ Xⁿ ↦ ∑ Tⁿ ⊗ bₙ`.
Multiplication by a polynomial with scalar coefficients becomes multiplication by the
corresponding Laurent polynomial in the left factor. This is the map through which a filtered
family of submodules of `B` becomes constant once the parameter `X` is inverted.

## Main definitions

* `TauCeti.toLaurentTensor`: the algebra map `B[X] → R[T;T⁻¹] ⊗[R] B`.
* `TauCeti.laurentTensorCoeff`: the coefficients `R[T;T⁻¹] ⊗[R] M ≃ ℤ →₀ M` of an element of the
  constant family, for an `R`-module `M`.

## Main results

* `TauCeti.toLaurentTensor_monomial`: the map sends `b Xⁿ` to `Tⁿ ⊗ b`.
* `TauCeti.toLaurentTensor_map_algebraMap_mul`: polynomials with scalar coefficients act
  through `Polynomial.toLaurent`.
* `TauCeti.laurentTensorCoeff_toLaurentTensor_apply_natCast`: the coefficient of `Tⁿ` of the
  image of `p` is the coefficient of `Xⁿ` of `p`.
* `TauCeti.toLaurentTensor_injective`: the map is injective.
-/

public section

open Polynomial LaurentPolynomial
open scoped TensorProduct

namespace TauCeti

section Coeff

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The coefficients of an element of the constant family `R[T;T⁻¹] ⊗[R] M`: the coefficient of
`Tⁿ` in `∑ Tⁿ ⊗ mₙ` is `mₙ`. -/
noncomputable def laurentTensorCoeff : R[T;T⁻¹] ⊗[R] M ≃ₗ[R] ℤ →₀ M :=
  (AddMonoidAlgebra.coeffLinearEquiv R).rTensor M ≪≫ₗ TensorProduct.finsuppScalarLeft R M ℤ

variable {R M}

/-- The coefficient of `Tⁿ` in `f ⊗ m` is the coefficient of `Tⁿ` in `f` times `m`. -/
@[simp]
theorem laurentTensorCoeff_tmul_apply (f : R[T;T⁻¹]) (m : M) (n : ℤ) :
    laurentTensorCoeff R M (f ⊗ₜ m) n = f.coeff n • m := by
  simp [laurentTensorCoeff]

/-- The coefficients of `Tⁿ ⊗ m` are `m` at `n` and zero elsewhere. -/
@[simp]
theorem laurentTensorCoeff_T_tmul (n : ℤ) (m : M) :
    laurentTensorCoeff R M (T n ⊗ₜ m) = Finsupp.single n m := by
  ext k
  simp [Finsupp.single_apply]

/-- The element of the constant family with the single coefficient `m` at `n` is `Tⁿ ⊗ m`. -/
@[simp]
theorem laurentTensorCoeff_symm_single (n : ℤ) (m : M) :
    (laurentTensorCoeff R M).symm (Finsupp.single n m) = T n ⊗ₜ m := by
  rw [LinearEquiv.symm_apply_eq, laurentTensorCoeff_T_tmul]

end Coeff

variable {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]

variable (R B)

/-- The map `∑ bₙ Xⁿ ↦ ∑ Tⁿ ⊗ bₙ` from polynomials over `B` to the constant Laurent family
`R[T;T⁻¹] ⊗[R] B`, as an algebra map. -/
noncomputable def toLaurentTensor : B[X] →ₐ[R] R[T;T⁻¹] ⊗[R] B :=
  eval₂AlgHom Algebra.TensorProduct.includeRight (T 1 ⊗ₜ 1) fun b ↦ by
    rw [Algebra.TensorProduct.includeRight_apply]
    exact (Commute.one_left _).tmul (Commute.one_right b)

variable {R B}

/-- `toLaurentTensor` sends the monomial `b Xⁿ` to `Tⁿ ⊗ b`. -/
@[simp]
theorem toLaurentTensor_monomial (n : ℕ) (b : B) :
    toLaurentTensor R B (monomial n b) = T n ⊗ₜ b := by
  rw [toLaurentTensor, eval₂AlgHom_apply, eval₂_monomial]
  simp [Algebra.TensorProduct.tmul_pow, T_pow]

/-- `toLaurentTensor` sends a constant `b` to `1 ⊗ b`. -/
@[simp]
theorem toLaurentTensor_C (b : B) : toLaurentTensor R B (C b) = 1 ⊗ₜ b := by
  rw [← monomial_zero_left, toLaurentTensor_monomial, Nat.cast_zero, T_zero]

/-- `toLaurentTensor` sends the variable `X` to `T ⊗ 1`. -/
@[simp]
theorem toLaurentTensor_X : toLaurentTensor R B X = T 1 ⊗ₜ 1 := by
  rw [← monomial_one_one_eq_X, toLaurentTensor_monomial, Nat.cast_one]

/-- `toLaurentTensor` sends a polynomial with scalar coefficients to its image in the left
tensor factor. -/
@[simp]
theorem toLaurentTensor_map_algebraMap (p : R[X]) :
    toLaurentTensor R B (p.map (algebraMap R B)) = toLaurent p ⊗ₜ 1 := by
  have h : (toLaurentTensor R B).comp (mapAlg R B) =
      (Algebra.TensorProduct.includeLeft (S := R)).comp (toLaurentAlg (R := R)) :=
    Polynomial.algHom_ext (by simp [mapAlg_eq_map])
  simpa [mapAlg_eq_map, toLaurentAlg_apply] using congrArg (· p) h

/-- Multiplying by a polynomial with scalar coefficients multiplies the image under
`toLaurentTensor` by the corresponding Laurent polynomial. -/
theorem toLaurentTensor_map_algebraMap_mul (g : R[X]) (p : B[X]) :
    toLaurentTensor R B (g.map (algebraMap R B) * p) =
      toLaurent g • toLaurentTensor R B p := by
  rw [map_mul, toLaurentTensor_map_algebraMap, Algebra.TensorProduct.tmul_one_mul_eq_smul]

/-- The coefficient of `Tⁿ` of the image of `p` is the coefficient of `Xⁿ` of `p`. -/
@[simp]
theorem laurentTensorCoeff_toLaurentTensor_apply_natCast (p : B[X]) (n : ℕ) :
    laurentTensorCoeff R B (toLaurentTensor R B p) n = p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial m b =>
    rw [toLaurentTensor_monomial, laurentTensorCoeff_tmul_apply, T_apply, coeff_monomial]
    split_ifs <;> simp_all

/-- The image of a polynomial has no coefficients at negative powers of `T`. -/
theorem laurentTensorCoeff_toLaurentTensor_apply_of_neg (p : B[X]) {n : ℤ} (hn : n < 0) :
    laurentTensorCoeff R B (toLaurentTensor R B p) n = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial m b =>
    simp [show (m : ℤ) ≠ n by omega]

/-- `toLaurentTensor` is injective. -/
theorem toLaurentTensor_injective : Function.Injective (toLaurentTensor R B) := fun p q h ↦
  AddMonoidAlgebra.ext <| Finsupp.ext fun n ↦ by
    rw [← laurentTensorCoeff_toLaurentTensor_apply_natCast (R := R) p n,
      ← laurentTensorCoeff_toLaurentTensor_apply_natCast (R := R) q n, h]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
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

## Main results

* `TauCeti.laurentExpansion_monomial`: the expansion sends `b Xⁿ` to `Tⁿ ⊗ b`.
* `TauCeti.laurentExpansion_map_algebraMap_mul`: polynomials with scalar coefficients act
  through `Polynomial.toLaurent`.
* `TauCeti.laurentExpansion_injective`: the expansion is injective.
-/

public section

open Polynomial LaurentPolynomial
open scoped TensorProduct

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
  rw [map_mul, laurentExpansion_map_algebraMap]
  conv_lhs => rw [← Algebra.algebraMap_self_apply (toLaurent g),
    ← Algebra.TensorProduct.algebraMap_apply]
  exact (Algebra.smul_def _ _).symm

/-- Multiplying by `Xᵏ` multiplies the Laurent expansion by `Tᵏ`. -/
theorem laurentExpansion_X_pow_mul (k : ℕ) (p : B[X]) :
    laurentExpansion R B ((Polynomial.X : B[X]) ^ k * p) =
      (T k : R[T;T⁻¹]) • laurentExpansion R B p := by
  simpa using laurentExpansion_map_algebraMap_mul ((Polynomial.X : R[X]) ^ k) p

/-- Reading off the coefficient of `Tⁿ` of an element of `R[T;T⁻¹] ⊗[R] B`. -/
private noncomputable def coeffT (n : ℤ) : R[T;T⁻¹] ⊗[R] B →ₗ[R] B :=
  TensorProduct.lid R B ∘ₗ
    ((Finsupp.lapply n ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap).rTensor B)

private theorem coeffT_laurentExpansion (p : B[X]) (n : ℕ) :
    coeffT n (laurentExpansion R B p) = p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial m b =>
    simp only [laurentExpansion_monomial, coeffT, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.rTensor_tmul, coeff_monomial]
    by_cases h : m = n
    · subst h
      simp
    · simp [h]

/-- The Laurent expansion is injective: the coefficient of `Tⁿ` of the expansion of `p` is the
coefficient of `Xⁿ` of `p`. -/
theorem laurentExpansion_injective : Function.Injective (laurentExpansion R B) := fun p q h ↦
  AddMonoidAlgebra.ext <| Finsupp.ext fun n ↦ by
    rw [← coeffT_laurentExpansion (R := R) p n, ← coeffT_laurentExpansion (R := R) q n, h]

end TauCeti

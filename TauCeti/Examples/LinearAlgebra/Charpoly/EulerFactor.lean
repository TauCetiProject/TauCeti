/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Charpoly.Projective

/-!
# Euler factors as reversed characteristic polynomials

For a Frobenius `φ` acting on a lattice `T` with cyclotomic character value `N`, the two usual
normalizations of an Euler factor are `det (1 - φ X | T)` and `det (1 - φ⁻¹ X | T^*)` on the Tate
dual `T^* = Hom(T, O(1))`, where `φ⁻¹` acts as `N⁻¹` times the transpose of `φ`. These examples
test `LinearMap.projectiveCharpolyRev` on the cases that distinguish the two:

* the zero endomorphism of a rank-two module has reversed characteristic polynomial `1`, although
  its characteristic polynomial is `X ^ 2`;
* for `T = ℤ_p(1)`, where `φ` is multiplication by `N`, the polynomial on `T` is `1 - N X`, while
  `φ⁻¹` on `T^*` is the identity, with polynomial `1 - X`; the two differ when `N ≠ 1` but agree
  modulo `N - 1`;
* an elliptic factor `1 - a X + N X ^ 2` becomes `1 - a N⁻¹ X + N⁻¹ X ^ 2` after scaling by `N⁻¹`;
* every endomorphism of the zero module has reversed characteristic polynomial `1`;
* `N φ⁻¹` is a root of the dual-normalized polynomial `det (1 - N⁻¹ φ X)`.
-/

open Polynomial LinearMap

namespace TauCeti.EulerFactorExamples

/-- The zero endomorphism of a free module of rank two has reversed characteristic polynomial
`1`. -/
example : projectiveCharpolyRev (0 : Module.End ℤ (Fin 2 → ℤ)) = 1 :=
  projectiveCharpolyRev_zero

/-- The characteristic polynomial of the same zero endomorphism is `X ^ 2`, not `1`. -/
example : (0 : Module.End ℤ (Fin 2 → ℤ)).charpoly = X ^ 2 := by
  simp

/-- The identity of a rank-one module has reversed characteristic polynomial `1 - X`. -/
example {R : Type*} [CommRing R] [Nontrivial R] :
    projectiveCharpolyRev (LinearMap.id : Module.End R R) = 1 - X := by
  rw [projectiveCharpolyRev_eq_reverse_charpoly, ← one_smul R LinearMap.id,
    reverse_charpoly_smul_id, Module.finrank_self, pow_one, C_1, one_mul]

/-- Multiplication by `N` on a rank-one module has reversed characteristic polynomial
`1 - N X`. -/
example {R : Type*} [CommRing R] [Nontrivial R] (N : R) :
    projectiveCharpolyRev (N • LinearMap.id : Module.End R R) = 1 - C N * X := by
  rw [projectiveCharpolyRev_eq_reverse_charpoly, reverse_charpoly_smul_id, Module.finrank_self,
    pow_one]

/-- With `N = 3`, the polynomials `1 - 3 X` and `1 - X` of multiplication by `3` and of the
identity on `ℤ` are different. -/
example : projectiveCharpolyRev ((3 : ℤ) • LinearMap.id : Module.End ℤ ℤ) ≠
    projectiveCharpolyRev (LinearMap.id : Module.End ℤ ℤ) := by
  intro h
  have h1 := congrArg (fun p : ℤ[X] ↦ p.coeff 1) h
  simp only [coeff_projectiveCharpolyRev_one, map_smul, LinearMap.trace_id, Module.finrank_self,
    Nat.cast_one, smul_eq_mul, mul_one, projectiveTrace_eq_trace] at h1
  omega

/-- They agree modulo `3 - 1 = 2`. -/
example : C (2 : ℤ) ∣ projectiveCharpolyRev ((3 : ℤ) • LinearMap.id : Module.End ℤ ℤ) -
    projectiveCharpolyRev (LinearMap.id : Module.End ℤ ℤ) := by
  simpa using C_sub_one_dvd_projectiveCharpolyRev_smul_sub (3 : ℤ) (LinearMap.id : Module.End ℤ ℤ)

/-- The dual normalization `det (1 - N⁻¹ φᵀ X)` is `det (1 - φ X)` evaluated at `N⁻¹ X`. -/
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (φ : Module.End K V) (N : K) :
    projectiveCharpolyRev (N⁻¹ • φ.dualMap) = (projectiveCharpolyRev φ).comp (C N⁻¹ * X) := by
  rw [projectiveCharpolyRev_smul, projectiveCharpolyRev_dualMap]

/-- An elliptic Euler factor `1 - a X + N X ^ 2` becomes `1 - a N⁻¹ X + N⁻¹ X ^ 2` after scaling the
endomorphism by `N⁻¹`. -/
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (φ : Module.End K V) (a N : K) (hN : N ≠ 0)
    (h : projectiveCharpolyRev φ = 1 - C a * X + C N * X ^ 2) :
    projectiveCharpolyRev (N⁻¹ • φ) = 1 - C (a * N⁻¹) * X + C N⁻¹ * X ^ 2 := by
  have hN' : C N * C N⁻¹ ^ 2 = C N⁻¹ := by
    rw [← C_pow, ← C_mul]
    congr 1
    field_simp
  rw [projectiveCharpolyRev_smul, h]
  simp only [Polynomial.add_comp, Polynomial.sub_comp, Polynomial.one_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp, Polynomial.X_pow_comp, C_mul]
  linear_combination X ^ 2 * hN'

/-- Every endomorphism of the zero module has reversed characteristic polynomial `1`. -/
example {R : Type*} [CommRing R] (f : Module.End R (Fin 0 → R)) : projectiveCharpolyRev f = 1 := by
  rw [Subsingleton.elim f 0, projectiveCharpolyRev_zero]

/-- `N φ⁻¹` is a root of `det (1 - N⁻¹ φ X)`. -/
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (φ : V ≃ₗ[K] V) (N : K) (hN : N ≠ 0) :
    aeval (N • (φ.symm : Module.End K V)) (projectiveCharpolyRev (N⁻¹ • (φ : Module.End K V))) =
      0 := by
  refine aeval_projectiveCharpolyRev_eq_zero_of_mul_eq_one ?_
  rw [smul_mul_smul_comm, mul_inv_cancel₀ hN, one_smul]
  ext x
  simp

end TauCeti.EulerFactorExamples

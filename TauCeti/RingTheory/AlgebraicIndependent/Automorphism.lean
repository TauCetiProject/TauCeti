/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Algebraic independence of eigenvectors of an algebra endomorphism

Let `A` be a commutative integral domain that is a faithful algebra over a commutative ring `R`,
and let `σ : A →ₐ[R] A` be an `R`-algebra endomorphism. Suppose `(yᵢ)` is a family of nonzero
elements of `A` satisfying `σ (yᵢ) = algebraMap R A (uᵢ) * yᵢ` for scalars `uᵢ : R`. If the
monomial-eigenvalue map `d ↦ ∏ᵢ uᵢ ^ (d i)` on finitely supported exponent tuples `ι →₀ ℕ` is
injective, then distinct monomials in the `yᵢ` are nonzero `σ`-eigenvectors with distinct
eigenvalues, hence `R`-linearly independent by `Module.End.eigenvectors_linearIndependent'`, so
`(yᵢ)` is algebraically independent over `R`
(`AlgHom.algebraicIndependent_of_algHom_eigenvectors`).

## Main results

* `AlgHom.algebraicIndependent_of_algHom_eigenvectors`: nonzero `σ`-eigenvectors whose eigenvalues
  have injective monomial products are algebraically independent over `R`.
-/

public section

namespace AlgHom

variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **Algebraic independence of eigenvectors with multiplicatively independent eigenvalues.**
Let `σ : A →ₐ[R] A` be an `R`-algebra endomorphism of a domain `A` faithful over `R`, and let
`y : ι → A` be nonzero elements satisfying `σ (y i) = algebraMap R A (u i) * y i`. If distinct
monomial exponent tuples `d : ι →₀ ℕ` produce distinct products `∏ i, u i ^ d i` in `R`, then `y`
is algebraically independent over `R`. -/
theorem algebraicIndependent_of_algHom_eigenvectors [IsDomain A] [FaithfulSMul R A]
    (σ : A →ₐ[R] A) {u : ι → R} {y : ι → A}
    (hy0 : ∀ i, y i ≠ 0) (hσ : ∀ i, σ (y i) = algebraMap R A (u i) * y i)
    (hu : Function.Injective fun d : ι →₀ ℕ ↦ d.prod fun i k ↦ u i ^ k) :
    AlgebraicIndependent R y := by
  classical
  have : IsDomain R := Function.Injective.isDomain _ (FaithfulSMul.algebraMap_injective R A)
  let f : Module.End R A := σ.toLinearMap
  let μ : (ι →₀ ℕ) → R := fun d ↦ d.prod fun i k ↦ u i ^ k
  let v : (ι →₀ ℕ) → A := fun d ↦ d.prod fun i k ↦ y i ^ k
  have heig (d : ι →₀ ℕ) : f.HasEigenvector (μ d) (v d) := by
    refine ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
    · rw [AlgHom.toLinearMap_apply, Algebra.smul_def, map_finsuppProd, map_finsuppProd,
        ← Finsupp.prod_mul]
      exact Finsupp.prod_congr fun i _ ↦ by rw [map_pow, hσ, mul_pow, map_pow]
    · exact d.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ (hy0 i)
  have hli : LinearIndependent R v := f.eigenvectors_linearIndependent' μ hu v heig
  rw [_root_.algebraicIndependent_iff]
  intro P hP
  have hsum : ∑ d ∈ P.support, P.coeff d • v d = 0 := by
    conv at hP => rw [P.as_sum]
    simpa only [map_sum, MvPolynomial.aeval_monomial, Algebra.smul_def, v] using hP
  ext d
  by_cases hd : d ∈ P.support
  · simpa using linearIndependent_iff'.1 hli P.support P.coeff hsum d hd
  · simpa using MvPolynomial.notMem_support_iff.1 hd

end AlgHom

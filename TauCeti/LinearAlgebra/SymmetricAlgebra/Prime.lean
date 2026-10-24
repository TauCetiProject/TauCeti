/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Noetherian

/-!
# Degree-one elements of a symmetric algebra as prime elements

This file records the divisibility theory of the degree-one elements `ι ℓ` of a symmetric algebra
`Sym M`. One degree-one element divides another exactly when the vectors are proportional:
`ι ℓ ∣ ι m ↔ m ∈ R ∙ ℓ`, because a quotient of degree-one elements has degree zero. Over a field
`K`, a nonzero `ι ℓ` is a prime element of `Sym M`, since `ℓ` extends to a basis and `Sym M` is
then a polynomial ring in which `ι ℓ` is a variable. When `M` is finite-dimensional, `Sym M` is
Noetherian and `ι ℓ` spans a prime ideal of height one.

For polynomial functions `Sym(V*)` on a vector space `V`, the prime ideal spanned by a nonzero
linear form `ℓ` is the ideal of the hyperplane `ker ℓ`. These are the codimension-one primes along
which the quotient map of a finite linear group can ramify.

## Main results

* `SymmetricAlgebra.ι_dvd_ι_iff`: `ι ℓ ∣ ι m` exactly when `m` is a multiple of `ℓ`.
* `SymmetricAlgebra.prime_ι`: over a field, a nonzero degree-one element is prime.
* `SymmetricAlgebra.height_span_singleton_ι`: over a field and for finite-dimensional `M`, a
  nonzero degree-one element spans an ideal of height one.
-/

public section

namespace SymmetricAlgebra

open TauCeti.SymmetricAlgebra

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A degree-one element `ι ℓ` of a symmetric algebra divides another one `ι m` exactly when `m`
is a multiple of `ℓ`. -/
theorem ι_dvd_ι_iff {ℓ m : M} : ι R M ℓ ∣ ι R M m ↔ m ∈ R ∙ ℓ := by
  refine ⟨fun ⟨q, hq⟩ ↦ ?_, fun h ↦ ?_⟩
  · -- The degree-one component of `ι ℓ * q` is `ι ℓ` times the constant term of `q`.
    have h1 : (DirectSum.decompose (homogeneousSubmodule R M) (ι R M m) (1 + 0) :
        SymmetricAlgebra R M) = ι R M ℓ * algebraMap R _ (algebraMapInv q) := by
      rw [hq, DirectSum.coe_decompose_mul_add_of_left_mem _ (ι_mem_homogeneousSubmodule R M ℓ),
        ← GradedRing.projZeroRingHom_apply, projZeroRingHom_eq_algebraMap_comp_algebraMapInv,
        RingHom.comp_apply, RingHom.coe_coe]
    rw [Nat.add_zero, DirectSum.decompose_of_mem_same _ (ι_mem_homogeneousSubmodule R M m)] at h1
    refine Submodule.mem_span_singleton.2 ⟨algebraMapInv q, ι_injective R M ?_⟩
    rw [h1, map_smul, Algebra.smul_def, mul_comm]
  · obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 h
    exact ⟨algebraMap R _ r, by rw [map_smul, Algebra.smul_def, mul_comm]⟩

end CommSemiring

section Field

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {ℓ : M}

/-- Over a field, a nonzero degree-one element of a symmetric algebra is a prime element: after
extending `ℓ` to a basis, it is a variable of the polynomial ring `Sym M`. -/
theorem prime_ι (hℓ : ℓ ≠ 0) : Prime (ι K M ℓ) := by
  have hs : LinearIndepOn K id ({ℓ} : Set M) := (linearIndepOn_singleton_iff K).2 hℓ
  let b := Module.Basis.extend hs
  have hmem : ℓ ∈ hs.extend (Set.subset_univ _) := Module.Basis.subset_extend hs rfl
  have hb : ι K M ℓ = (equivMvPolynomial b).symm (MvPolynomial.X ⟨ℓ, hmem⟩) := by
    rw [equivMvPolynomial_symm_X, Module.Basis.extend_apply_self]
  rw [hb, MulEquiv.prime_iff]
  exact MvPolynomial.prime_X

/-- Over a field, a nonzero degree-one element of the symmetric algebra of a finite-dimensional
vector space spans a prime ideal of height one. -/
theorem height_span_singleton_ι [Module.Finite K M] (hℓ : ℓ ≠ 0) :
    (Ideal.span {ι K M ℓ}).height = 1 :=
  Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (prime_ι hℓ).ne_zero) (prime_ι hℓ).not_isUnit

end Field

end SymmetricAlgebra

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Tensor products over a field that are domains

Let `K` be a field. If `A` is a `K`-algebra and `L` a `K`-algebra with `A ⊗[K] L` a domain, then
`B ⊗[K] L` is again a domain for every localization `B` of `A` at nonzero elements, since it is the
localization of `A ⊗[K] L` at their images, which stay nonzero because `A ⟶ A ⊗[K] L` is injective.
In particular this passes from a domain `A` to its fraction field: if `A ⊗[K] L` is a domain then
so is `Frac(A) ⊗[K] L`. This is how the function field of an integral scheme over `K` inherits
"geometric integrality" from the coordinate rings of its affine opens.

As an instance of this, for any `K`-algebra `D` that is a domain and any set of variables `σ`, the
tensor product `K(X_σ) ⊗[K] D` of `D` with the rational function field
`K(X_σ) = FractionRing (MvPolynomial σ K)` is again a domain. Indeed, `K[X_σ] ⊗[K] D` is the
polynomial ring `D[X_σ]`, a domain.

Since every field extension is algebraic over a purely transcendental one, this is the purely
transcendental half of the comparison between the irreducible components of a scheme over `K`
and those of its extension of scalars to a field extension of `K`.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {K : Type*} [Field K]

/-- Let `B` be a localization of the `K`-algebra `A` at a submonoid of nonzero divisors. If
`A ⊗[K] L` is a domain, then so is `B ⊗[K] L`. -/
theorem isDomain_tensorProduct_of_isLocalization {A : Type*} [CommRing A] [Algebra K A]
    (M : Submonoid A) (hM : M ≤ nonZeroDivisors A) (B : Type*) [CommRing B] [Algebra K B]
    [Algebra A B] [IsScalarTower K A B] [IsLocalization M B] (L : Type*) [CommRing L]
    [Algebra K L] [IsDomain (A ⊗[K] L)] : IsDomain (B ⊗[K] L) := by
  have : Nontrivial A :=
    (Algebra.TensorProduct.includeLeft (R := K) (S := K) (B := L)).domain_nontrivial
  have : Nontrivial L := (Algebra.TensorProduct.includeRight (R := K) (A := A)).domain_nontrivial
  let φ : A ⊗[K] L →ₐ[K] B ⊗[K] L :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A B) (AlgHom.id K L)
  algebraize [φ.toRingHom]
  have : IsScalarTower A (A ⊗[K] L) (B ⊗[K] L) := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, φ]
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[K] L) M) (B ⊗[K] L) :=
    IsLocalization.tensorProduct_tensorProduct K L M B
      (by ext; simp [RingHom.algebraMap_toAlgebra, φ])
  -- `A ⟶ A ⊗[K] L` is injective, so it carries the nonzero divisors `M` to nonzero elements.
  have hinj : Function.Injective (algebraMap A (A ⊗[K] L)) :=
    Algebra.TensorProduct.includeLeft_injective (S := K) (algebraMap K L).injective
  exact IsLocalization.isDomain_of_le_nonZeroDivisors _
    (M := Algebra.algebraMapSubmonoid (A ⊗[K] L) M) (map_le_nonZeroDivisors_of_injective _ hinj hM)

/-- The tensor product of a domain over a field `K` with a rational function field over `K` is a
domain. -/
instance isDomain_fractionRing_mvPolynomial_tensorProduct {σ D : Type*} [CommRing D] [IsDomain D]
    [Algebra K D] : IsDomain (FractionRing (MvPolynomial σ K) ⊗[K] D) := by
  have : IsDomain (MvPolynomial σ K ⊗[K] D) :=
    ((Algebra.TensorProduct.comm K _ D).trans
      ((MvPolynomial.algebraTensorAlgEquiv K D).restrictScalars K)).toMulEquiv.isDomain
  exact isDomain_tensorProduct_of_isLocalization (nonZeroDivisors (MvPolynomial σ K)) le_rfl _ D

end TauCeti

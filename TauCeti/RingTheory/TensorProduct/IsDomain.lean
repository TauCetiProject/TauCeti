/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Tensoring a domain with a rational function field

Let `K` be a field and `D` a `K`-algebra that is a domain. For any set of variables `σ`, the
tensor product `K(X_σ) ⊗[K] D` of `D` with the rational function field
`K(X_σ) = FractionRing (MvPolynomial σ K)` is again a domain. Indeed, `K[X_σ] ⊗[K] D` is the
polynomial ring `D[X_σ]`, a domain, and `K(X_σ) ⊗[K] D` is its localization at the nonzero
polynomials with coefficients in `K`.

Since every field extension is algebraic over a purely transcendental one, this is the purely
transcendental half of the comparison between the irreducible components of a scheme over `K`
and those of its extension of scalars to a field extension of `K`.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {K : Type*} [Field K]

/-- The tensor product of a domain over a field `K` with a rational function field over `K` is a
domain. -/
instance isDomain_fractionRing_mvPolynomial_tensorProduct {σ D : Type*} [CommRing D] [IsDomain D]
    [Algebra K D] : IsDomain (FractionRing (MvPolynomial σ K) ⊗[K] D) := by
  let R := MvPolynomial σ K
  let F := FractionRing R
  let S := R ⊗[K] D
  have : IsDomain S :=
    ((Algebra.TensorProduct.comm K R D).trans
      ((MvPolynomial.algebraTensorAlgEquiv K D).restrictScalars K)).toMulEquiv.isDomain
  have hinj : Function.Injective (algebraMap R S) :=
    Algebra.TensorProduct.includeLeft_injective (S := K) (algebraMap K D).injective
  -- `F ⊗[R] S` is the localization of the domain `S` at the image of the nonzero elements of `R`.
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := F) (B := S)
  have : IsDomain (F ⊗[R] S) := IsLocalization.isDomain_of_le_nonZeroDivisors (R := S)
    (M := Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) (S := F ⊗[R] S)
    (map_le_nonZeroDivisors_of_injective _ hinj le_rfl)
  exact (Algebra.TensorProduct.cancelBaseChange K R R F D).symm.toMulEquiv.isDomain

end TauCeti

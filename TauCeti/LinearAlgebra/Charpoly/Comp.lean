/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# The characteristic polynomials of `g ∘ f` and `f ∘ g`

For linear maps `f : M → N` and `g : N → M` between finite free modules over a commutative ring,
the endomorphisms `g ∘ f` of `M` and `f ∘ g` of `N` have the same characteristic polynomial up to
a power of `X` accounting for the difference of the ranks
(`LinearMap.X_pow_finrank_mul_charpoly_comp_comm`). When the ranks agree the two characteristic
polynomials are equal (`LinearMap.charpoly_comp_comm`). Read in bases, this is Mathlib's
`Matrix.charpoly_mul_comm'` for rectangular matrices.

A typical use is a pair of endomorphisms `A = g ∘ f` and `B = f ∘ g` which are conjugate only
through maps that are not invertible, such as the derivatives of local maps that are inverse to
each other only on a submanifold.
-/

public section

open Module Polynomial

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M] [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]

/-- For linear maps `f : M → N` and `g : N → M` between finite free modules, the characteristic
polynomials of `g ∘ f` and `f ∘ g` agree after multiplying by `X` to the rank of the other
module. -/
theorem X_pow_finrank_mul_charpoly_comp_comm (f : M →ₗ[R] N) (g : N →ₗ[R] M) :
    X ^ finrank R N * (g ∘ₗ f).charpoly = X ^ finrank R M * (f ∘ₗ g).charpoly := by
  nontriviality R
  let bM := Module.finBasis R M
  let bN := Module.finBasis R N
  rw [← charpoly_toMatrix (g ∘ₗ f) bM, ← charpoly_toMatrix (f ∘ₗ g) bN, toMatrix_comp bM bN bM,
    toMatrix_comp bN bM bN]
  simpa using Matrix.charpoly_mul_comm' (toMatrix bN bM g) (toMatrix bM bN f)

/-- For linear maps `f : M → N` and `g : N → M` between finite free modules of the same rank, the
endomorphisms `g ∘ f` and `f ∘ g` have the same characteristic polynomial. -/
theorem charpoly_comp_comm (f : M →ₗ[R] N) (g : N →ₗ[R] M) (h : finrank R M = finrank R N) :
    (g ∘ₗ f).charpoly = (f ∘ₗ g).charpoly := by
  nontriviality R
  have := X_pow_finrank_mul_charpoly_comp_comm f g
  rw [h] at this
  exact (isRegular_X_pow _).left.eq_iff.mp this

end LinearMap

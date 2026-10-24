/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.LinearAlgebra.Dual.BaseChange

/-!
# Scalar extension of a perfect pairing

A perfect pairing `p : M →ₗ[R] N →ₗ[R] R` identifies `M` with the dual of `N`. When `N` is
finite projective, taking duals commutes with scalar extension along any commutative `R`-algebra
`A` (`TauCeti.Module.Dual.baseChangeEvaluationEquiv`), so `p` extends to a perfect pairing
between `A ⊗[R] M` and `A ⊗[R] N`, given on pure tensors by
`⟨a ⊗ x, b ⊗ y⟩ = a * b * algebraMap R A (p x y)`.

This is the pairing carried by the scalar extension of a root pairing, for instance the rational
root system `ℚ ⊗[ℤ] X`, `ℚ ⊗[ℤ] Y` of an integral root datum.

## Main definitions

* `LinearMap.toPerfPairBaseChange`: the scalar extension of a perfect pairing, as an equivalence
  of `A ⊗[R] M` onto the dual of `A ⊗[R] N`.

## Main results

* `LinearMap.toPerfPairBaseChange_tmul_tmul`: its value on two pure tensors.

The underlying bilinear map of `LinearMap.toPerfPairBaseChange` is again a perfect pairing, by
Mathlib's instance making the linear map underlying an equivalence onto a dual a perfect pairing.
-/

public section

open Module
open scoped TensorProduct

namespace LinearMap

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] (A : Type*) [CommSemiring A] [Algebra R A]
  (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair] [Module.Finite R N] [Module.Projective R N]

/-- **The scalar extension of a perfect pairing.** For a perfect pairing `p` between `M` and a
finite projective module `N`, the equivalence `A ⊗[R] M ≃ₗ[A] Dual A (A ⊗[R] N)` obtained by
extending `p.toPerfPair : M ≃ₗ[R] Dual R N` to `A` and identifying `A ⊗[R] Dual R N` with the dual
of `A ⊗[R] N`. -/
noncomputable def toPerfPairBaseChange : A ⊗[R] M ≃ₗ[A] Dual A (A ⊗[R] N) :=
  (p.toPerfPair.baseChange R A _ _).trans TauCeti.Module.Dual.baseChangeEvaluationEquiv

/-- The scalar extension of a perfect pairing on pure tensors:
`⟨a ⊗ x, b ⊗ y⟩ = a * b * algebraMap R A (p x y)`. -/
@[simp]
theorem toPerfPairBaseChange_tmul_tmul (a b : A) (x : M) (y : N) :
    p.toPerfPairBaseChange A (a ⊗ₜ x) (b ⊗ₜ y) = a * b * algebraMap R A (p x y) := by
  simp [toPerfPairBaseChange]

end LinearMap

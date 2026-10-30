/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# The derivation action of an endomorphism on two-vectors

An endomorphism `A` of a module `M` acts on `⋀² M` as a derivation,
`D_A (u ∧ w) = A u ∧ w + u ∧ A w`. This is the infinitesimal form of the functoriality
`⋀² (exp (t A))`, and it is how a Lie algebra of endomorphisms of `M`, such as the skew-adjoint
endomorphisms of an inner product space, acts on two-forms. Here it is obtained by polarizing
Mathlib's `exteriorPower.map`: since `(u + A u) ∧ (w + A w) = u ∧ w + D_A (u ∧ w) + A u ∧ A w`,
`D_A = ⋀² (1 + A) - 1 - ⋀² A`.

## Main definitions

* `LinearMap.exteriorSquareDerivation A`: the derivation action `D_A` of `A` on `⋀² M`.

## Main results

* `LinearMap.exteriorSquareDerivation_ιMulti`: `D_A (u ∧ w) = A u ∧ w + u ∧ A w`.
-/

public section

noncomputable section

open exteriorPower

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The derivation action of an endomorphism `A` on two-vectors,
`D_A (u ∧ w) = A u ∧ w + u ∧ A w` (`LinearMap.exteriorSquareDerivation_ιMulti`). It is defined by
polarizing the functoriality of `⋀²`: `D_A = ⋀² (1 + A) - 1 - ⋀² A`. -/
def exteriorSquareDerivation (A : M →ₗ[R] M) : ⋀[R]^2 M →ₗ[R] ⋀[R]^2 M :=
  exteriorPower.map 2 (LinearMap.id + A) - LinearMap.id - exteriorPower.map 2 A

/-- **The derivation rule**: `D_A (u ∧ w) = A u ∧ w + u ∧ A w`. -/
@[simp]
theorem exteriorSquareDerivation_ιMulti (A : M →ₗ[R] M) (u w : M) :
    A.exteriorSquareDerivation (ιMulti R 2 ![u, w]) =
      ιMulti R 2 ![A u, w] + ιMulti R 2 ![u, A w] := by
  apply Subtype.ext
  simp [exteriorSquareDerivation, exteriorPower.map_apply_ιMulti, ExteriorAlgebra.ιMulti_apply,
    Function.comp_def, Matrix.vecTail, add_mul, mul_add]
  abel

end LinearMap

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Base change of the antipode

Let `H` be a Hopf algebra over a commutative semiring `R`, and `A` a commutative `R`-algebra, so
that `A ⊗[R] H` is an `A`-Hopf algebra. For an `R`-linear map `f : A → B` between two such
algebras, in particular for an `R`-algebra map, the map `f ⊗ id : A ⊗[R] H → B ⊗[R] H` commutes
with the antipodes. So does the cancellation `A ⊗[R'] (R' ⊗[R] H) ≃ A ⊗[R] H` of an intermediate
base change, for an `R`-algebra `R'` and an `R'`-algebra `A`.

## Main results

* `TensorProduct.antipode_rTensor`: the antipode of `B ⊗[R] H` on the image of `x ∈ A ⊗[R] H` is
  the image of the antipode of `x`.
* `TensorProduct.AlgebraTensorModule.antipode_cancelBaseChange`: cancelling an intermediate base
  change, `A ⊗[R'] (R' ⊗[R] H) ≃ A ⊗[R] H`, commutes with the antipodes.
-/

public section

open HopfAlgebra

namespace TensorProduct

variable {R A B H : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [CommSemiring B]
  [Algebra R B] (f : A →ₗ[R] B)

/-- For an `R`-linear map `f : A → B`, the map `f ⊗ id : A ⊗[R] H → B ⊗[R] H` commutes with the
antipodes. -/
theorem antipode_rTensor [Semiring H] [HopfAlgebra R H] (x : A ⊗[R] H) :
    antipode B (f.rTensor H x) = f.rTensor H (antipode A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a h => simp
  | add x y hx hy => simp only [map_add, hx, hy]

namespace AlgebraTensorModule

variable {R' : Type*} [CommSemiring R'] [Algebra R R'] [Algebra R' A] [IsScalarTower R R' A]

/-- Cancelling the intermediate base change, `A ⊗[R'] (R' ⊗[R] H) ≃ A ⊗[R] H`, commutes with the
antipodes of the two scalar extensions to `A`. -/
theorem antipode_cancelBaseChange [Semiring H] [HopfAlgebra R H] (x : A ⊗[R'] (R' ⊗[R] H)) :
    antipode A (cancelBaseChange R R' A A H x) = cancelBaseChange R R' A A H (antipode A x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a y =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
    | tmul r h => simp

end AlgebraTensorModule

end TensorProduct

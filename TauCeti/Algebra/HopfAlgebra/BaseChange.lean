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
that `A ⊗[R] H` is an `A`-Hopf algebra. For an `R`-algebra map `f : A → B`, the map
`f ⊗ id : A ⊗[R] H → B ⊗[R] H` commutes with the antipodes.

## Main results

* `TensorProduct.antipode_rTensor`: the antipode of `B ⊗[R] H` on the image of `x ∈ A ⊗[R] H` is
  the image of the antipode of `x`.
-/

public section

open HopfAlgebra

namespace TensorProduct

variable {R A B H : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [CommSemiring B]
  [Algebra R B] (f : A →ₐ[R] B)

/-- The map `f ⊗ id : A ⊗[R] H → B ⊗[R] H` commutes with the antipodes. -/
theorem antipode_rTensor [Semiring H] [HopfAlgebra R H] (x : A ⊗[R] H) :
    antipode B (f.toLinearMap.rTensor H x) = f.toLinearMap.rTensor H (antipode A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a h => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end TensorProduct

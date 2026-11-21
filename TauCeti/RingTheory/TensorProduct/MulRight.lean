/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Multiplication by a pure tensor with one factor `1`

In the tensor product `A ⊗[R] B` of `R`-algebras, right multiplication by `a ⊗ₜ 1` is the
tensor product of right multiplication by `a` on `A` with the identity of `B`
(`LinearMap.rTensor_mulRight_apply`). Together with flatness of `B` this transfers injectivity of
multiplication by `a` from `A` to `A ⊗[R] B`.
-/

public section

open scoped TensorProduct

namespace LinearMap

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- Right multiplication by `a ⊗ₜ 1` in `A ⊗[R] B` is the tensor product of right multiplication
by `a` with the identity of `B`. -/
theorem rTensor_mulRight_apply (a : A) (x : A ⊗[R] B) :
    (LinearMap.mulRight R a).rTensor B x = x * (a ⊗ₜ[R] 1) := by
  simpa [LinearMap.mulRight_one, LinearMap.rTensor_def] using
    (LinearMap.congr_fun (LinearMap.mulRight_tmul (R := R) a (1 : B)) x).symm

end LinearMap

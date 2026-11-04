/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finiteness of tensor products over a larger scalar ring

Let `S` be an `R`-algebra, `M` a finite `S`-module and `N` a finite `R`-module. Then `M ⊗[R] N`,
with `S` acting through `M`, is a finite `S`-module. This is the finiteness counterpart of
Mathlib's `Module.Free.tensor`; Mathlib's `Module.Finite.tensorProduct` is the case `S = R` and
`Module.Finite.base_change` the case `M = S`.

## Main results

* `Module.Finite.tensor`: `M ⊗[R] N` is finite over `S`.
-/

public section

open TensorProduct

namespace Module.Finite

variable {R S M N : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
  [Module R M] [Module S M] [IsScalarTower R S M] [AddCommMonoid N] [Module R N]

/-- The tensor product of a finite `S`-module with a finite `R`-module is a finite `S`-module. -/
instance tensor [Module.Finite S M] [Module.Finite R N] : Module.Finite S (M ⊗[R] N) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  exact .of_surjective ((AlgebraTensorModule.lTensor S M f) ∘ₗ
    (TensorProduct.piScalarRight R S M (Fin n)).symm.toLinearMap)
    ((LinearMap.lTensor_surjective M hf).comp (LinearEquiv.surjective _))

end Module.Finite

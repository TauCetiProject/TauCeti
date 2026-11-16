/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Tensor products of coalgebras

This file records the counit of a tensor product of coalgebras in terms of
`TensorProduct.dualDistrib`.

## Main declarations

* `TauCeti.Coalgebra.tensorProduct_counit`: the counit of `M ⊗[R] N` is
  `TensorProduct.dualDistrib R M N` applied to the tensor product of the counits.
-/

public section

open scoped TensorProduct

namespace TauCeti.Coalgebra

/-- The counit of a tensor product of coalgebras `M ⊗[R] N` is `TensorProduct.dualDistrib R M N`
applied to the tensor product of their counits. -/
theorem tensorProduct_counit {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [CoalgebraStruct R M]
    [AddCommMonoid N] [Module R N] [CoalgebraStruct R N] :
    Coalgebra.counit (R := R) (A := M ⊗[R] N) =
      TensorProduct.dualDistrib R M N
        (Coalgebra.counit (R := R) (A := M) ⊗ₜ[R] Coalgebra.counit (R := R) (A := N)) := by
  ext m n
  simp [mul_comm]

end TauCeti.Coalgebra

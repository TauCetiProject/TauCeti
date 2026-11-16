/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic

/-!
# Products of generators of the tensor algebra

Mathlib's `TensorAlgebra.tprod R M n x` is the product `ι (x 0) * ⋯ * ι (x (n - 1))` of `n`
generators of the tensor algebra.  This file records how such a product splits off its last
generator (`TensorAlgebra.tprod_succ`), the step of inductions on the length of the product.
-/

public section

namespace TensorAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A product of `n + 1` generators of the tensor algebra is the product of the first `n` of them
times the last one. -/
theorem tprod_succ {n : ℕ} (x : Fin (n + 1) → M) :
    tprod R M (n + 1) x = tprod R M n (fun i ↦ x i.castSucc) * ι R (x (Fin.last n)) := by
  rw [tprod_apply, tprod_apply, List.ofFn_succ', List.prod_concat]

end TensorAlgebra

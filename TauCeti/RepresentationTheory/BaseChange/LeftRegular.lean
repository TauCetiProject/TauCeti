/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange

/-!
# Base change of the left regular representation

For an `R`-algebra `A` and a monoid `G`, `TauCeti.baseChangeOfMulActionEquiv` identifies the base
change `A ⊗_R R[G]` of the left regular representation with `A[G]`. On the pure tensors `1 ⊗ x`
it is the extension of the coefficients of `x` along the structure map `R → A`.

## Main results

* `TauCeti.baseChangeOfMulActionEquiv_one_tmul`: the identification `A ⊗_R R[G] ≅ A[G]` sends
  `1 ⊗ x` to `x` with its coefficients extended to `A`.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- On `1 ⊗ x` the identification `A ⊗_R R[G] ≅ A[G]` extends the coefficients of `x` along the
structure map `R → A`. -/
theorem baseChangeOfMulActionEquiv_one_tmul {R A G : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [Monoid G] (x : MonoidAlgebra R G) :
    baseChangeOfMulActionEquiv R A G G (1 ⊗ₜ x) =
      MonoidAlgebra.mapAlgHom G (Algebra.ofId R A) x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add]
  | single g r => simp [Algebra.smul_def]

end TauCeti

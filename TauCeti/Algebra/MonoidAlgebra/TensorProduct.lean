/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Tensor products with monoid algebras

This file records the standard linear identification of a tensor product with a monoid algebra
as a space of finitely supported functions.

## Main definitions

* `TauCeti.MonoidAlgebra.tensorEquivFinsupp`: the equivalence
  `k[G] ⊗ W ≃ₗ G →₀ W`.

## Main results

* `TauCeti.MonoidAlgebra.tensorEquivFinsupp_single_tmul` and
  `TauCeti.MonoidAlgebra.tensorEquivFinsupp_symm_single`: the equivalence and its inverse on
  generators.
-/

public section

open scoped TensorProduct

noncomputable section

namespace TauCeti.MonoidAlgebra

variable {k G W : Type*} [CommSemiring k] [AddCommMonoid W] [Module k W]

variable (k G W) in
/-- The standard identification `k[G] ⊗ W ≃ₗ G →₀ W`, sending `single g r ⊗ₜ w` to
`Finsupp.single g (r • w)`. -/
def tensorEquivFinsupp : _root_.MonoidAlgebra k G ⊗[k] W ≃ₗ[k] G →₀ W := by
  classical
  exact TensorProduct.congr (_root_.MonoidAlgebra.coeffLinearEquiv k) (.refl k W) ≪≫ₗ
    TensorProduct.finsuppScalarLeft k W G

/-- The tensor/Finsupp equivalence sends a pure tensor supported at `g` to a Finsupp supported
at `g`. -/
@[simp]
theorem tensorEquivFinsupp_single_tmul (g : G) (r : k) (w : W) :
    tensorEquivFinsupp k G W (_root_.MonoidAlgebra.single g r ⊗ₜ[k] w) =
      Finsupp.single g (r • w) := by
  simp [tensorEquivFinsupp, TensorProduct.finsuppScalarLeft_apply_tmul]

/-- The inverse of the tensor/Finsupp equivalence sends a Finsupp supported at `g` to a pure
tensor supported at `g`. -/
@[simp]
theorem tensorEquivFinsupp_symm_single (g : G) (w : W) :
    (tensorEquivFinsupp k G W).symm (Finsupp.single g w) =
      _root_.MonoidAlgebra.single g (1 : k) ⊗ₜ[k] w := by
  simp [LinearEquiv.symm_apply_eq]

end TauCeti.MonoidAlgebra

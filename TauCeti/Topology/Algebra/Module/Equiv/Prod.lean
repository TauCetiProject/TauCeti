/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# The linear equivalence underlying a product of continuous linear equivalences

Mathlib records the linear equivalences underlying `ContinuousLinearEquiv.prodComm` and
`ContinuousLinearEquiv.prodAssoc`. This file adds the matching lemma for
`ContinuousLinearEquiv.prodCongr`: it is built from `LinearEquiv.prodCongr`.
-/

public section

namespace ContinuousLinearEquiv

variable {R : Type*} [Semiring R]
  {M₁ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R M₄]

/-- The linear equivalence underlying `e.prodCongr e'` is the product of those underlying `e`
and `e'`. -/
@[simp]
theorem prodCongr_toLinearEquiv (e : M₁ ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) :
    (e.prodCongr e').toLinearEquiv = e.toLinearEquiv.prodCongr e'.toLinearEquiv :=
  (rfl)

end ContinuousLinearEquiv

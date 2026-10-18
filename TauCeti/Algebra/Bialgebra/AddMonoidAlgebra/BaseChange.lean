/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# Base change of additive monoid bialgebras

Scalar extension of `R[M]` is `S[M]`, compatibly with the standard bialgebra structures.
For `M = ℤ` this identifies scalar extension of the Laurent coordinate algebra of the
multiplicative group with the Laurent coordinate algebra over the new base.

This is the additive-monoid counterpart of
`TauCeti.MonoidAlgebra.scalarTensorBialgEquiv`, using Mathlib's
`AddMonoidAlgebra.scalarTensorEquiv` for the underlying algebra equivalence.
-/

public section

open TensorProduct

namespace AddMonoidAlgebra

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
variable {M : Type*} [AddCommMonoid M]

/-- Scalar extension of an additive monoid bialgebra is the additive monoid bialgebra
over the extended scalars. -/
noncomputable def scalarTensorBialgEquiv :
    S ⊗[R] _root_.AddMonoidAlgebra R M ≃ₐc[S] _root_.AddMonoidAlgebra S M :=
  BialgEquiv.ofAlgEquiv (_root_.AddMonoidAlgebra.scalarTensorEquiv R S)
    (by ext m; simp) (by ext m; simp)

/-- On pure tensors, the comparison extends coefficients and multiplies by the scalar. -/
@[simp]
theorem scalarTensorBialgEquiv_tmul (s : S) (p : _root_.AddMonoidAlgebra R M) :
    scalarTensorBialgEquiv R S (s ⊗ₜ[R] p) =
      s • _root_.AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R S) p := by
  rw [scalarTensorBialgEquiv, BialgEquiv.ofAlgEquiv_apply]
  exact _root_.AddMonoidAlgebra.scalarTensorEquiv_tmul s p

/-- The inverse comparison sends a monomial to its scalar times the corresponding
unit-coefficient monomial over the original base. -/
@[simp]
theorem scalarTensorBialgEquiv_symm_single (m : M) (s : S) :
    (scalarTensorBialgEquiv R S).symm (_root_.AddMonoidAlgebra.single m s) =
      s ⊗ₜ[R] _root_.AddMonoidAlgebra.single m (1 : R) := by
  apply EquivLike.injective (scalarTensorBialgEquiv R S (M := M))
  rw [BialgEquiv.apply_symm_apply, scalarTensorBialgEquiv_tmul]
  simp

end AddMonoidAlgebra

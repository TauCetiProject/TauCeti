/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Bialgebra maps into tensor products

This file packages the canonical maps `x ↦ x ⊗ₜ 1` and `y ↦ 1 ⊗ₜ y` into a tensor product
of bialgebras as bialgebra morphisms, and records their underlying algebra maps.

The tensor-product bialgebra structure and its unit isomorphisms are from Mathlib's
`Mathlib.RingTheory.Bialgebra.TensorProduct`.
-/

open TensorProduct

namespace TauCeti

namespace Bialgebra.TensorProduct

variable {R H₁ H₂ : Type*} [CommSemiring R]
variable [Semiring H₁] [Semiring H₂] [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂]

/-- The left inclusion `x ↦ x ⊗ₜ 1` of a bialgebra into a tensor product of bialgebras,
packaged as a bialgebra morphism. It is the unit `R →ₐc[R] H₂` tensored on the right with `H₁`,
precomposed with the right-unit isomorphism `H₁ ≃ₐc[R] H₁ ⊗[R] R`. -/
noncomputable def includeLeft : H₁ →ₐc[R] H₁ ⊗[R] H₂ :=
  (_root_.Bialgebra.TensorProduct.map (BialgHom.id R H₁) (_root_.Bialgebra.unitBialgHom R H₂)).comp
    (_root_.Bialgebra.TensorProduct.rid R R H₁).symm.toBialgHom

/-- The right inclusion `y ↦ 1 ⊗ₜ y` of a bialgebra into a tensor product of bialgebras,
packaged as a bialgebra morphism. It is the unit `R →ₐc[R] H₁` tensored on the left with `H₂`,
precomposed with the left-unit isomorphism `H₂ ≃ₐc[R] R ⊗[R] H₂`. -/
noncomputable def includeRight : H₂ →ₐc[R] H₁ ⊗[R] H₂ :=
  (_root_.Bialgebra.TensorProduct.map (_root_.Bialgebra.unitBialgHom R H₁) (BialgHom.id R H₂)).comp
    (_root_.Bialgebra.TensorProduct.lid R H₂).symm.toBialgHom

@[simp]
theorem includeLeft_apply (x : H₁) : includeLeft (H₂ := H₂) x = x ⊗ₜ[R] (1 : H₂) := by
  simp [includeLeft, _root_.Bialgebra.unitBialgHom, Algebra.ofId_apply]

@[simp]
theorem includeRight_apply (y : H₂) : includeRight (H₁ := H₁) y = (1 : H₁) ⊗ₜ[R] y := by
  simp [includeRight, _root_.Bialgebra.unitBialgHom, Algebra.ofId_apply]

@[simp]
theorem includeLeft_toAlgHom :
    (includeLeft : H₁ →ₐc[R] H₁ ⊗[R] H₂).toAlgHom = Algebra.TensorProduct.includeLeft := by
  ext x
  simp only [BialgHom.coe_toAlgHom, includeLeft_apply, Algebra.TensorProduct.includeLeft_apply]

@[simp]
theorem includeRight_toAlgHom :
    (includeRight : H₂ →ₐc[R] H₁ ⊗[R] H₂).toAlgHom = Algebra.TensorProduct.includeRight := by
  ext y
  simp only [BialgHom.coe_toAlgHom, includeRight_apply, Algebra.TensorProduct.includeRight_apply]

end Bialgebra.TensorProduct

end TauCeti

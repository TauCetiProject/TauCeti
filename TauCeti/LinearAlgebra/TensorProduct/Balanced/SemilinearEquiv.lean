/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Extension

/-!
# Balanced extension of a semilinear equivalence

A semilinear equivalence over a ring isomorphism identifies the extension of scalars of its
source with its target.
-/

public section

noncomputable section

open TauCeti

namespace LinearEquiv

variable {R S P Q : Type*} [Ring R] [Ring S] [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module S Q] {σ : R →+* S} {τ : S →+* R}
  [RingHomInvPair σ τ] [RingHomInvPair τ σ]

/-- The linear equivalence induced by extending scalars along the ring isomorphism of a
semilinear equivalence. It sends `s ⊗ p` to `s • e p`. -/
def balancedExtension (e : P ≃ₛₗ[σ] Q) : BalancedExtension σ P ≃ₗ[S] Q :=
  LinearEquiv.ofLinearMap (BalancedExtension.lift e.toLinearMap)
    ((BalancedExtension.includeRight σ P).comp e.symm.toLinearMap)
    (by ext q; simp) (BalancedExtension.hom_ext fun p ↦ by simp)

/-- The extended equivalence on a pure tensor. -/
@[simp]
theorem balancedExtension_tmul (e : P ≃ₛₗ[σ] Q) (s : S) (p : P) :
    e.balancedExtension (BalancedExtension.tmul σ s p) = s • e p :=
  BalancedExtension.lift_tmul e.toLinearMap s p

/-- The inverse of the extended equivalence sends `q` to `1 ⊗ e⁻¹ q`. -/
@[simp]
theorem balancedExtension_symm_apply (e : P ≃ₛₗ[σ] Q) (q : Q) :
    e.balancedExtension.symm q = BalancedExtension.tmul σ 1 (e.symm q) :=
  BalancedExtension.includeRight_apply _

end LinearEquiv

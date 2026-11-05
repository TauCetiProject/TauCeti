/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PicardGroup

/-!
# Cancelling an invertible module against its dual

An invertible module `M` cancels against its dual: the contraction `ℓ ⊗ ξ ↦ ξ ℓ` is an
isomorphism `M ⊗ M^* ≃ R` (`Module.Invertible.linearEquiv`). Tensoring on the left with
`M ⊗ M^*` therefore gives the isomorphism `M ⊗ (M^* ⊗ P) ≃ P`
(`Module.Invertible.leftCancelDualEquiv`), the special case of Mathlib's
`Module.Invertible.leftCancelEquiv` for the dual of `M`.

When `P = N^*` is itself a dual, the isomorphism is evaluation of the tensor product of
functionals: `M^* ⊗ N^* ≃ (M ⊗ N)^*` by `TensorProduct.dualDistribEquiv`, and the image of
`ℓ ⊗ t` takes the value `t (ℓ ⊗ x)` at `x`
(`Module.Invertible.leftCancelDualEquiv_tmul_apply`). This is how determinant lines of exact
sequences cancel a common factor `det E ⊗ (det E)^*`.

## Main declarations

* `Module.Invertible.leftCancelDualEquiv`: the isomorphism `M ⊗ (M^* ⊗ P) ≃ P`.
* `Module.Invertible.leftCancelDualEquiv_tmul_tmul`: its value `ℓ ⊗ (ξ ⊗ p) ↦ ξ ℓ • p`.
* `Module.Invertible.leftCancelDualEquiv_tmul_apply`: its value on duals.
-/

public section

noncomputable section

open Module TensorProduct

namespace Module.Invertible

variable (R : Type*) [CommSemiring R] (M P : Type*) [AddCommMonoid M] [Module R M]
  [Module.Invertible R M] [AddCommMonoid P] [Module R P]

/-- Cancel an invertible module `M` against its dual in `M ⊗ (M^* ⊗ P)`, by the contraction
`ℓ ⊗ ξ ↦ ξ ℓ`. This is `Module.Invertible.leftCancelEquiv` for the pairing of `M` with its
dual. -/
def leftCancelDualEquiv : M ⊗[R] (Dual R M ⊗[R] P) ≃ₗ[R] P :=
  leftCancelEquiv P (TensorProduct.comm R M (Dual R M) ≪≫ₗ linearEquiv R M)

variable {R M P}

/-- `Module.Invertible.leftCancelDualEquiv` sends `ℓ ⊗ (ξ ⊗ p)` to `ξ ℓ • p`. -/
@[simp]
theorem leftCancelDualEquiv_tmul_tmul (ℓ : M) (ξ : Dual R M) (p : P) :
    leftCancelDualEquiv R M P (ℓ ⊗ₜ (ξ ⊗ₜ p)) = ξ ℓ • p := by
  simp [leftCancelDualEquiv, linearEquiv]

/-- On a dual `P = N^*`, `Module.Invertible.leftCancelDualEquiv` evaluates the tensor product of
functionals: the image of `ℓ ⊗ t` takes the value `t (ℓ ⊗ x)` at `x`, with `t` read as a
functional on `M ⊗ N` through `TensorProduct.dualDistribEquiv`. -/
theorem leftCancelDualEquiv_tmul_apply {N : Type*} [AddCommMonoid N] [Module R N]
    [Module.Finite R N] [Projective R N] (ℓ : M) (t : Dual R M ⊗[R] Dual R N) (x : N) :
    leftCancelDualEquiv R M (Dual R N) (ℓ ⊗ₜ t) x = dualDistribEquiv R M N t (ℓ ⊗ₜ x) := by
  induction t using TensorProduct.inductionOn with
  | tmul ξ η => simp [mul_comm]
  | add t₁ t₂ h₁ h₂ =>
    rw [TensorProduct.tmul_add, map_add, LinearMap.add_apply, h₁, h₂, map_add,
      LinearMap.add_apply]

end Module.Invertible

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

A free module of rank one, in particular a line over a field, is invertible
(`Module.Invertible.of_finrank_eq_one`). In an invertible module, a vector `x` and a functional
`ξ` with `ξ x = 1` are dual bases of `M` and of its dual: every vector `y` is `ξ y • x` and every
functional `η` is `η x • ξ`. Consequently an element of `W ⊗ M^*` is the pure tensor of its
evaluation at `x` with `ξ`. This is how an identity of determinant lines stated by evaluating a
dual factor is turned into an identity of pure tensors.

## Main declarations

* `Module.Invertible.of_finrank_eq_one`: a free module of rank one is invertible.
* `Module.Invertible.linearEquiv_tmul`: the value `ξ ⊗ ℓ ↦ ξ ℓ` of the contraction.
* `Module.Invertible.toLinearMap_linearEquiv`: the contraction is Mathlib's `contractLeft`.
* `Module.Invertible.leftCancelDualEquiv`: the isomorphism `M ⊗ (M^* ⊗ P) ≃ P`.
* `Module.Invertible.leftCancelDualEquiv_tmul_tmul`: its value `ℓ ⊗ (ξ ⊗ p) ↦ ξ ℓ • p`.
* `Module.Invertible.leftCancelDualEquiv_tmul_apply`: its value on duals.
* `Module.Invertible.apply_smul_eq_self`, `Module.Invertible.dual_apply_smul_eq_self`: the
  expansions `ξ y • x = y` and `η x • ξ = η` for `ξ x = 1`.
* `Module.Invertible.rid_lTensor_eval_tmul_eq_self`: an element of `W ⊗ M^*` is the pure tensor
  of its evaluation at `x` with `ξ`.
-/

public section

noncomputable section

open Module TensorProduct

namespace Module.Invertible

/-- **A free module of rank one is invertible.** In particular, for a line `V` over a field `k`
the contraction `V^* ⊗ V → k`, `f ⊗ v ↦ f v`, is an isomorphism. -/
theorem of_finrank_eq_one {R M : Type*} [CommSemiring R] [StrongRankCondition R]
    [AddCommMonoid M] [Module R M] [Module.Free R M] (h : finrank R M = 1) :
    Module.Invertible R M :=
  haveI := Module.finite_of_finrank_eq_succ h
  .congr (LinearEquiv.ofFinrankEq R M (by rw [finrank_self, h]))

variable (R : Type*) [CommSemiring R] (M P : Type*) [AddCommMonoid M] [Module R M]
  [Module.Invertible R M] [AddCommMonoid P] [Module R P]

/-- Cancel an invertible module `M` against its dual in `M ⊗ (M^* ⊗ P)`, by the contraction
`ℓ ⊗ ξ ↦ ξ ℓ`. This is `Module.Invertible.leftCancelEquiv` for the pairing of `M` with its
dual. -/
def leftCancelDualEquiv : M ⊗[R] (Dual R M ⊗[R] P) ≃ₗ[R] P :=
  leftCancelEquiv P (TensorProduct.comm R M (Dual R M) ≪≫ₗ linearEquiv R M)

variable {R M P}

/-- `Module.Invertible.linearEquiv` is the contraction `ξ ⊗ ℓ ↦ ξ ℓ`. -/
@[simp]
theorem linearEquiv_tmul (ξ : Dual R M) (ℓ : M) : linearEquiv R M (ξ ⊗ₜ ℓ) = ξ ℓ := by
  simp [linearEquiv]

/-- The underlying linear map of `Module.Invertible.linearEquiv` is Mathlib's contraction
`contractLeft R M`. -/
@[simp]
theorem toLinearMap_linearEquiv :
    (linearEquiv R M : Dual R M ⊗[R] M →ₗ[R] R) = contractLeft R M :=
  TensorProduct.ext' fun ξ ℓ ↦ by simp

/-- `Module.Invertible.leftCancelDualEquiv` sends `ℓ ⊗ (ξ ⊗ p)` to `ξ ℓ • p`. -/
@[simp]
theorem leftCancelDualEquiv_tmul_tmul (ℓ : M) (ξ : Dual R M) (p : P) :
    leftCancelDualEquiv R M P (ℓ ⊗ₜ (ξ ⊗ₜ p)) = ξ ℓ • p := by
  simp [leftCancelDualEquiv]

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

section DualPair

variable {x : M} {ξ : Dual R M} (hξ : ξ x = 1)
include hξ

/-- In an invertible module, a vector `x` and a functional `ξ` with `ξ x = 1` are dual bases:
every vector `y` is `ξ y • x`. -/
theorem apply_smul_eq_self (y : M) : ξ y • x = y := by
  have h : ξ ⊗ₜ[R] (ξ y • x) = ξ ⊗ₜ y := (linearEquiv R M).injective (by simp [hξ])
  simpa [hξ] using congr(TensorProduct.lid R M ((Dual.eval R M x).rTensor M $h))

/-- In an invertible module, a vector `x` and a functional `ξ` with `ξ x = 1` are dual bases:
every functional `η` is `η x • ξ`. -/
theorem dual_apply_smul_eq_self (η : Dual R M) : η x • ξ = η := by
  ext y
  conv_rhs => rw [← apply_smul_eq_self hξ y]
  simp [mul_comm]

/-- In `W ⊗ M^*` for an invertible module `M`, with `ξ x = 1`, every element `X` is the pure
tensor of its evaluation at `x` with `ξ`. -/
theorem rid_lTensor_eval_tmul_eq_self {W : Type*} [AddCommMonoid W] [Module R W]
    (X : W ⊗[R] Dual R M) :
    TensorProduct.rid R W ((Dual.eval R M x).lTensor W X) ⊗ₜ ξ = X := by
  induction X using TensorProduct.inductionOn with
  | tmul w η =>
    rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Dual.eval_apply,
      TensorProduct.smul_tmul, dual_apply_smul_eq_self hξ]
  | add X Y hX hY => rw [map_add, map_add, TensorProduct.add_tmul, hX, hY]

end DualPair

end Module.Invertible

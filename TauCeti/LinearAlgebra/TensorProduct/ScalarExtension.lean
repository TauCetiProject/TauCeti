/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Cancelling scalar extension on the right

The canonical identification `(E ⊗[K] L) ⊗[L] V ≃ E ⊗[K] V` is linear over `E`, although
`L` acts on the right component of the scalar-extended algebra. This identification compares
scalar extension of an underlying `K`-module with scalar extension of an `L`-module, and is used
when a construction over `L/K` is transported along `K → E`.

The construction uses Mathlib's `Algebra.TensorProduct.commRight`,
`TensorProduct.AlgebraTensorModule.cancelBaseChange`, and `TensorProduct.comm`.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable (K L E V : Type*) [CommSemiring K] [CommSemiring L] [CommSemiring E]
  [Algebra K L] [Algebra K E] [AddCommMonoid V] [Module L V] [Module K V]
  [IsScalarTower K L V]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Cancelling the scalar-extended algebra identifies extension of an `L`-module with extension
of its underlying `K`-module. The map sends `(e ⊗ l) ⊗ v` to `e ⊗ (l • v)`. -/
def _root_.TensorProduct.cancelBaseChangeRight :
    ((E ⊗[K] L) ⊗[L] V) ≃ₗ[E] E ⊗[K] V := by
  let f := (TensorProduct.comm L (E ⊗[K] L) V).restrictScalars K
    ≪≫ₗ (TensorProduct.congr (LinearEquiv.refl L V)
      (Algebra.TensorProduct.commRight K L E).symm.toLinearEquiv).restrictScalars K
    ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange K L L V E).restrictScalars K
    ≪≫ₗ TensorProduct.comm K V E
  refine { f.toAddEquiv with map_smul' := ?_ }
  intro c x
  -- Normalize the additive equivalence's `toFun` field before tensor induction.
  change f (c • x) = c • f x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [smul_add, hx, hy]
  | tmul a v =>
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp [TensorProduct.add_tmul, smul_add, ha, hb]
    | tmul e l => simp [f, TensorProduct.smul_tmul']

/-- The cancellation equivalence acts by the `L`-scalar on the vector component. -/
@[simp]
theorem _root_.TensorProduct.cancelBaseChangeRight_tmul (e : E) (l : L) (v : V) :
    TensorProduct.cancelBaseChangeRight K L E V ((e ⊗ₜ[K] l) ⊗ₜ[L] v) =
      e ⊗ₜ[K] (l • v) := (rfl)

/-- The inverse cancellation inserts the unit of `L` in the scalar-extended algebra. -/
@[simp]
theorem _root_.TensorProduct.cancelBaseChangeRight_symm_tmul (e : E) (v : V) :
    (TensorProduct.cancelBaseChangeRight K L E V).symm (e ⊗ₜ[K] v) =
      (e ⊗ₜ[K] (1 : L)) ⊗ₜ[L] v := (rfl)

end TauCeti

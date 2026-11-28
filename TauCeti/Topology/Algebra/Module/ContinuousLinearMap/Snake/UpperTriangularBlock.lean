/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Snake.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.UpperTriangularBlock

/-!
# Connecting map of the upper-triangular block snake diagram

Specializing the continuous snake connecting map `Function.Exact.snakeδL` to the split product rows
for `ContinuousLinearMap.upperTriangularBlock A B D` yields
`ContinuousLinearMap.snakeδL_upperTriangularBlock_eq`: `y ∈ ker D` is sent to the class of `B y`
modulo `range A`.
-/

public section

namespace ContinuousLinearMap

variable {R E₁ E₂ F₁ F₂ : Type*} [Ring R]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module R E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁] [ContinuousAdd F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module R F₂]

/-- In the split product snake diagram for `upperTriangularBlock A B D`, the continuous connecting
map `ker D →L[R] F₁ ⧸ range A` sends `y ∈ ker D` to the class of `B y` modulo `range A`. -/
theorem snakeδL_upperTriangularBlock_eq
    (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂)
    {σ : E₂ →L[R] E₁ × E₂} (hσ : Function.RightInverse σ (snd R E₁ E₂))
    {ρ : F₁ × F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ (inl R F₁ F₂)) :
    (Function.Exact.inl_snd).snakeδL .inl_snd
      (A.upperTriangularBlock_comp_inl B D).symm (A.snd_comp_upperTriangularBlock B D) hσ hρ =
        A.range.mkQL ∘L B ∘L D.ker.subtypeL := by
  ext y
  exact Function.Exact.snakeδL_eq _ _ _ _ hσ hρ y (inr R E₁ E₂ y) (B y) rfl (by simp)

end ContinuousLinearMap

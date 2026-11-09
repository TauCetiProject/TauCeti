/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Contraction of a line

For a one-dimensional vector space `V`, Mathlib's contraction `contractLeft k V : Dual V ⊗ V → k`,
`f ⊗ v ↦ f v`, is a linear equivalence.

A vector `x` and a functional `ξ` of a line with `ξ x = 1` are dual bases of `V` and of its dual:
every vector `y` is `ξ y • x` and every functional `η` is `η x • ξ`. Consequently an element of
`W ⊗ V^*` is the pure tensor of its evaluation at `x` with `ξ`. This is how an identity of
determinant lines stated by evaluating a dual factor is turned into an identity of pure tensors.

## Main declarations

* `TauCeti.contractLeftEquivOfFinrankEqOne`: the contraction `Dual V ⊗ V ≃ k` of a line.
* `TauCeti.contractLeftEquivOfFinrankEqOne_tmul`: its value `f ⊗ v ↦ f v` on a pure tensor.
* `TauCeti.toLinearMap_contractLeftEquivOfFinrankEqOne`: its underlying linear map is
  `contractLeft k V`.
* `TauCeti.apply_smul_eq_self_of_finrank_eq_one`,
  `TauCeti.dual_apply_smul_eq_self_of_finrank_eq_one`: the expansions `ξ y • x = y` and
  `η x • ξ = η` in a line, for `ξ x = 1`.
* `TauCeti.rid_lTensor_eval_tmul_eq_self_of_finrank_eq_one`: an element of `W ⊗ V^*` is the pure
  tensor of its evaluation at `x` with `ξ`.
-/

public section

namespace TauCeti

open Module (finrank)

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- **The contraction of a line is an equivalence.** For `finrank k V = 1`, the contraction
`Dual V ⊗ V ≃ k`, `f ⊗ v ↦ f v` (`TauCeti.contractLeftEquivOfFinrankEqOne_tmul`). It is the tensor
product of the coordinate maps `f ↦ f (b 0)` and `v ↦ b.coord 0 v` for a basis `b` of `V`. -/
noncomputable def contractLeftEquivOfFinrankEqOne (h : finrank k V = 1) :
    TensorProduct k (Module.Dual k V) V ≃ₗ[k] k :=
  haveI : FiniteDimensional k V := Module.finite_of_finrank_eq_succ h
  let b := Module.finBasisOfFinrankEq k V h
  (TensorProduct.congr (b.dualBasis.equivFun.trans (LinearEquiv.funUnique (Fin 1) k k))
    (b.equivFun.trans (LinearEquiv.funUnique (Fin 1) k k))).trans (TensorProduct.lid k k)

@[simp]
theorem contractLeftEquivOfFinrankEqOne_tmul (h : finrank k V = 1) (f : Module.Dual k V)
    (v : V) :
    contractLeftEquivOfFinrankEqOne h (f ⊗ₜ v) = f v := by
  have : FiniteDimensional k V := Module.finite_of_finrank_eq_succ h
  conv_rhs => rw [← (Module.finBasisOfFinrankEq k V h).sum_repr v]
  simp [contractLeftEquivOfFinrankEqOne, mul_comm]

/-- The contraction equivalence of a line is Mathlib's contraction `contractLeft k V`. -/
theorem toLinearMap_contractLeftEquivOfFinrankEqOne (h : finrank k V = 1) :
    (contractLeftEquivOfFinrankEqOne h : TensorProduct k (Module.Dual k V) V →ₗ[k] k) =
      contractLeft k V :=
  TensorProduct.ext' fun f v ↦ by simp

section DualPair

open scoped TensorProduct

variable (h : finrank k V = 1) {x : V} {ξ : Module.Dual k V} (hξ : ξ x = 1)
include h hξ

/-- In a line, a vector `x` and a functional `ξ` with `ξ x = 1` are dual bases: every vector `y` is
`ξ y • x`. -/
theorem apply_smul_eq_self_of_finrank_eq_one (y : V) : ξ y • x = y := by
  have hx : x ≠ 0 := by rintro rfl; simp at hξ
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' x hx).1 h y
  simp [hξ]

/-- In a line, a vector `x` and a functional `ξ` with `ξ x = 1` are dual bases: every functional
`η` is `η x • ξ`. -/
theorem dual_apply_smul_eq_self_of_finrank_eq_one (η : Module.Dual k V) : η x • ξ = η := by
  ext y
  conv_rhs => rw [← apply_smul_eq_self_of_finrank_eq_one h hξ y]
  simp [mul_comm]

/-- In `W ⊗ V^*` for a line `V`, with `ξ x = 1`, every element `X` is the pure tensor of its
evaluation at `x` with `ξ`. -/
theorem rid_lTensor_eval_tmul_eq_self_of_finrank_eq_one {W : Type*} [AddCommGroup W]
    [Module k W] (X : W ⊗[k] Module.Dual k V) :
    TensorProduct.rid k W ((Module.Dual.eval k V x).lTensor W X) ⊗ₜ ξ = X := by
  induction X using TensorProduct.inductionOn with
  | tmul w η =>
    rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Module.Dual.eval_apply,
      TensorProduct.smul_tmul, dual_apply_smul_eq_self_of_finrank_eq_one h hξ]
  | add X Y hX hY => rw [map_add, map_add, TensorProduct.add_tmul, hX, hY]

end DualPair

end TauCeti

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

## Main declarations

* `TauCeti.contractLeftEquivOfFinrankEqOne`: the contraction `Dual V ⊗ V ≃ k` of a line.
* `TauCeti.contractLeftEquivOfFinrankEqOne_tmul`: its value `f ⊗ v ↦ f v` on a pure tensor.
* `TauCeti.toLinearMap_contractLeftEquivOfFinrankEqOne`: its underlying linear map is
  `contractLeft k V`.
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

end TauCeti

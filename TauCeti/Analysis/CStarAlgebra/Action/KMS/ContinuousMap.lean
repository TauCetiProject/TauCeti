/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.KMS.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap

/-!
# `0`-KMS states on algebras of continuous functions

On a commutative C⋆-algebra every state is tracial, hence a `0`-KMS state of every dynamics,
`isKMSState_zero_iff_of_comm`. In particular, for a compact space `X` the evaluation state
`f ↦ f x` on `C(X, ℂ)` is a `0`-KMS state of every real action on `C(X, ℂ)`,
`isKMSState_zero_ofClass_evalStarAlgHom`.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Definition 5.3.1, for the KMS condition at `β = 0`.
-/

public section

open Complex
open scoped ComplexOrder

namespace TauCeti.CStarAction

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Evaluation at a point is a `0`-KMS state of every real action on `C(X, ℂ)`. -/
theorem isKMSState_zero_ofClass_evalStarAlgHom (α : CStarAction (Multiplicative ℝ) C(X, ℂ))
    (x : X) : α.IsKMSState 0 (.ofClass (ContinuousMap.evalStarAlgHom ℂ ℂ x)) := by
  refine isKMSState_zero_iff_of_comm.mpr (ofReal_injective ?_)
  simp [PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one]

end TauCeti.CStarAction

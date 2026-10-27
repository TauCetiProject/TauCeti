/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.ContinuousMap
public import TauCeti.Analysis.CStarAlgebra.Action.KMS.Basic

/-!
# KMS states of the rotation of the circle

On a commutative C⋆-algebra every state is tracial, hence a `0`-KMS state of every dynamics,
`isKMSState_zero_iff_of_comm`. In particular, for a compact space `X` the evaluation state
`f ↦ f x` on `C(X, ℂ)` is a `0`-KMS state of every real action on `C(X, ℂ)`,
`isKMSState_zero_ofClass_evalStarAlgHom`.

For the rotation action of the real line on `C(S¹, ℂ)` the evaluation states are not invariant,
`exists_ofClass_evalStarAlgHom_rotation_ne`. So a `0`-KMS state need not be invariant, in contrast
with `IsKMSState.apply_action` for nonzero inverse temperature.

At nonzero inverse temperature the rotation action has no KMS states at all: the β-KMS states
of `rotation` are exactly the states for `β = 0` and there are none otherwise,
`isKMSState_rotation_iff`. The coordinate function `u(z) = z` satisfies
`α_t(u) = exp (-i t) u`, so it is entire analytic with `α_{iβ}(u) = exp β • u`. Since `u⋆ u = 1`
and multiplication is commutative, the analytic KMS identity `ω (u⋆ α_{iβ}(u)) = ω (u u⋆)` reads
`exp β = 1`.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Definition 5.3.1, for the KMS condition at `β = 0`.
-/

public section

open Complex
open scoped ComplexOrder

namespace TauCeti.CStarAction

open Circle (coordinate coordinate_mul_star star_coordinate_mul)

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Evaluation at a point is a `0`-KMS state of every real action on `C(X, ℂ)`. -/
theorem isKMSState_zero_ofClass_evalStarAlgHom (α : CStarAction (Multiplicative ℝ) C(X, ℂ))
    (x : X) : α.IsKMSState 0 (.ofClass (ContinuousMap.evalStarAlgHom ℂ ℂ x)) := by
  refine isKMSState_zero_iff_of_comm.mpr (ofReal_injective ?_)
  simp [PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one]

open PositiveContinuousLinearMap in
/-- Evaluation states are not invariant under the rotation action, although they are `0`-KMS
states by `isKMSState_zero_ofClass_evalStarAlgHom`. -/
theorem exists_ofClass_evalStarAlgHom_rotation_ne (x : Circle) :
    ∃ t f, ofClass (ContinuousMap.evalStarAlgHom ℂ ℂ x) (rotation t f) ≠
      ofClass (ContinuousMap.evalStarAlgHom ℂ ℂ x) f := by
  refine ⟨.ofAdd Real.pi, coordinate, fun h => ?_⟩
  simp [CharZero.neg_eq_self_iff] at h

/-- **KMS states of the rotation action.** A state of `C(S¹, ℂ)` is a β-KMS state of the rotation
action exactly when `β = 0`: every state is tracial, and there are no β-KMS states for `β ≠ 0`. -/
theorem isKMSState_rotation_iff {β : ℝ} {ω : C(Circle, ℂ) →P[ℂ] ℂ} :
    rotation.IsKMSState β ω ↔ β = 0 ∧ ‖(ω : C(Circle, ℂ) →L[ℂ] ℂ)‖ = 1 := by
  refine ⟨fun hω => ⟨?_, hω.norm_eq_one⟩, fun ⟨hβ, h⟩ => hβ ▸ isKMSState_zero_iff_of_comm.mpr h⟩
  have hω1 : ω 1 = 1 := by
    rw [← PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one, hω.norm_eq_one, ofReal_one]
  have key := hω.apply_mul_entireExtension_mul_I (star coordinate)
    (isEntireAnalytic_of_apply_eq_exp_smul rotation_coordinate)
  rw [entireExtension_eq_exp_smul rotation_coordinate, mul_smul_comm, star_coordinate_mul,
    coordinate_mul_star, map_smul, hω1, smul_eq_mul, mul_one] at key
  -- `key : exp (-i (iβ)) = 1`, and `-i (iβ) = β`
  have hexp : (Real.exp β : ℂ) = 1 := by
    rwa [show -I * (β * I) = β by linear_combination (-(β : ℂ)) * I_sq, ← ofReal_exp] at key
  exact Real.exp_eq_one_iff β |>.mp (mod_cast hexp)

end TauCeti.CStarAction

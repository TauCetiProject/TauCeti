/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.ReturnTime

/-!
# Checks for return times

Checks for `TauCeti.positiveReturnTime`.

* Under the identity every point of `A` returns at time `1`.
* Under the flip of `Bool`, the point `false` returns to `{false}` at time `2`, while it never
  returns to the empty set.
-/

public section

open Set

namespace TauCeti.Examples.ReturnTime

/-- Under the identity, every point of `A` returns to `A` at time `1`. -/
theorem positiveReturnTime_id {X : Type*} {A : Set X} {x : X} (hx : x ∈ A) :
    positiveReturnTime id A x = 1 := by
  rw [← Nat.cast_one, positiveReturnTime_eq_coe_iff one_pos]
  exact ⟨hx, fun i hi hi1 ↦ absurd hi (by omega)⟩

/-- Under the flip of `Bool`, `false` returns to `{false}` at time `2`. -/
theorem positiveReturnTime_not_false :
    positiveReturnTime (fun b : Bool ↦ !b) {false} false = 2 := by
  rw [← Nat.cast_ofNat, positiveReturnTime_eq_coe_iff two_pos]
  refine ⟨rfl, fun i hi hi2 ↦ ?_⟩
  obtain rfl : i = 1 := by omega
  simp

/-- No point returns to the empty set. -/
theorem positiveReturnTime_empty {X : Type*} (T : X → X) (x : X) :
    positiveReturnTime T ∅ x = ⊤ :=
  positiveReturnTime_eq_top_iff.2 fun _ _ ↦ notMem_empty _

end TauCeti.Examples.ReturnTime

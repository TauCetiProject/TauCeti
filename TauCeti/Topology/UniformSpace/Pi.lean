/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Pi

/-!
# Completeness of the factors of a product of uniform spaces

Each factor of a complete product of nonempty uniform spaces is complete
(`CompleteSpace.of_pi`), so such a product is complete if and only if every factor is
(`completeSpace_pi_iff`). This is the family counterpart of Mathlib's
`CompleteSpace.fst_of_prod`, `CompleteSpace.snd_of_prod` and `completeSpace_prod_of_nonempty`,
and converses Mathlib's instance `Pi.complete`.
-/

public section

variable {ι : Type*} {E : ι → Type*} [∀ i, UniformSpace (E i)] [∀ i, Nonempty (E i)]

/-- Each factor of a complete product of nonempty uniform spaces is complete. -/
theorem CompleteSpace.of_pi [CompleteSpace (∀ i, E i)] (i : ι) : CompleteSpace (E i) := by
  classical
  -- `E i` is a retract of the product: insert into a fixed point `c` and read coordinate `i`.
  let c : ∀ j, E j := fun _ ↦ Classical.arbitrary _
  refine CompleteSpace.of_comp_eq_id (fun x : ∀ j, E j ↦ x i) (Function.update c i)
    (funext fun _ ↦ Function.update_self ..) (continuous_apply i) ?_
  refine uniformContinuous_pi.2 fun j ↦ ?_
  rcases eq_or_ne j i with rfl | hji
  · simp only [Function.update_self]; exact uniformContinuous_id
  · simpa [Function.update_of_ne hji] using uniformContinuous_const

/-- A product of nonempty uniform spaces is complete if and only if every factor is complete. -/
theorem completeSpace_pi_iff : CompleteSpace (∀ i, E i) ↔ ∀ i, CompleteSpace (E i) :=
  ⟨fun _ ↦ .of_pi, fun _ ↦ inferInstance⟩

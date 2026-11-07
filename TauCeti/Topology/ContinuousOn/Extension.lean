/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousOn

/-!
# Extending continuous functions on subtypes

A continuous function on a subtype extends to a function on the ambient space that is continuous
on the subset and agrees with the original function there. The extension is not asserted to be
continuous away from the subset.
-/

public section

open Function

/-- A continuous function on a subtype of a space extends to a function that is continuous on the
subset and agrees with it there. -/
theorem exists_continuousOn_eq_of_continuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty Y] {A : Set X} {s : A → Y} (hs : Continuous s) :
    ∃ r : X → Y, ContinuousOn r A ∧ ∀ a : A, r a = s a := by
  have hr : ∀ a : A, extend Subtype.val s (fun _ => Classical.arbitrary Y) a = s a := fun a =>
    Subtype.val_injective.extend_apply _ _ a
  refine ⟨extend Subtype.val s fun _ => Classical.arbitrary Y, ?_, hr⟩
  rw [continuousOn_iff_continuous_domRestrict]
  exact hs.congr fun a => (hr a).symm

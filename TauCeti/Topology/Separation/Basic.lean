/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Basic

/-!
# Avoiding finitely many points is an open condition

In a `T1Space` the complement of a point is open (Mathlib's `isOpen_ne`). Intersecting finitely
many such complements and pulling back along a continuous map shows that the points where a
continuous map into a `T1Space` avoids finitely many given values form an open set
(`TauCeti.isOpen_forall_ne`). For instance, the real coordinates of the complex plane minus
finitely many points form an open subset of `ℝ × ℝ`.
-/

public section

namespace TauCeti

/-- The points where a continuous map into a `T1Space` avoids finitely many values `c i` form an
open set. -/
theorem isOpen_forall_ne {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    [Finite ι] {f : X → Y} (hf : Continuous f) {c : ι → Y} :
    IsOpen {x : X | ∀ i, f x ≠ c i} := by
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun _ ↦ isOpen_ne.preimage hf

end TauCeti

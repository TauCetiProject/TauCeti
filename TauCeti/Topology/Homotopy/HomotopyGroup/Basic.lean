/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Basic properties of homotopy groups

A pointed space is path connected if and only if its zeroth homotopy set is a subsingleton.
This follows from Mathlib's equivalence between the zeroth homotopy set and path components.
-/

public section

open scoped Topology Topology.Homotopy
open HomotopyGroup Topology.Homotopy

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- A pointed space is path connected if and only if its zeroth homotopy set `π_ 0 X x` is a
subsingleton. -/
theorem pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (x : X) :
    PathConnectedSpace X ↔ Subsingleton (π_ 0 X x) := by
  rw [pathConnectedSpace_iff_zerothHomotopy]
  have hne : Nonempty (ZerothHomotopy X) := ⟨ZerothHomotopy.mk x⟩
  simp only [hne, true_and]
  exact (homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) x).symm.subsingleton_congr

end TauCeti

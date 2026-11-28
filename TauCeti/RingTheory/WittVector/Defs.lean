/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Defs

/-!
# Witt vectors over the zero ring

A Witt vector over `R` is a sequence of coordinates in `R`, so the Witt vectors over a ring with
at most one element have at most one element: `WittVector p R` is the zero ring when `R` is.
-/

public section

namespace WittVector

variable {p : ℕ} {R : Type*}

/-- The Witt vectors over a subsingleton ring form a subsingleton. -/
instance [Subsingleton R] : Subsingleton (WittVector p R) :=
  ⟨fun _ _ ↦ ext fun _ ↦ Subsingleton.elim _ _⟩

end WittVector

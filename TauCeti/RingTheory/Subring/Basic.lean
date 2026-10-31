/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Basic facts about subrings

The inclusion of a subring into itself is the identity homomorphism.

## Main results

* `Subring.inclusion_rfl`: the inclusion `R ⊆ R` is `RingHom.id R`.
-/

public section

namespace Subring

/-- The inclusion of a subring into itself is the identity homomorphism. -/
@[simp]
theorem inclusion_rfl {A : Type*} [Ring A] (R : Subring A) :
    R.inclusion le_rfl = RingHom.id R :=
  rfl

end Subring

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Composing open partial homeomorphisms with homeomorphisms

This file supplements Mathlib's `Homeomorph.transOpenPartialHomeomorph`, which precomposes an
open partial homeomorphism with a homeomorphism, by its identity law: precomposing with
`Homeomorph.refl` changes nothing (`Homeomorph.refl_transOpenPartialHomeomorph`). Together with
Mathlib's `Homeomorph.trans_transOpenPartialHomeomorph` this makes the precomposition an action of
homeomorphisms.
-/

public section

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Precomposing an open partial homeomorphism with the identity homeomorphism leaves it
unchanged. -/
@[simp, mfld_simps]
theorem refl_transOpenPartialHomeomorph (c : OpenPartialHomeomorph X Y) :
    (Homeomorph.refl X).transOpenPartialHomeomorph c = c := by
  simp [transOpenPartialHomeomorph_eq_trans]

end Homeomorph

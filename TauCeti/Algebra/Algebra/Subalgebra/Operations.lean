/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations

/-!
# The fixed subring of a ring action

Mathlib's `FixedPoints.subring B G` is the subring of elements of `B` fixed by every element of a
monoid `G` acting on `B` by ring automorphisms. Its carrier is `MulAction.fixedPoints G B`. This
file records the membership and carrier lemmas, the counterparts for subrings of Mathlib's
`FixedPoints.mem_subalgebra`.

## Main results

* `TauCeti.FixedPoints.mem_subring`: membership in the fixed subring.
* `TauCeti.FixedPoints.coe_subring`: the carrier of the fixed subring is the set of fixed points.
-/

public section

namespace TauCeti.FixedPoints

variable {B G : Type*} [Ring B] [Monoid G] [MulSemiringAction G B]

/-- Membership in the fixed subring. -/
@[simp]
theorem mem_subring {x : B} : x ∈ _root_.FixedPoints.subring B G ↔ ∀ g : G, g • x = x :=
  Iff.rfl

/-- The carrier of the fixed subring is the set of fixed points. -/
@[simp]
theorem coe_subring : (_root_.FixedPoints.subring B G : Set B) = MulAction.fixedPoints G B :=
  rfl

end TauCeti.FixedPoints

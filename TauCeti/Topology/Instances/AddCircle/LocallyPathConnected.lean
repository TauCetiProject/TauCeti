/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Real additive circles are locally path-connected

For a real period `p`, `AddCircle p` is the quotient of the locally path-connected space `ℝ`, so it
is locally path-connected (`AddCircle.instLocallyPathConnectedSpaceReal`), by Mathlib's
`Quotient.locallyPathConnectedSpace`.
-/

public section

namespace AddCircle

/-- A real additive circle is locally path-connected, as a quotient of `ℝ`. -/
instance instLocallyPathConnectedSpaceReal (p : ℝ) : LocallyPathConnectedSpace (AddCircle p) :=
  Quotient.locallyPathConnectedSpace

end AddCircle

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Instances.AddCircle.Real
public import TauCeti.Topology.Algebra.Group.Quotient.LocallyPathConnected

/-!
# Real additive circles are locally path-connected

For a real period `p`, `AddCircle p` is the quotient of the locally path-connected group `ℝ` by
the subgroup `zmultiples p`, so it is locally path-connected
(`AddCircle.instLocallyPathConnectedSpaceReal`), by
`QuotientAddGroup.instLocallyPathConnectedSpace`. Instance search does not unfold the definition
`AddCircle p`, so the instance is restated here.
-/

public section

namespace AddCircle

/-- A real additive circle is locally path-connected, as a quotient of `ℝ`. -/
instance instLocallyPathConnectedSpaceReal (p : ℝ) : LocallyPathConnectedSpace (AddCircle p) :=
  QuotientAddGroup.instLocallyPathConnectedSpace _

end AddCircle

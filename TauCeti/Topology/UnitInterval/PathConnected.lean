/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Path-connectedness and local path-connectedness of the unit interval

The unit interval `I = [0, 1]` in `ℝ` is convex, hence locally path-connected
(`unitInterval.instLocallyPathConnectedSpace`) and path-connected
(`unitInterval.instPathConnectedSpace`).
-/

public section

open Set

namespace unitInterval

/-- **The unit interval `I = [0, 1]` is locally path-connected.** -/
instance instLocallyPathConnectedSpace : LocallyPathConnectedSpace I :=
  Convex.locallyPathConnectedSpace ℝ (convex_Icc (0 : ℝ) 1)

/-- **The unit interval `I = [0, 1]` is path-connected.** -/
instance instPathConnectedSpace : PathConnectedSpace I :=
  PathConnectedSpace.of_locallyPathConnectedSpace

end unitInterval

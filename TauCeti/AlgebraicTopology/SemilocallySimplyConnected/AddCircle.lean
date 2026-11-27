/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Instances.AddCircle.Real
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Covering

/-!
# Real additive circles are semilocally simply connected

For a real period `p`, the covering map `(↑) : ℝ → AddCircle p` (`AddCircle.isCoveringMap_coe`)
is surjective and has simply connected total space, so `AddCircle p` is semilocally simply
connected (`AddCircle.instSemilocallySimplyConnectedSpaceReal`), by
`TauCeti.SemilocallySimplyConnectedSpace.of_isCoveringMap`.
-/

public section

namespace AddCircle

/-- A real additive circle is semilocally simply connected, being covered by the simply connected
space `ℝ`. -/
instance instSemilocallySimplyConnectedSpaceReal (p : ℝ) :
    TauCeti.SemilocallySimplyConnectedSpace (AddCircle p) :=
  .of_isCoveringMap (isCoveringMap_coe p) QuotientAddGroup.mk_surjective

end AddCircle

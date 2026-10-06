/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Total disconnectedness of a universe lift

The universe lift `ULift X` of a topological space is homeomorphic to `X`
(`Homeomorph.ulift`), so it is totally disconnected when `X` is. Mathlib records the analogous
transport for compactness (`ULift.compactSpace`); this instance completes the profinite instance
stack on `ULift X`, which the universal properties of free pro-`p` groups need when a target group
has to be lifted to the universe of the generating set.
-/

public section

universe u v

/-- The universe lift of a totally disconnected space is totally disconnected. -/
instance ULift.totallyDisconnectedSpace {X : Type u} [TopologicalSpace X]
    [TotallyDisconnectedSpace X] : TotallyDisconnectedSpace (ULift.{v} X) :=
  Homeomorph.ulift.symm.totallyDisconnectedSpace

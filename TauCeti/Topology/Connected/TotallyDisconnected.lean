/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Total disconnectedness of discrete sets and of a universe lift

A discrete set is totally disconnected, since a preconnected discrete set has at most one point.
In a `T₁` space every finite set is discrete (`Set.Finite.isDiscrete`), which is how a finite
ω-limit set is shown to be a single point.

The universe lift `ULift X` of a topological space embeds into `X` via `ULift.down`
(`Topology.IsEmbedding.uliftDown`), so it is totally disconnected when `X` is. Mathlib records the
analogous transport for compactness (`ULift.compactSpace`) and the separation axioms; this instance
completes the profinite instance stack on `ULift X`, which the universal properties of free
pro-`p` groups need when a target group has to be lifted to the universe of the generating set.
-/

public section

universe u v

/-- **A discrete set is totally disconnected.** -/
theorem IsDiscrete.isTotallyDisconnected {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsDiscrete s) : IsTotallyDisconnected s := fun _t hts ht ↦
  ht.isDiscrete_iff_subsingleton.1 (hs.mono hts)

/-- The universe lift of a totally disconnected space is totally disconnected. -/
instance ULift.totallyDisconnectedSpace {X : Type u} [TopologicalSpace X]
    [TotallyDisconnectedSpace X] : TotallyDisconnectedSpace (ULift.{v} X) :=
  Topology.IsEmbedding.uliftDown.isTotallyDisconnected_range.1
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

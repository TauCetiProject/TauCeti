/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Separation.Basic

/-!
# Total disconnectedness of discrete sets and of a universe lift

A discrete set, one whose points are all isolated in it, is totally disconnected, since a
preconnected discrete set has at most one point. In a `T₁` space every finite set is discrete. This
is how an ω-limit set inside a finite or discrete set is shown to be a single point.

The universe lift `ULift X` of a topological space is homeomorphic to `X`
(`Homeomorph.ulift`), so it is totally disconnected when `X` is. Mathlib records the analogous
transport for compactness (`ULift.compactSpace`); this instance completes the profinite instance
stack on `ULift X`, which the universal properties of free pro-`p` groups need when a target group
has to be lifted to the universe of the generating set.
-/

public section

universe u v

/-- **A discrete set is totally disconnected.** A set each of whose points is isolated in it has
no preconnected subset with two points. -/
theorem IsDiscrete.isTotallyDisconnected {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsDiscrete s) : IsTotallyDisconnected s := fun _t hts ht ↦
  ht.isDiscrete_iff_subsingleton.1 (hs.mono hts)

/-- **A finite set in a `T₁` space is totally disconnected.** -/
theorem Set.Finite.isTotallyDisconnected {X : Type*} [TopologicalSpace X] [T1Space X]
    {s : Set X} (hs : s.Finite) : IsTotallyDisconnected s :=
  hs.isDiscrete.isTotallyDisconnected

/-- The universe lift of a totally disconnected space is totally disconnected. -/
instance ULift.totallyDisconnectedSpace {X : Type u} [TopologicalSpace X]
    [TotallyDisconnectedSpace X] : TotallyDisconnectedSpace (ULift.{v} X) :=
  Homeomorph.ulift.symm.totallyDisconnectedSpace

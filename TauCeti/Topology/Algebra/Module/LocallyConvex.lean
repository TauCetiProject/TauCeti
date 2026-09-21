/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Homotopy.LocallyContractible

/-!
# Locally convex spaces are strongly locally contractible

A real locally convex topological vector space has a basis of convex neighbourhoods at each point,
and a nonempty convex set is contractible (`Convex.contractibleSpace`). Hence every point has a
basis of contractible neighbourhoods: the space is strongly locally contractible.

Mathlib records the weaker consequence that such a space is locally path-connected
(`LocallyConvexSpace.toLocallyPathConnectedSpace`); this file records the contractible version.
Together with `IsOpen.stronglyLocallyContractibleSpace` it makes every open subset of a real normed
space, such as a punctured plane, strongly locally contractible, and hence locally path-connected
and semilocally simply connected.
-/

public section

open Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- A real locally convex space is strongly locally contractible: its convex neighbourhoods of a
point are nonempty, hence contractible, and they form a basis of neighbourhoods. -/
instance (priority := 100) LocallyConvexSpace.toStronglyLocallyContractibleSpace :
    StronglyLocallyContractibleSpace E :=
  .of_bases (fun x ↦ LocallyConvexSpace.convex_basis (𝕜 := ℝ) x)
    fun _ _ hs ↦ hs.2.contractibleSpace ⟨_, mem_of_mem_nhds hs.1⟩

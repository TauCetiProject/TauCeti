/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.LocallyContractible

import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull

/-!
# Real topological vector spaces are strongly locally contractible

Every real topological vector space has a basis of balanced neighbourhoods of zero
(`nhds_basis_balanced`). These sets are star convex about zero (`Balanced.starConvex`),
hence contractible (`StarConvex.contractibleSpace`). Translating them gives a basis of
contractible neighbourhoods at every point; local convexity is not needed.

Together with `IsOpen.stronglyLocallyContractibleSpace`, this makes every open subset of a real
topological vector space strongly locally contractible, and hence locally path-connected.
-/

public section

open Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E]

/-- A real topological vector space is strongly locally contractible: translates of balanced
neighbourhoods of zero form a basis of nonempty star-convex, hence contractible, neighbourhoods. -/
instance (priority := 100) TauCeti.RealTopologicalVectorSpace.stronglyLocallyContractibleSpace :
    StronglyLocallyContractibleSpace E := by
  let : ContinuousNeg E := ContinuousNeg.of_continuousConstSMul ℝ E
  let : IsTopologicalAddGroup E := ⟨⟩
  refine .of_bases (p := fun _ s ↦ s ∈ 𝓝 (0 : E) ∧ Balanced ℝ s)
    (s := fun x s ↦ (x + ·) '' s) (fun x ↦ ?_) fun x s hs ↦ ?_
  · rw [← map_add_left_nhds_zero x]
    exact (nhds_basis_balanced ℝ E).map (x + ·)
  · exact (hs.2.starConvex.add_left x).contractibleSpace
      ((Set.nonempty_of_mem (mem_of_mem_nhds hs.1)).image (x + ·))

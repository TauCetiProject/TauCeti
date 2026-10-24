/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible

/-!
# Simple connectivity of convex sets

Nonempty star-convex subsets of real topological vector spaces are simply connected. In
particular, this applies to nonempty convex subsets.

## Main declarations

* `StarConvex.isSimplyConnected`: a nonempty star-convex subset is simply connected.
* `Convex.isSimplyConnected`: a nonempty convex subset is simply connected.
-/

public section

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] {s : Set E} {x : E}

/-- A nonempty star-convex subset of a real topological vector space is simply connected. -/
protected theorem StarConvex.isSimplyConnected (h : StarConvex ℝ x s) (hne : s.Nonempty) :
    IsSimplyConnected s := by
  let _ : ContractibleSpace s := h.contractibleSpace hne
  exact SimplyConnectedSpace.ofContractible s

/-- A nonempty convex subset of a real topological vector space is simply connected. -/
theorem Convex.isSimplyConnected {s : Set E} (hs : Convex ℝ s) (hne : s.Nonempty) :
    IsSimplyConnected s := by
  let ⟨x, hx⟩ := hne
  exact (hs.starConvex hx).isSimplyConnected hne

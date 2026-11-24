/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.LocallyContractible
public import Mathlib.Topology.Homotopy.Path

/-!
# Locally contractible spaces are locally path-connected

Mathlib's `LocallyContractibleSpace` is the classical notion: every neighbourhood `U` of a point
contains a neighbourhood `V` whose inclusion into `U` is null-homotopic. Mathlib derives local
path-connectedness only from the stronger `StronglyLocallyContractibleSpace`. The classical notion
already suffices: the homotopy from the inclusion `V ↪ U` to a constant map joins every point of
`V` inside `U` to the same point, so `V` lies in the path component of `U` through the given point
(`LocallyContractibleSpace.locallyPathConnectedSpace`).
-/

public section

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- A locally contractible space, in the classical sense that every neighbourhood of a point
contains a neighbourhood whose inclusion is null-homotopic, is locally path-connected. -/
theorem LocallyContractibleSpace.locallyPathConnectedSpace (h : LocallyContractibleSpace X) :
    LocallyPathConnectedSpace X := by
  refine locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mpr fun x u _ hxu => ?_
  obtain ⟨V, hVu, hV, y, ⟨F⟩⟩ := h x u (‹IsOpen u›.mem_nhds hxu)
  -- Each point of `V` is joined inside `u` to the centre `y` of the null-homotopy.
  have hjoin : ∀ v ∈ V, JoinedIn u v y := fun v hv =>
    ⟨(F.evalAt ⟨v, hv⟩).map continuous_subtypeVal, fun t => (F (t, ⟨v, hv⟩)).property⟩
  refine Filter.mem_of_superset hV fun v hv => ?_
  exact (hjoin x (mem_of_mem_nhds hV)).trans (hjoin v hv).symm

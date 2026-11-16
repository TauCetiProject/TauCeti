/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Countable ranges and locally constant maps

Locally constant functions on Lindelof spaces have countable range. Conversely, continuous
functions with countable range in a completely regular Hausdorff space are locally constant
when their domain is locally connected.

## Main results

* `IsLocallyConstant.range_countable`: countability of a locally constant range.
* `Continuous.isLocallyConstant_of_countable_range`: local constancy of continuous maps with
  countable range.
* `Continuous.isLocallyConstant_of_range_subset`: the same conclusion when the range is contained
  in that of a locally constant map on a Lindelof space.

## References

* `Mathlib.Topology.Compactness.Lindelof`, for countability of discrete Lindelof spaces.
* `Set.Countable.isTotallyDisconnected`, for countable subsets of completely regular spaces.
-/

public section

open Set Function Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X]

/-- A locally constant function on a Lindelof space has countable range. -/
theorem IsLocallyConstant.range_countable [LindelofSpace X] {f : X → Y}
    (hf : IsLocallyConstant f) : (range f).Countable := by
  let _ : TopologicalSpace Y := ⊥
  let _ : DiscreteTopology Y := discreteTopology_bot Y
  exact (isLindelof_range hf.continuous).countable_of_discrete

variable [TopologicalSpace Y] [T35Space Y] [LocallyConnectedSpace X]

/-- A continuous function with countable range in a completely regular Hausdorff space is
locally constant on a locally connected domain. -/
theorem Continuous.isLocallyConstant_of_countable_range {f : X → Y}
    (hf : Continuous f) (hr : (range f).Countable) : IsLocallyConstant f := by
  apply IsLocallyConstant.of_constant_on_connected_components
  intro x y hy
  have hsub : (f '' connectedComponent x).Subsingleton :=
    hr.isTotallyDisconnected _ (image_subset_range _ _) <|
      isPreconnected_connectedComponent.image f hf.continuousOn
  exact hsub ⟨y, hy, rfl⟩ ⟨x, mem_connectedComponent, rfl⟩

/-- A continuous map into a completely regular Hausdorff space is locally constant on a locally
connected domain if its range lies in that of a locally constant map on a Lindelof space. -/
theorem Continuous.isLocallyConstant_of_range_subset
    {Z : Type*} [TopologicalSpace Z] [LindelofSpace Z] {f : X → Y} {g : Z → Y}
    (hf : Continuous f) (hg : IsLocallyConstant g) (hr : range f ⊆ range g) :
    IsLocallyConstant f :=
  hf.isLocallyConstant_of_countable_range (hg.range_countable.mono hr)

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.PartialHomeomorph.Defs
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Closed images under partial homeomorphisms

This file collects elementary criteria for the image of a set under a partial homeomorphism
`e : X → Y`, or under its inverse, to be closed in the whole ambient space, and not merely
relatively closed in `e.target` or `e.source`. Neither the source nor the target of `e` is assumed
to be open.

## Main statements

* `PartialHomeomorph.isClosed_image_symm_of_isCompact`: the inverse of a partial homeomorphism
  from a Hausdorff space maps compact subsets of its target to closed sets.
* `PartialHomeomorph.isClosed_image_of_closure_subset_target`: the image of a closed subset of
  the source is closed if its closure stays inside the target, without a compactness assumption.
-/

public section

namespace PartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : PartialHomeomorph X Y)

/-- The image under `e.symm` of a compact subset of `e.target` is closed when the source space
is Hausdorff. -/
theorem isClosed_image_symm_of_isCompact [T2Space X] {t : Set Y} (ht : IsCompact t)
    (hte : t ⊆ e.target) : IsClosed (e.symm '' t) :=
  (ht.image_of_continuousOn (e.continuousOn_symm.mono hte)).isClosed

/-- The image of a closed subset of the source is closed in the whole target space if its
closure does not leave the target of the partial homeomorphism. No compactness is required. -/
theorem isClosed_image_of_closure_subset_target {s : Set X} (hs : IsClosed s)
    (hse : s ⊆ e.source) (hclosure : closure (e '' s) ⊆ e.target) :
    IsClosed (e '' s) := by
  refine isClosed_of_closure_subset fun y hy ↦ ⟨e.symm y, ?_, e.right_inv (hclosure hy)⟩
  have hy' : e.symm y ∈ closure (e.symm '' (e '' s)) :=
    ((e.continuousOn_symm y (hclosure hy)).mono (subset_closure.trans hclosure)).mem_closure_image
      hy
  rwa [(e.leftInvOn.mono hse).image_image, hs.closure_eq] at hy'

end PartialHomeomorph

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Basic properties of open partial homeomorphisms

This file collects elementary topological facts about open partial homeomorphisms that are not
in Mathlib.

A chart of a manifold is an open partial homeomorphism `φ : M → E`, and subsets of `M` are often
built by pulling back sets from the model space, as `φ.symm '' K` for some `K ⊆ φ.target`. When
`K` is compact and `M` is Hausdorff, such a pulled-back set is closed in all of `M`, not just in
`φ.source`. This lets arguments that need closed subsets of `M` (for instance, the relative
Mayer–Vietoris sequence for the local homology groups `Hₖ(M, M ∖ A)`, whose complements must be
open) be applied to compact convex pieces of a chart.

## Main statements

* `OpenPartialHomeomorph.isClosed_image_symm_of_isCompact`: the inverse of an open partial
  homeomorphism from a Hausdorff space maps compact subsets of its target to closed sets.
* `OpenPartialHomeomorph.isClosed_image_of_closure_subset_target`: the image of a closed subset
  of the source is closed if its closure stays inside the target, without a compactness assumption.
-/

public section

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)

/-- The image under `e.symm` of a compact subset of `e.target` is closed when the source space
is Hausdorff. -/
lemma isClosed_image_symm_of_isCompact [T2Space X] {t : Set Y} (ht : IsCompact t)
    (hte : t ⊆ e.target) : IsClosed (e.symm '' t) :=
  (ht.image_of_continuousOn (e.continuousOn_symm.mono hte)).isClosed

/-- The image of a closed subset of the source is closed in the whole target space if its
closure does not leave the target of the partial homeomorphism. No compactness is required. -/
theorem isClosed_image_of_closure_subset_target {s : Set X} (hs : IsClosed s)
    (hse : s ⊆ e.source) (hclosure : closure (e '' s) ⊆ e.target) :
    IsClosed (e '' s) := by
  have himage : e.IsImage s (e '' s) := by
    intro x hx
    exact ⟨fun ⟨z, hz, hzx⟩ => e.injOn (hse hz) hx hzx ▸ hz,
      fun hs => mem_image_of_mem e hs⟩
  apply isClosed_of_closure_subset
  intro y hy
  have ht := hclosure hy
  have hsymm : e.symm y ∈ closure s := (himage.symm.closure ht).mpr hy
  exact ⟨e.symm y, hs.closure_subset hsymm, e.right_inv ht⟩

end OpenPartialHomeomorph

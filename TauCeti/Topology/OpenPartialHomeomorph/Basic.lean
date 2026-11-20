/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import TauCeti.Topology.PartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic

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

The two closed-image statements hold for partial homeomorphisms whose source and target need not be
open, and are proved in that generality in `TauCeti.Topology.PartialHomeomorph.Basic`. They are
restated here in terms of the coercion and inverse of an open partial homeomorphism. Because the
source and target of an open partial homeomorphism are open, locally closed subsets of the source
or target are also sent to locally closed subsets of the ambient space.

## Main statements

* `OpenPartialHomeomorph.isClosed_image_symm_of_isCompact`: the inverse of an open partial
  homeomorphism from a Hausdorff space maps compact subsets of its target to closed sets.
* `OpenPartialHomeomorph.isClosed_image_of_closure_subset_target`: the image of a closed subset
  of the source is closed if its closure stays inside the target, without a compactness assumption.
* `OpenPartialHomeomorph.isLocallyClosed_image_of_subset_source`,
  `OpenPartialHomeomorph.isLocallyClosed_image_symm_of_subset_target`: an open partial homeomorphism
  and its inverse preserve locally closed subsets contained in their source or target.
-/

public section

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)

/-- The image under `e.symm` of a compact subset of `e.target` is closed when the source space
is Hausdorff. -/
lemma isClosed_image_symm_of_isCompact [T2Space X] {t : Set Y} (ht : IsCompact t)
    (hte : t ⊆ e.target) : IsClosed (e.symm '' t) :=
  e.toPartialHomeomorph.isClosed_image_symm_of_isCompact ht hte

/-- The image of a closed subset of the source is closed in the whole target space if its
closure does not leave the target of the partial homeomorphism. No compactness is required. -/
theorem isClosed_image_of_closure_subset_target {s : Set X} (hs : IsClosed s)
    (hse : s ⊆ e.source) (hclosure : closure (e '' s) ⊆ e.target) :
    IsClosed (e '' s) :=
  e.toPartialHomeomorph.isClosed_image_of_closure_subset_target hs hse hclosure

/-- The image under an open partial homeomorphism of a locally closed subset of its source is
locally closed in the ambient target space. -/
theorem isLocallyClosed_image_of_subset_source {s : Set X} (hs : IsLocallyClosed s)
    (hse : s ⊆ e.source) : IsLocallyClosed (e '' s) := by
  rw [← Set.inter_eq_right.2 hse, ← Subtype.image_preimage_val, ← Set.image_comp]
  exact (hs.preimage continuous_subtypeVal).image e.isOpenEmbedding_restrict.isInducing
    e.isOpenEmbedding_restrict.isOpen_range.isLocallyClosed

/-- The image under `e.symm` of a locally closed subset of `e.target` is locally closed in the
ambient source space. -/
theorem isLocallyClosed_image_symm_of_subset_target {s : Set Y} (hs : IsLocallyClosed s)
    (hst : s ⊆ e.target) : IsLocallyClosed (e.symm '' s) :=
  e.symm.isLocallyClosed_image_of_subset_source hs hst

end OpenPartialHomeomorph

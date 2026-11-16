/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import TauCeti.Topology.PartialHomeomorph.Basic

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

Both statements hold for partial homeomorphisms whose source and target need not be open, and are
proved in that generality in `TauCeti.Topology.PartialHomeomorph.Basic`. They are restated here
in terms of the coercion and inverse of an open partial homeomorphism.

## Main statements

* `OpenPartialHomeomorph.isClosed_image_symm_of_isCompact`: the inverse of an open partial
  homeomorphism from a Hausdorff space maps compact subsets of its target to closed sets.
* `OpenPartialHomeomorph.isClosed_image_of_closure_subset_target`: the image of a closed subset
  of the source is closed if its closure stays inside the target, without a compactness assumption.
* `OpenPartialHomeomorph.symm_map_of_intertwines`: if `e` intertwines a self-map `f` of its source
  with a map `A`, then `A` preserves the target and `e.symm` intertwines `A` with `f`.
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

/-- If an open partial homeomorphism `e` intertwines a map `f` of its source into itself with a
map `A`, then `A` maps the target of `e` into itself and `e.symm` intertwines `A` with `f`
there. -/
theorem symm_map_of_intertwines {f : X → X} {A : Y → Y}
    (hA : ∀ x ∈ e.source, f x ∈ e.source ∧ e (f x) = A (e x)) {z : Y} (hz : z ∈ e.target) :
    A z ∈ e.target ∧ e.symm (A z) = f (e.symm z) := by
  obtain ⟨hfs, hfe⟩ := hA (e.symm z) (e.map_target hz)
  rw [e.right_inv hz] at hfe
  rw [← hfe]
  exact ⟨e.map_source hfs, e.left_inv hfs⟩

end OpenPartialHomeomorph

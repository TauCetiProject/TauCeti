/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import TauCeti.Topology.PartialHomeomorph.Basic
import Mathlib.Algebra.Group.Basic

/-!
# Basic properties of open partial homeomorphisms

This file collects elementary facts about open partial homeomorphisms that are not
in Mathlib.

A chart of a manifold is an open partial homeomorphism `φ : M → E`, and subsets of `M` are often
built by pulling back sets from the model space, as `φ.symm '' K` for some `K ⊆ φ.target`. When
`K` is compact and `M` is Hausdorff, such a pulled-back set is closed in all of `M`, not just in
`φ.source`. This lets arguments that need closed subsets of `M` (for instance, the relative
Mayer–Vietoris sequence for the local homology groups `Hₖ(M, M ∖ A)`, whose complements must be
open) be applied to compact convex pieces of a chart.

The two closedness statements hold for partial homeomorphisms whose source and target need not
be open, and are
proved in that generality in `TauCeti.Topology.PartialHomeomorph.Basic`. They are restated here
in terms of the coercion and inverse of an open partial homeomorphism.

For an additive-group model, a chart translated to take a source point to zero has no other zero
on its source (`OpenPartialHomeomorph.sub_preimage_zero_subset`).

## Main statements

* `OpenPartialHomeomorph.sub_preimage_zero_subset`: translating a chart to send `z` to zero
  gives no other zero on its source, for any additive-group model.
* `OpenPartialHomeomorph.isClosed_image_symm_of_isCompact`: the inverse of an open partial
  homeomorphism from a Hausdorff space maps compact subsets of its target to closed sets.
* `OpenPartialHomeomorph.isClosed_image_of_closure_subset_target`: the image of a closed subset
  of the source is closed if its closure stays inside the target, without a compactness assumption.
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

/-- A chart translated to take `z` to zero has no other zero on its source. -/
theorem sub_preimage_zero_subset [AddGroup Y] {z : X} (hz : z ∈ e.source) :
    (fun x : e.source ↦ e x - e z) ⁻¹' {0} ⊆ {⟨z, hz⟩} := by
  intro x hx
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
  rw [Set.mem_singleton_iff]
  exact Subtype.ext (e.injOn x.property hz (sub_eq_zero.1 hx))

end OpenPartialHomeomorph

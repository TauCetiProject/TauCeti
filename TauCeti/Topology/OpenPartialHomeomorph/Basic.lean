/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.Sets.Compacts
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

Both closedness statements hold for partial homeomorphisms whose source and target need not be
open, and are proved in that generality in `TauCeti.Topology.PartialHomeomorph.Basic`. They are
restated here in terms of the coercion and inverse of an open partial homeomorphism. We also bundle
the image of a compact subset of the source as a `TopologicalSpace.Compacts`
(`OpenPartialHomeomorph.compactsImage`).

## Main statements

* `OpenPartialHomeomorph.isClosed_image_symm_of_isCompact`: the inverse of an open partial
  homeomorphism from a Hausdorff space maps compact subsets of its target to closed sets.
* `OpenPartialHomeomorph.isClosed_image_of_closure_subset_target`: the image of a closed subset
  of the source is closed if its closure stays inside the target, without a compactness assumption.
* `OpenPartialHomeomorph.compactsImage`: the image of a compact subset of `e.source`, bundled as a
  `TopologicalSpace.Compacts` contained in `e.target`, with inverse-cancellation lemmas.
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

/-- The image of a compact subset of `e.source`, bundled as a `TopologicalSpace.Compacts`. -/
def compactsImage (K : TopologicalSpace.Compacts X) (hK : (K : Set X) ⊆ e.source) :
    TopologicalSpace.Compacts Y :=
  ⟨e '' K, K.isCompact.image_of_continuousOn (e.continuousOn.mono hK)⟩

/-- The underlying set of `e.compactsImage K hK` is `e '' K`. -/
@[simp, norm_cast]
theorem coe_compactsImage (K : TopologicalSpace.Compacts X) (hK : (K : Set X) ⊆ e.source) :
    (e.compactsImage K hK : Set Y) = e '' (K : Set X) := (rfl)

/-- The image of a compact subset of `e.source` lies in `e.target`. -/
theorem compactsImage_subset_target (K : TopologicalSpace.Compacts X)
    (hK : (K : Set X) ⊆ e.source) :
    (e.compactsImage K hK : Set Y) ⊆ e.target :=
  Set.image_subset_iff.2 fun _ hx ↦ e.map_source (hK hx)

/-- Pulling back the image of a compact subset of `e.source` recovers that compact set. -/
@[simp]
theorem compactsImage_symm_compactsImage (K : TopologicalSpace.Compacts X)
    (hK : (K : Set X) ⊆ e.source)
    (hK' : (e.compactsImage K hK : Set Y) ⊆ e.symm.source :=
      e.symm_source.symm ▸ e.compactsImage_subset_target K hK) :
    e.symm.compactsImage (e.compactsImage K hK) hK' = K :=
  TopologicalSpace.Compacts.ext (e.symm_image_image_of_subset_source hK)

/-- Pushing forward the inverse image of a compact subset of `e.target` recovers that compact
set. -/
@[simp]
theorem compactsImage_compactsImage_symm (K : TopologicalSpace.Compacts Y)
    (hK : (K : Set Y) ⊆ e.symm.source)
    (hK' : (e.symm.compactsImage K hK : Set X) ⊆ e.source :=
      e.symm_target ▸ e.symm.compactsImage_subset_target K hK) :
    e.compactsImage (e.symm.compactsImage K hK) hK' = K :=
  TopologicalSpace.Compacts.ext (e.image_symm_image_of_subset_target (e.symm_source ▸ hK))

end OpenPartialHomeomorph

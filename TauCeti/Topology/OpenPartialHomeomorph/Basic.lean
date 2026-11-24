/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
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
* `OpenPartialHomeomorph.sourceRestrict`: the restriction of an open partial homeomorphism to its
  source, as a continuous map.
* `Topology.IsOpenEmbedding.of_continuousOn_inverse`: a continuous map with a continuous inverse
  on an open set containing its range is an open embedding, being an open partial homeomorphism
  with source the whole space.
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

/-- Every point is in the source of the identity partial homeomorphism. -/
theorem mem_refl_source (x : X) : x ∈ (OpenPartialHomeomorph.refl X).source :=
  Set.mem_univ x

/-- The restriction of an open partial homeomorphism to its source, as a continuous map. -/
def sourceRestrict : C(e.source, Y) :=
  ⟨e.source.domRestrict e, e.continuousOn.domRestrict⟩

/-- Restricting to the source agrees pointwise with the partial homeomorphism. -/
@[simp]
theorem sourceRestrict_apply (x : e.source) : e.sourceRestrict x = e x :=
  (rfl)

/-- The restriction to the source is an open embedding. -/
theorem isOpenEmbedding_sourceRestrict : Topology.IsOpenEmbedding e.sourceRestrict :=
  e.isOpenEmbedding_restrict

/-- A point of the source is the only point of the source that `e` sends to its image. -/
theorem sourceRestrict_preimage {a : X} (ha : a ∈ e.source) :
    e.sourceRestrict ⁻¹' {e a} ⊆ ContinuousMap.subtypeVal e.source ⁻¹' {a} :=
  fun x hx ↦ e.injOn x.property ha hx

end OpenPartialHomeomorph

namespace Topology.IsOpenEmbedding

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous map `f : X → Y` is an open embedding if it maps into an open set `W` on which a
map `g` is continuous and inverse to `f`: `g ∘ f = id` and `f ∘ g = id` on `W`. Then `f` is an
open partial homeomorphism with source `X` and target `W`. -/
theorem of_continuousOn_inverse {f : X → Y} {g : Y → X} {W : Set Y} (hf : Continuous f)
    (hW : IsOpen W) (hg : ContinuousOn g W) (hfW : ∀ x, f x ∈ W) (hgf : ∀ x, g (f x) = x)
    (hfg : ∀ y ∈ W, f (g y) = y) : IsOpenEmbedding f :=
  OpenPartialHomeomorph.isOpenEmbedding
    { toFun := f
      invFun := g
      source := Set.univ
      target := W
      map_source' := fun x _ ↦ hfW x
      map_target' := fun _ _ ↦ Set.mem_univ _
      left_inv' := fun x _ ↦ hgf x
      right_inv' := hfg
      open_source := isOpen_univ
      open_target := hW
      continuousOn_toFun := hf.continuousOn
      continuousOn_invFun := hg } rfl

end Topology.IsOpenEmbedding

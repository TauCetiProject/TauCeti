/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Local connectedness of compact images and of closed unions

Local connectedness is not preserved by continuous images in general — every metric space is a
continuous image of a discrete one — but it *is* preserved by quotient maps. This file applies that
to two kinds of continuous surjections that are automatically quotient maps, being closed maps:
a continuous surjection out of a compact space onto a Hausdorff one, and the natural map
`Set.sigmaToiUnion s : (Σ i, s i) → ⋃ i, s i` out of the disjoint union of a locally finite family
of closed sets. The first gives the type-level and set-level results for compact images; the second
gives local connectedness of a locally finite union of closed, locally connected sets, for instance
of a finite union of arcs.

The quotient step itself is Mathlib's. `Topology.IsCoinducing.locallyConnectedSpace` states that
a topology coinduced by a locally connected one is locally connected, which reaches quotient maps
through `IsQuotientMap.isCoinducing` and is strictly more general, since coinducing does not ask
for surjectivity. Local connectedness of a disjoint union, needed for the second application, is
the instance `Sigma.locallyConnectedSpace`.

One application is the necessary half of Carathéodory's continuity theorem: a conformal map on a
bounded domain with locally connected boundary that extends continuously to the closure has
locally connected image boundary. The extension maps the compact source boundary onto the image
boundary, so the set-level result applies. This application is in
`TauCeti/Analysis/Complex/Conformal/LocallyConnectedBoundary.lean`.

## Main results

* `TauCeti.locallyConnectedSpace_of_continuous_surjective` — the continuous image of a compact
  locally connected space in a Hausdorff space is locally connected.
* `TauCeti.locallyConnectedSpace_image_of_isCompact` — the set-level form: `f '' s` is locally
  connected for a compact, locally connected `s` on which `f` is continuous.
* `Sigma.locallyConnectedSpace` — a disjoint union of locally connected spaces is locally
  connected.
* `LocallyFinite.locallyConnectedSpace_iUnion` — a locally finite union of closed, locally
  connected sets is locally connected; for instance a finite union of arcs.

## References

* R. Engelking, *General Topology*, Theorem 6.1.29 (Hahn's theorem on quotients).
* J. G. Hocking and G. S. Young, *Topology*, Ch. 3.
-/

public section

open Set Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The continuous image of a compact locally connected space in a Hausdorff space is locally
connected.** A continuous surjection out of a compact space onto a Hausdorff one is closed, hence
a quotient map, hence coinducing, so `Topology.IsCoinducing.locallyConnectedSpace` applies. -/
theorem locallyConnectedSpace_of_continuous_surjective [LocallyConnectedSpace X] [CompactSpace X]
    [T2Space Y] {f : X → Y} (hf : Continuous f) (hsurj : Function.Surjective f) :
    LocallyConnectedSpace Y :=
  (hf.isClosedMap.isQuotientMap hf hsurj).isCoinducing.locallyConnectedSpace

/-- **The set-level form: a compact, locally connected set has locally connected continuous
images.** Stated with the subtype topologies on `s` and on `f '' s`, which is how a boundary or a
closure of a subset of a normed space is met in practice. -/
theorem locallyConnectedSpace_image_of_isCompact [T2Space Y] {s : Set X} {f : X → Y}
    [LocallyConnectedSpace s] (hs : IsCompact s) (hf : ContinuousOn f s) :
    LocallyConnectedSpace (f '' s) := by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  exact locallyConnectedSpace_of_continuous_surjective (hf.mapsToRestrict (mapsTo_image f s))
    (surjective_mapsTo_image_restrict f s)

end TauCeti

/-- **A disjoint union of locally connected spaces is locally connected.** A neighbourhood of
`⟨i, x⟩` contains the image under `Sigma.mk i` of a preconnected neighbourhood of `x`. -/
instance Sigma.locallyConnectedSpace {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, LocallyConnectedSpace (X i)] : LocallyConnectedSpace (Σ i, X i) := by
  refine locallyConnectedSpace_iff_connected_subsets.2 fun ⟨i, x⟩ U hU => ?_
  rw [Sigma.nhds_mk] at hU
  obtain ⟨V, hV, hVc, hVU⟩ := locallyConnectedSpace_iff_connected_subsets.1 inferInstance x _ hU
  refine ⟨Sigma.mk i '' V, ?_, hVc.image _ continuous_sigmaMk.continuousOn,
    image_subset_iff.2 hVU⟩
  rw [Sigma.nhds_mk]
  exact Filter.image_mem_map hV

/-- **A locally finite union of closed, locally connected sets is locally connected.** For
instance a finite union of arcs `f i '' Icc 0 1` in a Hausdorff space is locally connected. The
union is a quotient of the disjoint union `Σ i, s i`, because the natural map
`Set.sigmaToiUnion s` is closed. Closedness cannot be dropped, even for two sets: the segment
`{0} ×ˢ Icc (-1) 1` and the graph of `sin (1 / x)` over `0 < x ≤ 1` are locally connected, but
their union, the topologist's sine curve, is not. -/
theorem LocallyFinite.locallyConnectedSpace_iUnion {X ι : Type*} [TopologicalSpace X]
    {s : ι → Set X} [∀ i, LocallyConnectedSpace (s i)] (hf : LocallyFinite s)
    (hs : ∀ i, IsClosed (s i)) : LocallyConnectedSpace (⋃ i, s i) := by
  have hcont : Continuous (sigmaToiUnion s) :=
    continuous_sigma fun i => by unfold sigmaToiUnion; fun_prop
  refine (IsClosedMap.isQuotientMap (fun C hC => ?_) hcont
    (sigmaToiUnion_surjective s)).isCoinducing.locallyConnectedSpace
  -- the image of `C` is cut out of the union by the closed sets `C ∩ s i`, transported to `X`
  have himage : sigmaToiUnion s '' C =
      (↑) ⁻¹' ⋃ i, ((↑) : s i → X) '' (Sigma.mk (β := fun j => s j) i ⁻¹' C) := by
    ext ⟨y, hy⟩
    simp [sigmaToiUnion]
  rw [himage]
  refine IsClosed.preimage continuous_subtype_val <|
    (hf.subset fun i => Subtype.coe_image_subset _ _).isClosed_iUnion fun i => ?_
  exact (hs i).isClosedMap_subtype_val _ (isClosed_sigma_iff.1 hC i)

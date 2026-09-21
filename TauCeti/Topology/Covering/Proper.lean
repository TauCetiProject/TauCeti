/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Local homeomorphisms that are proper over an open set are coverings there

A local homeomorphism `f : E → X` need not be a covering map: an open inclusion is a local
homeomorphism, and it is not evenly covered at the boundary of its image.  What fails there is
properness, and the classical remedy is that a *proper* local homeomorphism between Hausdorff
spaces is a covering map.  Mathlib records the special case of a compact total space
(`isLocalHomeomorph_iff_isCoveringMap`) and the closed-map form
`IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`.

This file gives the version *over an open subset* `s` of a locally compact base: if every compact
subset of `s` has compact preimage, then `f` is a covering map over `s`, whatever happens outside
`s`.  This is the form a holomorphic map of a domain supplies when it is known to send points
near the boundary of the domain close to a closed set `C`: over the complement `s = Cᶜ` the map
is proper, hence a covering.

## Main results

* `IsCoveringMapOn.of_isLocalHomeomorph_of_isCompact_preimage` -- a local homeomorphism is a
  covering map over an open set on whose compact subsets it is proper.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Section 4.
-/

public section

open Set Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X} {s : Set X}

/-- **A map locally homeomorphic above an open set is a covering there if it is proper there.**
If `f : E → X` is a local homeomorphism on `f ⁻¹' s`, where the spaces are Hausdorff and `X`
is locally compact, and every compact subset of `s` has compact preimage, then `f` is a covering
map over `s`. -/
theorem IsCoveringMapOn.of_isLocalHomeomorph_of_isCompact_preimage [T2Space E] [T2Space X]
    [LocallyCompactSpace X] (hs : IsOpen s) (hf : IsLocalHomeomorphOn f (f ⁻¹' s))
    (hK : ∀ K ⊆ s, IsCompact K → IsCompact (f ⁻¹' K)) : IsCoveringMapOn f s := by
  have hfs : IsOpen (f ⁻¹' s) := isOpen_iff_mem_nhds.mpr fun x hx ↦
    (hf.continuousAt hx).preimage_mem_nhds (hs.mem_nhds hx)
  have hcont : Continuous (s.restrictPreimage f) := continuous_iff_continuousAt.mpr fun x ↦
    (hf.continuousAt x.2).restrictPreimage
  refine IsCoveringMapOn.of_isCoveringMap_restrictPreimage _ hs hfs ?_
  have := hs.locallyCompactSpace
  -- The restriction `f ⁻¹' s → s` is again a local homeomorphism ...
  have hloc : IsLocalHomeomorph (s.restrictPreimage f) :=
    IsLocalHomeomorph.of_comp (g := Subtype.val)
      (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr <|
        hf.comp hfs.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
          fun x _ ↦ x.2)
      hs.isOpenEmbedding_subtypeVal.isLocalHomeomorph hcont
  -- ... and it is proper, hence a closed map with compact fibres.
  have hproper : IsProperMap (s.restrictPreimage f) := by
    refine isProperMap_iff_isCompact_preimage.mpr ⟨hcont, fun K hK' => ?_⟩
    rw [IsEmbedding.subtypeVal.isCompact_iff, image_val_preimage_restrictPreimage]
    exact hK _ (Subtype.coe_image_subset _ _) (hK'.image continuous_subtype_val)
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  refine hproper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun x _ => ?_)
    hloc.isLocalHomeomorphOn
  refine (hproper.isCompact_preimage isCompact_singleton).finite
    (IsDiscrete.of_openPartialHomeomorph _ subset_rfl fun e _ => ?_)
  obtain ⟨φ, hφ, hφf⟩ := hloc e
  exact ⟨φ, hφ, hφf.symm⟩

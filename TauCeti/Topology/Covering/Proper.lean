/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Proper maps and covering maps

A covering map is proper exactly when its fibres are finite
(`IsCoveringMap.isProperMap_iff_finite_fiber`): over an evenly covered open set `U` the map is
the projection `U × F → U` with `F` the discrete fibre, which is closed when `F` is finite, and
being a closed map is local on the target. Thus the preimage of a compact set under a
finite-sheeted cover is compact; this is what makes a finite cover of a punctured compact surface
compact away from small neighbourhoods of the punctures.

Conversely, a local homeomorphism is a covering map over the part of the base where it is proper.

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

* `IsCoveringMap.isProperMap`, `IsCoveringMap.isProperMap_iff_finite_fiber`: a covering map is
  proper exactly when its fibres are finite.
* `IsCoveringMapOn.of_isLocalHomeomorph_of_isCompact_preimage` -- a local homeomorphism is a
  covering map over an open set on whose compact subsets it is proper.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Section 4.
-/

public section

open Set Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X} {s : Set X}

/-- **A covering map with finite fibres is proper.** Over an evenly covered open set the map is
the projection onto the base of a product with a finite discrete fibre. -/
theorem IsCoveringMap.isProperMap (hf : IsCoveringMap f) (hfin : ∀ x, Finite (f ⁻¹' {x})) :
    IsProperMap f := by
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨hf.continuous, ?_, fun x ↦ (toFinite _).isCompact⟩
  choose hdisc U hxU hU hfU H hH using hf
  -- Being a closed map is local on the target, so check it over each evenly covered `U x`.
  refine (TopologicalSpace.IsOpenCover.of_sets hU
    (eq_univ_of_forall fun x ↦ mem_iUnion.mpr ⟨x, hxU x⟩)).isClosedMap_iff_restrictPreimage.mpr
    fun x ↦ ?_
  have := hdisc x
  have := hfin x
  have hfst : (U x).restrictPreimage f = Prod.fst ∘ H x :=
    funext fun e ↦ Subtype.ext (hH x e).symm
  rw [hfst]
  exact isClosedMap_fst_of_compactSpace.comp (H x).isClosedMap

/-- **A covering map is proper exactly when its fibres are finite**: a fibre of a covering map is
discrete, so it is compact exactly when it is finite. -/
theorem IsCoveringMap.isProperMap_iff_finite_fiber (hf : IsCoveringMap f) :
    IsProperMap f ↔ ∀ x, Finite (f ⁻¹' {x}) := by
  refine ⟨fun h x ↦ ?_, hf.isProperMap⟩
  have := (hf x).discreteTopology_fiber
  have := isCompact_iff_compactSpace.mp (h.isCompact_preimage (isCompact_singleton (x := x)))
  exact finite_of_compact_of_discrete

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

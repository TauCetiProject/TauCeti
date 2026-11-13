/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Irreducible

/-!
# Preimages of irreducible components

A continuous surjection whose preimages of irreducible components are irreducible induces, by
taking preimages, a bijection between the irreducible components of the target and those of the
source. Over a field, this recognises base changes along which every irreducible component stays
irreducible, that is, geometrically irreducible components.
-/

public section

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- If `f` is a continuous surjection and the preimage of every irreducible component of `Y` is
irreducible, then `Z ↦ f ⁻¹' Z` maps the irreducible components of `Y` bijectively onto those
of `X`. -/
theorem Function.Surjective.bijOn_preimage_irreducibleComponents {f : X → Y}
    (hf : Function.Surjective f) (hc : Continuous f)
    (h : ∀ Z ∈ irreducibleComponents Y, IsIrreducible (f ⁻¹' Z)) :
    BijOn (f ⁻¹' ·) (irreducibleComponents Y) (irreducibleComponents X) := by
  have hmaps : MapsTo (f ⁻¹' ·) (irreducibleComponents Y) (irreducibleComponents X) := by
    refine fun Z hZ ↦ ⟨h Z hZ, fun T hT hZT ↦ ?_⟩
    have hle : Z ⊆ closure (f '' T) :=
      (image_preimage_eq Z hf ▸ image_mono hZT).trans subset_closure
    exact image_subset_iff.mp
      (subset_closure.trans (hZ.2 (hT.image f hc.continuousOn).closure hle))
  refine ⟨hmaps, (Set.preimage_injective.mpr hf).injOn, fun T hT ↦ ?_⟩
  obtain ⟨Z, hZ, hTZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure (f '' T)) (hT.1.image f hc.continuousOn).closure
  have hle : T ⊆ f ⁻¹' Z := image_subset_iff.mp (subset_closure.trans hTZ)
  exact ⟨Z, hZ, subset_antisymm (hT.2 (hmaps hZ).1 hle) hle⟩

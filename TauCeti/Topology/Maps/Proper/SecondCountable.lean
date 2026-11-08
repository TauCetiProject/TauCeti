/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Second countability under proper surjections

A proper surjection sends a second-countable space to a second-countable space. Unlike an open
quotient, a proper map need not send basis sets to open sets. Instead we use the kernel images of
finite unions of basis sets: these are open because the map is closed, and compactness of each
fibre supplies a finite subcover inside the preimage of any prescribed target neighborhood.

No separation hypothesis is required on either space.

## References

* N. Bourbaki, *General Topology*, Chapter I, §10 (proper mappings).
-/

public section

open Set TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- For a proper surjection, kernel images of finite unions of source basis sets form a basis
of the target. A kernel image contains a point exactly when it contains the entire fibre. -/
theorem IsProperMap.isTopologicalBasis_kernImage_finite (hf : IsProperMap f)
    (hsurj : Function.Surjective f) {B : Set (Set X)} (hB : IsTopologicalBasis B) :
    IsTopologicalBasis ((fun b : Set (Set X) ↦ kernImage f (⋃₀ b)) ''
      {b | b.Finite ∧ b ⊆ B}) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨b, ⟨_, hb⟩, rfl⟩
    exact isClosedMap_iff_kernImage.1 hf.isClosedMap (isOpen_sUnion fun u hu ↦ hB.isOpen (hb hu))
  · intro y U hy hU
    let C : Set (Set X) := {u | u ∈ B ∧ u ⊆ f ⁻¹' U}
    have hcover : f ⁻¹' {y} ⊆ ⋃ u ∈ C, u := by
      intro x hx
      have hxU : x ∈ f ⁻¹' U := by
        simpa only [mem_preimage, Set.mem_singleton_iff.1 hx] using hy
      obtain ⟨u, hu, hxu, hus⟩ := hB.exists_subset_of_mem_open hxU
        (hU.preimage hf.continuous)
      exact mem_iUnion.2 ⟨u, mem_iUnion.2 ⟨⟨hu, hus⟩, hxu⟩⟩
    obtain ⟨b, hbC, hbfin, hbcover⟩ :=
      (hf.isCompact_preimage isCompact_singleton).elim_finite_subcover_image (b := C) (c := id)
        (fun u hu ↦ hB.isOpen hu.1) hcover
    refine ⟨kernImage f (⋃₀ b), ⟨b, ⟨hbfin, fun u hu ↦ (hbC hu).1⟩, rfl⟩, ?_, ?_⟩
    · intro x hxy
      exact mem_sUnion.2 (by simpa only [mem_iUnion, exists_prop, id_eq] using hbcover hxy)
    · intro z hz
      obtain ⟨x, rfl⟩ := hsurj z
      obtain ⟨u, hub, hxu⟩ := hz rfl
      exact (hbC hub).2 hxu

/-- A proper surjective map preserves second countability. The map need not be open, and no
separation hypotheses are needed. -/
theorem IsProperMap.secondCountableTopology (hf : IsProperMap f)
    (hsurj : Function.Surjective f) [SecondCountableTopology X] : SecondCountableTopology Y :=
  (hf.isTopologicalBasis_kernImage_finite hsurj (isBasis_countableBasis X)).secondCountableTopology
    ((Set.countable_ofPred_finite_subset (countable_countableBasis X)).image _)

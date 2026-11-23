/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Topology.MetricSpace.InjectiveNeighborhood
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Assembling local diffeomorphisms near a section

A map which is locally invertible near a retraction section, and induces the topology
on that section, identifies a smaller neighbourhood with its image by a single partial
diffeomorphism. Neither the section nor its image needs to be compact. The source can
be kept inside a prescribed open set on which local invertibility is known. Nonemptiness
of the ambient source is needed to define the inverse outside its target.

`IsLocalDiffeomorphOn.exists_partialDiffeomorph_near_section` is the smooth assembly
step for normal-exponential coordinates: the section is the zero section of the normal
bundle and the retraction is its bundle projection. The conclusion supplies a smooth
inverse on one neighbourhood of the entire embedded submanifold.
`TauCeti.exists_partialDiffeomorph_near_section_of_isLocalDiffeomorphAt` needs local
invertibility only along the section, and also keeps the target inside a prescribed open set.

The construction uses `Topology.IsInducing.exists_injOn_neighborhood_section` for global
injectivity and `IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn` for the smooth inverse.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition,
Theorem 6.24 (tubular neighbourhoods).
-/

public section

open Set Function
open scoped Manifold ContDiff

namespace IsLocalDiffeomorphOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M N B : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace B]
  [TopologicalSpace.PseudoMetrizableSpace M] [TopologicalSpace.PseudoMetrizableSpace N]
  [Nonempty M] {n : ℕ∞ω} {f : M → N} {s : B → M} {O : Set M}

/-- Local diffeomorphisms near a continuous retraction section whose image induces the
base topology assemble to a partial diffeomorphism on a neighbourhood of the whole section.
The source stays inside the original open domain, and the forward map is unchanged. -/
theorem exists_partialDiffeomorph_near_section (hf : IsLocalDiffeomorphOn I J n f O)
    (hO : IsOpen O) (hsO : range s ⊆ O) (hs : Continuous s)
    (π : M → B) (hπ : Continuous π) (hsect : LeftInverse π s)
    (hind : Topology.IsInducing (f ∘ s)) :
    ∃ Φ : PartialDiffeomorph I J M N n,
      range s ⊆ Φ.source ∧ Φ.source ⊆ O ∧ Φ.target = f '' Φ.source ∧ ⇑Φ = f := by
  obtain ⟨U, hU, hsU, hUO, hemb⟩ := hf.isLocalHomeomorphOn.exists_isOpenEmbedding_near_section
    hO hsO hs π hπ hsect hind
  have hlocal : IsLocalDiffeomorphOn I J n f U := fun p => hf ⟨p.val, hUO p.property⟩
  have hinj : InjOn f U := Set.injOn_iff_injective.mpr hemb.injective
  refine ⟨hlocal.partialDiffeomorphOfInjOn hU hinj, ?_, ?_, ?_,
    coe_partialDiffeomorphOfInjOn hlocal hU hinj⟩
  · simpa only [partialDiffeomorphOfInjOn_source] using hsU
  · simpa only [partialDiffeomorphOfInjOn_source] using hUO
  · rw [partialDiffeomorphOfInjOn_target, partialDiffeomorphOfInjOn_source]

end IsLocalDiffeomorphOn

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M N B : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace B]
  [TopologicalSpace.PseudoMetrizableSpace M] [TopologicalSpace.PseudoMetrizableSpace N]
  [Nonempty M] {n : ℕ∞ω} {f : M → N} {s : B → M} {O : Set M} {O' : Set N}

/-- A map which is a local diffeomorphism at every point of a continuous retraction section,
and whose restriction to the section induces the base topology, is a partial diffeomorphism on
a neighbourhood of the whole section. The source stays inside a prescribed open neighbourhood
`O` of the section, the target inside a prescribed open neighbourhood `O'` of its image, and the
forward map is unchanged. -/
theorem exists_partialDiffeomorph_near_section_of_isLocalDiffeomorphAt
    (hf : ∀ b, IsLocalDiffeomorphAt I J n f (s b)) (hO : IsOpen O) (hsO : range s ⊆ O)
    (hO' : IsOpen O') (hsO' : range (f ∘ s) ⊆ O') (hs : Continuous s)
    (π : M → B) (hπ : Continuous π) (hsect : LeftInverse π s)
    (hind : Topology.IsInducing (f ∘ s)) :
    ∃ Φ : PartialDiffeomorph I J M N n, range s ⊆ Φ.source ∧ Φ.source ⊆ O ∧
      Φ.target ⊆ O' ∧ Φ.target = f '' Φ.source ∧ ⇑Φ = f := by
  -- Restrict to the open set of points of `O` near which `f` is a local diffeomorphism and which
  -- `f` sends into `O'`.
  let U := {p | IsLocalDiffeomorphAt I J n f p}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun _ hp ↦ hp.eventually
  let S := (U ∩ O) ∩ f ⁻¹' O'
  have hS : IsOpen S := ContinuousOn.isOpen_inter_preimage
    (fun _ hp ↦ hp.1.contMDiffAt.continuousAt.continuousWithinAt) (hU.inter hO) hO'
  have hsS : range s ⊆ S := range_subset_iff.2 fun b ↦
    ⟨⟨hf b, hsO (mem_range_self b)⟩, hsO' (mem_range_self b)⟩
  have hlocal : IsLocalDiffeomorphOn I J n f S := fun p ↦ p.property.1.1
  obtain ⟨Φ, hsΦ, hΦS, htarget, hΦ⟩ :=
    hlocal.exists_partialDiffeomorph_near_section hS hsS hs π hπ hsect hind
  refine ⟨Φ, hsΦ, fun _ hp ↦ (hΦS hp).1.2, ?_, htarget, hΦ⟩
  rw [htarget]
  rintro _ ⟨p, hp, rfl⟩
  exact (hΦS hp).2

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Induced and infimum topological ring structures

Mathlib provides `Topology.IsInducing.isTopologicalAddGroup`, `isTopologicalAddGroup_induced`,
`isTopologicalAddGroup_sInf`, `isTopologicalAddGroup_iInf`, and `isTopologicalAddGroup_inf` for
additive group topologies, while `RingTopology` bundles `CompleteLattice` operations only for
unital associative rings. This file supplies the direct `IsTopologicalRing` counterparts for
not-necessarily-unital, not-necessarily-associative rings:

* `Topology.IsInducing.isTopologicalRing` and `TauCeti.isTopologicalRing_induced`: pulling back a
  ring topology along a ring homomorphism yields a ring topology.
* `TauCeti.isTopologicalRing_sInf`, `TauCeti.isTopologicalRing_iInf`, and
  `TauCeti.isTopologicalRing_inf`: infima of ring topologies are ring topologies.
-/

public section

/-- A ring homomorphism that is a topological inducing map pulls back a topological ring structure
from its codomain to its domain. -/
theorem Topology.IsInducing.isTopologicalRing {R S F : Type*} [NonUnitalNonAssocRing R]
    [NonUnitalNonAssocRing S] [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) (hf : Topology.IsInducing f) :
    IsTopologicalRing R where
  toContinuousAdd := hf.continuousAdd f
  toContinuousMul := hf.continuousMul f
  toContinuousNeg := hf.continuousNeg (map_neg f)

namespace TauCeti

/-- Pulling back the topology of a topological ring along a ring homomorphism produces a
topological ring topology on the domain. -/
theorem isTopologicalRing_induced {R S F : Type*} [NonUnitalNonAssocRing R]
    [NonUnitalNonAssocRing S] [TopologicalSpace S] [IsTopologicalRing S] [FunLike F R S]
    [NonUnitalRingHomClass F R S] (f : F) :
    @IsTopologicalRing R (TopologicalSpace.induced f ‹_›) _ :=
  letI := TopologicalSpace.induced f ‹_›
  Topology.IsInducing.isTopologicalRing f ⟨rfl⟩

/-- The infimum of a set of ring topologies on `R` is a ring topology. -/
theorem isTopologicalRing_sInf {R : Type*} [NonUnitalNonAssocRing R]
    {ts : Set (TopologicalSpace R)} (h : ∀ t ∈ ts, @IsTopologicalRing R t _) :
    @IsTopologicalRing R (sInf ts) _ :=
  let _ := sInf ts
  { toContinuousAdd := continuousAdd_sInf fun t ht ↦ (h t ht).toContinuousAdd
    toContinuousMul := continuousMul_sInf fun t ht ↦ (h t ht).toContinuousMul
    toContinuousNeg := continuousNeg_sInf fun t ht ↦ (h t ht).toContinuousNeg }

/-- An indexed infimum of ring topologies on `R` is a ring topology. -/
theorem isTopologicalRing_iInf {ι : Sort*} {R : Type*} [NonUnitalNonAssocRing R]
    {ts : ι → TopologicalSpace R} (h : ∀ i, @IsTopologicalRing R (ts i) _) :
    @IsTopologicalRing R (⨅ i, ts i) _ :=
  isTopologicalRing_sInf (Set.forall_mem_range.mpr h)

/-- The infimum of two ring topologies on `R` is a ring topology. -/
theorem isTopologicalRing_inf {R : Type*} [NonUnitalNonAssocRing R]
    {t₁ t₂ : TopologicalSpace R} (h₁ : @IsTopologicalRing R t₁ _)
    (h₂ : @IsTopologicalRing R t₂ _) :
    @IsTopologicalRing R (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine isTopologicalRing_iInf fun b ↦ ?_
  cases b <;> assumption

end TauCeti

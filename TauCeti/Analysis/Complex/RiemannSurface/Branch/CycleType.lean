/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Branch.FiberCount
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic

/-!
# Cycle-type comparisons for fibres of finite holomorphic maps

Compares local multiplicities on a fibre with `fullCycleType` and `orbitCount` of a permutation.
-/

public section

open Set
open scoped Manifold

namespace TauCeti.RiemannSurface.FiniteHolomorphicMap

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] {α : Type*} [Fintype α] [DecidableEq α]
  (f : FiniteHolomorphicMap X Y) {y : Y} {σ : Equiv.Perm α}

/-- If the local multiplicities of `f` on the fibre over `y` match `fullCycleType σ`, the fibre
finset has cardinality `orbitCount σ`. -/
theorem card_finite_fiber_eq_orbitCount
    (h : (f.finite_fiber y).toFinset.val.map (localMultiplicity f) = Equiv.Perm.fullCycleType σ) :
    (f.finite_fiber y).toFinset.card = orbitCount σ := by
  have hc := congrArg Multiset.card h; rwa [Multiset.card_map, Finset.card_val,
    Equiv.Perm.fullCycleType_def, ← Equiv.Perm.orbitCount_eq_card_parts_partition] at hc

/-- If the local multiplicities of `f` on the fibre over `y` match `fullCycleType σ`, then
`(f ⁻¹' {y}).ncard` equals `orbitCount σ`. -/
theorem ncard_preimage_singleton_eq_orbitCount
    (h : (f.finite_fiber y).toFinset.val.map (localMultiplicity f) = Equiv.Perm.fullCycleType σ) :
    (f ⁻¹' {y}).ncard = orbitCount σ :=
  (ncard_eq_toFinset_card _ (f.finite_fiber y)).trans (f.card_finite_fiber_eq_orbitCount h)

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
  [CompactSpace X] [T2Space X] [T2Space Y] [PreconnectedSpace Y]

/-- If the local multiplicities of `f` on the fibre over `y` match `fullCycleType σ`, the local
ramification indices `e_x - 1` on that fibre sum to `Fintype.card α - orbitCount σ`. -/
theorem sum_localMultiplicity_sub_one_fiber_eq
    (h : (f.finite_fiber y).toFinset.val.map (localMultiplicity f) = Equiv.Perm.fullCycleType σ) :
    ∑ x ∈ (f.finite_fiber y).toFinset, (localMultiplicity f x - 1) =
      Fintype.card α - orbitCount σ := by
  have hdeg : degree f = Fintype.card α := by
    simpa [← degree_eq_fiber_sum f y, Finset.sum_eq_multiset_sum] using congrArg Multiset.sum h
  have hcard := card_fiber_add_sum_localMultiplicity_sub_one f y
  rw [f.card_finite_fiber_eq_orbitCount h, hdeg] at hcard; omega

end TauCeti.RiemannSurface.FiniteHolomorphicMap

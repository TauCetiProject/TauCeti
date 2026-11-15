/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.InductiveDimension.Classes
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic
import TauCeti.Topology.Algebra.Nonarchimedean.Basic

/-!
# Zero-dimensionality of nonarchimedean groups and nonarchimedean open subgroups

Mathlib's `Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected` shows that a Hausdorff
nonarchimedean topological group is totally separated (`NonarchimedeanGroup.instTotallySeparated`).
Without any separation axiom, the left cosets of open subgroups are clopen and form a neighbourhood
basis at every point, making every nonarchimedean topological group zero-dimensional
(`NonarchimedeanGroup.zeroDimensionalSpace`).

This file also registers `OpenSubgroup.instNonarchimedeanGroup` (and its additive counterpart):
since instance search on `↥U` for `U : OpenSubgroup G` does not unfold `OpenSubgroup` to
`Subgroup`, combining `OpenSubgroup.instIsTopologicalGroup` with `Subgroup.instNonarchimedeanGroup`
makes `NonarchimedeanGroup U` available directly on bundled open subgroups.

## Main instances

* `OpenSubgroup.instNonarchimedeanGroup`, `OpenAddSubgroup.instNonarchimedeanAddGroup`: an open
  subgroup of a nonarchimedean group is nonarchimedean in the subspace topology.

## Main results

* `NonarchimedeanGroup.zeroDimensionalSpace`, `NonarchimedeanAddGroup.zeroDimensionalSpace`: every
  nonarchimedean topological group is zero-dimensional, with no separation hypothesis.
-/

public section

open Filter Set Topology

/-- An open subgroup of a nonarchimedean group is nonarchimedean in the subspace topology. -/
@[to_additive /-- An open additive subgroup of a nonarchimedean additive group is nonarchimedean in
the subspace topology. -/]
instance OpenSubgroup.instNonarchimedeanGroup {G : Type*} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] (U : OpenSubgroup G) : NonarchimedeanGroup U where
  -- Instance search on `↥U` does not unfold `OpenSubgroup` to `Subgroup` on its own.
  is_nonarchimedean := (inferInstance : NonarchimedeanGroup ↥U.toSubgroup).is_nonarchimedean

namespace NonarchimedeanGroup

/-- Every nonarchimedean topological group is zero-dimensional: left cosets of open subgroups are
clopen and form a neighbourhood basis at every point. Kept as a theorem rather than an instance so
instance search does not run it against `ZeroDimensionalSpace → NonarchimedeanGroup` instances on
compact or locally compact groups. -/
@[to_additive /-- Every nonarchimedean topological additive group is zero-dimensional: cosets of
open additive subgroups are clopen and form a neighbourhood basis at every point. -/]
theorem zeroDimensionalSpace (G : Type*) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G] :
    ZeroDimensionalSpace G := by
  rw [zeroDimensionalSpace_iff_nhds_hasBasis_isClopen]
  intro x
  refine ⟨fun U ↦ ⟨fun hU ↦ ?_,
    fun ⟨C, ⟨hC, hxC⟩, hCU⟩ ↦ mem_of_superset (hC.isOpen.mem_nhds hxC) hCU⟩⟩
  have hpre : (x * ·) ⁻¹' U ∈ 𝓝 (1 : G) :=
    (continuous_const_mul x).continuousAt.preimage_mem_nhds (by simpa only [mul_one] using hU)
  obtain ⟨V, hV⟩ := is_nonarchimedean _ hpre
  refine ⟨(x⁻¹ * ·) ⁻¹' (V : Set G), ⟨V.isClopen.preimage (continuous_const_mul x⁻¹), ?_⟩, ?_⟩
  · simp
  · intro y hy
    simpa [mem_preimage] using hV hy

end NonarchimedeanGroup

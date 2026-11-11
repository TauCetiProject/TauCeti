/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# A linear topology is nonarchimedean and compatible with multiplication

If the neighbourhoods of zero of a topological module `M` over `R` have a basis of open
submodules (`IsLinearTopology R M`), then every neighbourhood of zero contains an open additive
subgroup, namely the underlying subgroup of an open submodule. So `M` is a nonarchimedean additive
group, and a linearly topologized ring is a nonarchimedean ring. A ring that is linearly
topologized on both sides, with topological additive group, is a topological ring, because open
ideals absorb multiplication.

These are theorems rather than instances: Tau Ceti has the converse instance
`TauCeti.NonarchimedeanAddGroup.isLinearTopology` over a compact ring, and the two together would
form an instance loop.

## Main results

* `IsLinearTopology.nonarchimedeanAddGroup`: a linearly topologized module is a nonarchimedean
  additive group.
* `IsLinearTopology.isTopologicalRing`: a two-sided linearly topologized ring with topological
  additive group is a topological ring.
* `IsLinearTopology.nonarchimedeanRing`: a linearly topologized ring is a nonarchimedean ring.
-/

public section

open Topology

namespace IsLinearTopology

/-- **A two-sided linearly topologised ring is a topological ring**, as soon as its additive group
is topological. For a commutative ring the `Rᵐᵒᵖ` hypothesis is supplied automatically. -/
theorem isTopologicalRing {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalAddGroup R]
    [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] : IsTopologicalRing R :=
  .of_addGroup_of_nhds_zero
    (tendsto_mul_zero_of_right (R := R) (f := 𝓝 0 ×ˢ 𝓝 0) Prod.fst Prod.snd Filter.tendsto_snd)
    (fun x₀ ↦ tendsto_mul_zero_of_right (R := R) (f := 𝓝 0) (fun _ ↦ x₀) id Filter.tendsto_id)
    fun x₀ ↦ tendsto_mul_zero_of_left (R := R) (f := 𝓝 0) id (fun _ ↦ x₀) Filter.tendsto_id

/-- A linearly topologized module is a nonarchimedean additive group: each open submodule inside a
neighbourhood of zero is an open additive subgroup. -/
theorem nonarchimedeanAddGroup (R : Type*) {M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [IsLinearTopology R M] :
    NonarchimedeanAddGroup M where
  is_nonarchimedean U hU := by
    obtain ⟨N, hN, hNU⟩ := (hasBasis_open_submodule R).mem_iff.1 hU
    exact ⟨⟨N.toAddSubgroup, hN⟩, hNU⟩

/-- A linearly topologized ring is a nonarchimedean ring: each open ideal inside a neighbourhood of
zero is an open additive subgroup. -/
theorem nonarchimedeanRing (R : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] : NonarchimedeanRing R where
  is_nonarchimedean := (nonarchimedeanAddGroup R (M := R)).is_nonarchimedean

end IsLinearTopology

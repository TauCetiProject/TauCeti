/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# Valuative topologies are nonarchimedean

Let `R` be a ring whose topology is the one defined by its valuative relation
(`IsValuativeTopology R`). The open balls `{x | v x < γ}` around `0` are additive subgroups and form
a neighbourhood basis of `0`, so `R` is a nonarchimedean topological ring. Mathlib records this only
for the topology `ValuativeRel.topologicalSpace` that it builds from the relation by hand; here it
is an instance for every topology satisfying `IsValuativeTopology R`.

Combined with Mathlib's `NonarchimedeanAddGroup.instTotallySeparated`, this makes every Hausdorff
valuative ring totally separated, hence totally disconnected. A division ring with a valuative
topology is Hausdorff (`IsValuativeTopology.instT2Space`), so in particular a nonarchimedean local
field is a totally disconnected space.

## Main declarations

* `TauCeti.instNonarchimedeanRingOfIsValuativeTopology`: a ring with a valuative topology is a
  nonarchimedean ring.
-/

public section

namespace TauCeti

open IsValuativeTopology

variable {R : Type*} [Ring R] [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]

/-- A ring whose topology is defined by its valuative relation is a nonarchimedean ring: every
neighbourhood of `0` contains an open ball `{x | v x < γ}`, which is an open additive subgroup. -/
instance (priority := low) instNonarchimedeanRingOfIsValuativeTopology : NonarchimedeanRing R where
  is_nonarchimedean U hU := by
    obtain ⟨γ, -, hγ⟩ := (hasBasis_nhds_zero R).mem_iff.mp hU
    let V := (ValuativeRel.valuation R).ltAddSubgroup γ
    exact ⟨⟨V, V.isOpen_of_mem_nhds ((hasBasis_nhds_zero R).mem_of_mem trivial)⟩, hγ⟩

end TauCeti

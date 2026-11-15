/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# The open subgroups of a nonarchimedean group are a basis of the neighbourhoods of one

`NonarchimedeanGroup` is stated as an existence property — every neighbourhood of `1` contains an
open subgroup — and the filter-basis form is what consumers actually use. This module records that
form, for multiplicative and additive groups.

No countability is involved: the basis is indexed by all open subgroups. Extracting an antitone
*sequence* from it, when `𝓝 0` is countably generated, is
`NonarchimedeanAddGroup.exists_antitone_basis_openAddSubgroup`.

## Main results

* `NonarchimedeanGroup.nhds_one_hasBasis_openSubgroup`, and its additive form
  `NonarchimedeanAddGroup.nhds_zero_hasBasis_openAddSubgroup`.
-/

public section

open Filter Topology

namespace NonarchimedeanGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]

/-- **The open subgroups form a basis of `𝓝 1`:** a set is a neighbourhood of `1` if and only if
it contains an open subgroup. -/
@[to_additive /-- **The open additive subgroups form a basis of `𝓝 0`:** a set is a neighbourhood
of `0` if and only if it contains an open additive subgroup. -/]
theorem nhds_one_hasBasis_openSubgroup :
    (𝓝 (1 : G)).HasBasis (fun _ : OpenSubgroup G ↦ True) fun V ↦ (V : Set G) :=
  ⟨fun _ ↦ ⟨fun hS ↦ (is_nonarchimedean _ hS).imp fun _ hV ↦ ⟨trivial, hV⟩,
    fun ⟨V, _, hV⟩ ↦ mem_of_superset V.mem_nhds_one hV⟩⟩

end NonarchimedeanGroup

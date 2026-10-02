/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ZMod
public import TauCeti.GroupTheory.Index.Two
public import TauCeti.Topology.Algebra.ContinuousMonoidHom

/-!
# The character of an open subgroup of index two is continuous

A subgroup `N` of index two in a group `G` has a character `χ_N : G →* Multiplicative (ZMod 2)`
with kernel `N`, `Subgroup.indexTwoCharacter`. When `G` is a topological group and `N` is open,
that kernel is open, so `χ_N` is continuous; this is what makes `χ_N` a class in continuous
cohomology with `𝔽₂` coefficients.

## Main results

* `Subgroup.continuous_indexTwoCharacter`: the character of an open subgroup of index two is
  continuous.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] {N : Subgroup G}

/-- **The character of an open subgroup of index two is continuous**: its kernel is the open
subgroup itself (`Subgroup.ker_indexTwoCharacter`). -/
theorem continuous_indexTwoCharacter (hN : N.index = 2) (hNo : IsOpen (N : Set G)) :
    Continuous (N.indexTwoCharacter hN) :=
  (N.indexTwoCharacter hN).continuous_of_isOpen_ker (by rwa [ker_indexTwoCharacter])

end Subgroup

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.Algebra.Group.Conj
import TauCeti.GroupTheory.FreeGroup.CSA

/-!
# Infinite conjugacy classes in nonabelian free groups

Nonabelian free groups are the canonical examples of ICC (infinite conjugacy class) groups, yielding
the free-group II₁ factors `L(F_n)` via Murray and von Neumann's ICC factor theorem
(`TauCeti.isFactor_groupVonNeumannAlgebra_of_isFreeGroup`). Since free groups are torsion-free and
commutative transitive (`IsFreeGroup.isCommTransitive`), `IsFreeGroup.infinite_setOf_isConj` and
`FreeGroup.infinite_setOf_isConj` follow immediately from
`Group.IsCommTransitive.infinite_setOf_isConj`.
-/

public section

namespace IsFreeGroup

/-- In a nonabelian free group, every nonidentity element has an infinite conjugacy class. -/
theorem infinite_setOf_isConj {G : Type*} [Group G] [IsFreeGroup G]
    (h : ¬ IsMulCommutative G) {g : G} (hg : g ≠ 1) :
    {x : G | IsConj g x}.Infinite :=
  isCommTransitive.infinite_setOf_isConj h hg

end IsFreeGroup

namespace FreeGroup

/-- Every nonidentity element of a free group on at least two generators has an infinite conjugacy
class. -/
theorem infinite_setOf_isConj {α : Type*} [Nontrivial α] {g : FreeGroup α} (hg : g ≠ 1) :
    {x : FreeGroup α | IsConj g x}.Infinite :=
  IsFreeGroup.infinite_setOf_isConj not_isMulCommutative hg

end FreeGroup

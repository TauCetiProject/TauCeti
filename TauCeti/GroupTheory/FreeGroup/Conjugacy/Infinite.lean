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

Every nonidentity element of a nonabelian free group has an infinite conjugacy class (the infinite
conjugacy class, or ICC, property). Since free groups are torsion-free and commutative transitive
(`IsFreeGroup.isCommTransitive`), this is an instance of
`Group.IsCommTransitive.infinite_setOf_isConj`. For `FreeGroup α`, noncommutativity holds whenever
`α` has at least two elements (`Nontrivial α`).

## Main results

* `IsFreeGroup.infinite_setOf_isConj`: in a nonabelian group satisfying `IsFreeGroup G`, every
  nonidentity element has an infinite conjugacy class.
* `FreeGroup.infinite_setOf_isConj`: when `α` is nontrivial, every nonidentity element of
  `FreeGroup α` has an infinite conjugacy class.
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

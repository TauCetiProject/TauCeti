/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SimpleGroupUniverse
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The statement of the classification of finite simple groups

This file assembles the explicit cyclic, alternating, Lie-type, and sporadic carriers indexed by
`TauCeti.CFSGIndex`. It then records the classification as a named proposition. No finiteness or
simplicity property of a listed carrier is asserted here, and the classification proposition is
not proved. The Lie-type branches use explicit carriers; their identification with the pinned
simply connected group schemes remains separate. The sporadic branches use the recorded
finite presentations, without assuming any recognition theorem for the presented groups.

## Main definitions

* `TauCeti.ValidLieTypeIndex.Group`: the concrete fixed-point, derived-subgroup, central-quotient
  carrier selected by a valid Lie-type index.
* `TauCeti.CFSGIndex.Group`: the concrete carrier selected by an index on the classification list.
* `TauCeti.ClassificationStatement`: every finite simple group is isomorphic to a listed carrier.
* `TauCeti.classificationStatement_of_zero`: the universe-zero statement implies the statement in
  every universe.

-/

public section

namespace TauCeti

/-- The concrete group represented by an index on the classification list. -/
abbrev CFSGIndex.Group : CFSGIndex → Type
  | .cyclic p _ => Multiplicative (ZMod p)
  | .alternating degree _ => alternatingGroup (Fin degree)
  | .lie index => index.Group
  | .sporadic name => name.Group

noncomputable instance (i : CFSGIndex) : Group i.Group := by
  cases i <;> infer_instance

universe u

/-- **Classification of finite simple groups, statement only.** Every finite simple group is
isomorphic to one of the explicitly constructed groups on the classification list.

The definition is exposed so that a module assuming `ClassificationStatement.{u}` can apply it to
a finite simple group, and a module proving the quantified statement can conclude it. -/
@[expose] def ClassificationStatement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G],
    ∃ i : CFSGIndex, Nonempty (G ≃* i.Group)

/-- The universe-zero classification statement implies the statement in every universe. -/
theorem classificationStatement_of_zero (h : ClassificationStatement.{0}) :
    ClassificationStatement.{u} :=
  exists_mulEquiv_of_forall_finite_isSimpleGroup_zero CFSGIndex.Group h

end TauCeti

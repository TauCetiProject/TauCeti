/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.ActionGroupoid.Basic
public import TauCeti.Topology.Homeomorph.Quotient

/-!
# The coarse space of an action groupoid

The native orbit quotient `MulAction.orbitRel.Quotient G X` is homeomorphic to the quotient
of `CategoryTheory.ActionCategory G X` by isomorphism. The homeomorphism upgrades
`CategoryTheory.ActionCategory.orbitQuotientEquivIsomorphismClasses` using the transported
object topology. This comparison needs no continuity assumption on the action: both spaces
have the quotient topology from the same object space and orbit relation.

This identifies the categorical coarse topology with the usual orbit topology without
identifying the objects with `X` definitionally or forgetting labels of ineffective arrows.
For a continuous discrete-group action the source is continuous and the target is open;
properness then gives a Hausdorff coarse space, which is also paracompact when `X` is
locally compact and second countable.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
-/

public section

open CategoryTheory Topology

namespace TauCeti.ActionGroupoid

variable (G X : Type*) [Group G] [MulAction G X] [TopologicalSpace X]

/-- The ordinary orbit space is the coarse space of the native action groupoid, with its
quotient topology. Ineffective labels remain in the groupoid. -/
def orbitQuotientHomeomorphIsomorphismClasses :
    MulAction.orbitRel.Quotient G X ≃ₜ
      Quotient (isIsomorphicSetoid (ActionCategory G X)) :=
  Homeomorph.Quotient.congr (objectHomeomorph G X).symm
    fun _ _ ↦ by
      rw [objectHomeomorph_symm_apply, objectHomeomorph_symm_apply]
      exact ActionCategory.isIsomorphic_iff_orbitRel.symm

/-- The orbit of a point corresponds to the isomorphism class of its native object. -/
@[simp]
theorem orbitQuotientHomeomorphIsomorphismClasses_mk (x : X) :
    orbitQuotientHomeomorphIsomorphismClasses G X (Quotient.mk _ x) =
      Quotient.mk _ (ActionCategory.objEquiv G X x) := by
  simp only [orbitQuotientHomeomorphIsomorphismClasses, Homeomorph.Quotient.congr_mk,
    objectHomeomorph_symm_apply]

/-- The inverse coarse homeomorphism takes the class of an object to its point's orbit. -/
@[simp]
theorem orbitQuotientHomeomorphIsomorphismClasses_symm_mk (x : ActionCategory G X) :
    (orbitQuotientHomeomorphIsomorphismClasses G X).symm (Quotient.mk _ x) =
      Quotient.mk _ x.back := by
  rw [Homeomorph.symm_apply_eq, orbitQuotientHomeomorphIsomorphismClasses_mk,
    ← objectHomeomorph_symm_apply, ← objectHomeomorph_apply G X x,
    Homeomorph.symm_apply_apply]

/-- The coarse homeomorphism has the previously constructed orbit-class equivalence as
its underlying equivalence. -/
@[simp]
theorem orbitQuotientHomeomorphIsomorphismClasses_toEquiv :
    (orbitQuotientHomeomorphIsomorphismClasses G X).toEquiv =
      ActionCategory.orbitQuotientEquivIsomorphismClasses G X := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => simp

end TauCeti.ActionGroupoid

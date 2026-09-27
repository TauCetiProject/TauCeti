/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Transport along equalities of degrees in the homogeneous cochain complex

Mathlib's `HomologicalComplex.XIsoOfEq` transports an element of a complex along an equality of
degrees. For the coinduced resolution `TopRep.resolution X` of a topological representation and
for its complex of homogeneous cochains `TopRep.homogeneousCochains X`, this file records how such
a transport is read: evaluating a transported element of the resolution at a point of the group is
the transported value one degree down, and the transport of a homogeneous cochain is, on the
underlying element of the resolution, the transport one degree up. Both rules are used wherever
two constructions land in degrees that are equal but not definitionally so, as for the total
degree `m + n` of a cup product built by recursion on `m`.
-/

public section

namespace TauCeti.ContinuousCohomology

open CategoryTheory ContRepresentation

universe u v w

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X : TopRep.{max v w} R G}

/-- Evaluating a transported element of the resolution at a point of `G` is the transported value,
one degree down. -/
theorem resolution_XIsoOfEq_hom_apply_apply {i j : ℕ} (h : i + 1 = j + 1)
    (F : (TopRep.resolutionX X (i + 1)).V) (g : G) :
    (((TopRep.resolution X).XIsoOfEq h).hom.hom F : C(G, (TopRep.resolutionX X j).V)) g =
      ((TopRep.resolution X).XIsoOfEq (Nat.succ.inj h)).hom.hom (F g) := by
  obtain rfl : i = j := Nat.succ.inj h
  simp [ContIntertwiningMap.id_apply]

/-- Transport along an equality of degrees in the complex of homogeneous cochains is transport
along the corresponding equality in the resolution, one degree up. -/
theorem coe_homogeneousCochains_XIsoOfEq_hom_apply {p q : ℕ} (h : p = q)
    (v : (TopRep.homogeneousCochains X).X p) :
    Subtype.val (((TopRep.homogeneousCochains X).XIsoOfEq h).hom v) =
      ((TopRep.resolution X).XIsoOfEq (congrArg (· + 1) h)).hom.hom (Subtype.val v) := by
  subst h
  simp [ContIntertwiningMap.id_apply]

end TauCeti.ContinuousCohomology

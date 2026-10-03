/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology

/-!
# Transport along equalities of degrees in the homogeneous cochain complex

Mathlib's `HomologicalComplex.XIsoOfEq` transports an element of a complex along an equality of
degrees. For the coinduced resolution `TopRep.resolution X` of a topological representation and
for its complex of homogeneous cochains `TopRep.homogeneousCochains X`, this file records how such
a transport is read: evaluating a transported element of the resolution at a point of the group is
the transported value one degree down, and the transport of a homogeneous cochain is, on the
underlying element of the resolution, the transport one degree up. Both rules are used wherever
two constructions land in degrees that are equal but not definitionally so, as for the total
degree `m + n` of a cup product built by recursion on `m`. On continuous cohomology the transport
is `degreeCast`, the isomorphism `continuousCohomology n X ≅ continuousCohomology k X` along an
equality `n = k`, and a cocycle that is the transport of another has the transported class
(`π_eq_degreeCast_π`).

## Main definitions

* `TauCeti.ContinuousCohomology.degreeCast`: transport of continuous cohomology along an equality
  of degrees.
* `TauCeti.ContinuousCohomology.cocyclesDegreeCast`: transport of cocycles along an equality of
  degrees.
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

/-- **Transport of continuous cohomology along an equality of degrees**: the isomorphism
`continuousCohomology n X ≅ continuousCohomology k X` induced by `n = k`. It plays for continuous
cohomology the role that `HomologicalComplex.XIsoOfEq` plays for the objects of a complex, and is
needed wherever two constructions land in degrees that are equal but not definitionally so, as
`0 + n` and `n`. -/
noncomputable def degreeCast (X : TopRep.{max v w} R G) {n k : ℕ} (h : n = k) :
    continuousCohomology n X ≅ continuousCohomology k X :=
  eqToIso (congrArg (continuousCohomology · X) h)

/-- Transport along `n = n` is the identity. -/
@[simp]
theorem degreeCast_rfl (n : ℕ) : degreeCast X (rfl : n = n) = Iso.refl _ := by
  simp [degreeCast]

/-- The inverse of a transport is the transport along the reversed equality. -/
@[simp]
theorem degreeCast_symm {n k : ℕ} (h : n = k) : (degreeCast X h).symm = degreeCast X h.symm := by
  subst h
  simp [degreeCast]

/-- Two successive transports are the transport along the composite equality. -/
@[reassoc (attr := simp)]
theorem degreeCast_hom_comp_degreeCast_hom {n k l : ℕ} (h : n = k) (h' : k = l) :
    (degreeCast X h).hom ≫ (degreeCast X h').hom = (degreeCast X (h.trans h')).hom := by
  simp [degreeCast]

/-- Transport of cocycles along an equality of degrees. -/
noncomputable def cocyclesDegreeCast {n k : ℕ} (h : n = k) :
    _root_.ContinuousCohomology.cocycles X n ≃ₗ[R]
      _root_.ContinuousCohomology.cocycles X k := by
  subst k
  exact LinearEquiv.refl R _

/-- The underlying cochain of a transported cocycle is the corresponding transport in the
homogeneous cochain complex. -/
-- Not a `simp` lemma: `simp` rewrites the implicit carrier
-- `(TopRep.homogeneousCochains X).X k` on the left-hand side through
-- `CategoryTheory.Functor.mapHomologicalComplex_obj_X`, so the statement is not in `simp`-normal
-- form; use it with `rw`.
theorem iCycles_cocyclesDegreeCast {n k : ℕ} (h : n = k)
    (z : _root_.ContinuousCohomology.cocycles X n) :
    (TopRep.homogeneousCochains X).iCycles k (cocyclesDegreeCast h z) =
      ((TopRep.homogeneousCochains X).XIsoOfEq h).hom
        ((TopRep.homogeneousCochains X).iCycles n z) := by
  subst k
  rfl

/-- **Transport of a class along an equality of degrees.** If the cocycle `z'` of degree `k` is,
as a homogeneous cochain, the transport of the cocycle `z` of degree `n` along `n = k`, then the
class of `z'` is the transport of the class of `z`. -/
theorem π_eq_degreeCast_π {n k : ℕ} (h : n = k) (z : _root_.ContinuousCohomology.cocycles X n)
    (z' : _root_.ContinuousCohomology.cocycles X k)
    (hz : (TopRep.homogeneousCochains X).iCycles k z' =
      ((TopRep.homogeneousCochains X).XIsoOfEq h).hom
        ((TopRep.homogeneousCochains X).iCycles n z)) :
    _root_.ContinuousCohomology.π X k z' =
      (degreeCast X h).hom (_root_.ContinuousCohomology.π X n z) := by
  subst h
  obtain rfl : z' = z := (TopRep.homogeneousCochains X).iCycles_injective n (by simpa using hz)
  simp

/-- The class of a transported cocycle is the transport of its class. -/
@[simp]
theorem π_cocyclesDegreeCast {n k : ℕ} (h : n = k)
    (z : _root_.ContinuousCohomology.cocycles X n) :
    _root_.ContinuousCohomology.π X k (cocyclesDegreeCast h z) =
      (degreeCast X h).hom (_root_.ContinuousCohomology.π X n z) :=
  π_eq_degreeCast_π h z (cocyclesDegreeCast h z) (iCycles_cocyclesDegreeCast h z)

end TauCeti.ContinuousCohomology

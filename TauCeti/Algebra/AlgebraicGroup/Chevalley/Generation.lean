/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Coroot
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Coroot

/-!
# Generating the torus of a Chevalley datum by simple root subgroups

The actual torus of a Chevalley datum has character lattice `Λ(D)`, which may be a proper
sublattice of the full weight lattice `P`. Each simple coroot is a word in the positive and
negative simple root subgroups. Their products reach the image of `Hom(P, Aˣ)` in
`Hom(Λ(D), Aˣ)`. The full-weight torus lies in the Kostant elementary subgroup over every
commutative ring. Membership of actual torus points in the named elementary subgroup and
its equality with the extended elementary subgroup for divisible units are developed in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Elementary`.

These results do not assert generation of all points of the group scheme; that requires the
geometric point-generation theorem. Over a general field the actual torus need not be
contained in the elementary subgroup: in the adjoint form of type A₁ over `ℚ`, the image of
the full-weight torus misses the class of `diag(2, 1)`.

The group-level root-word identity is `ChevalleyDatum.simpleCorootPoints_eq_weylElement_mul_inv`.
The full-weight torus containment specializes
`kostantTorusSubgroup_le_kostantElementarySubgroup` to a Chevalley datum.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 28(c).
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open TauCeti.UniversalEnvelopingAlgebra

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (A : Type*) [CommRing A]

/-- The simple coroot value is the product of a simple Weyl element and the inverse of its
value at one, as an equality of datum points over every commutative ring. -/
theorem simpleCorootPoints_eq_weylElement_mul_inv (i : Fin t.rank) (s : Aˣ) :
    D.simpleCorootPoints i A s =
      D.weylElement (t.simpleIndex ht i) A s *
        (D.weylElement (t.simpleIndex ht i) A 1)⁻¹ := by
  apply Subtype.ext
  rw [D.coe_simpleCorootPoints_eq_root_word]
  simp [weylElement_def]

/-- The full-weight torus of a Chevalley datum lies in its Kostant elementary subgroup over
every commutative ring, without any divisibility assumption on the units. -/
theorem kostantTorusSubgroup_weight_le_kostantElementarySubgroup (A : CommAlgCat ℤ) :
    kostantTorusSubgroup D.lattice D.basis D.weight A ≤
      kostantElementarySubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator A := by
  exact kostantTorusSubgroup_le_kostantElementarySubgroup
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator D.basis D.weight
    D.isCartanWeightVector_basis (t.rootGeneratorWeight ht) (t.lie_lieBasis_h_rootGenerator ht)
    Sum.inl Sum.inr D.isSl2Triple_representation_rootGenerator
    (fun i => by ext j; simp only [t.rootGeneratorWeight_inr, t.rootGeneratorWeight_inl,
      Pi.neg_apply]) A

end

end TauCeti.DynkinType.ChevalleyDatum

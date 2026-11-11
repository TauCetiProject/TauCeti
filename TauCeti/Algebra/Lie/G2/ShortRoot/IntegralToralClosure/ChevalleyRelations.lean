/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.ChevalleyRelations

/-!
# Mixed-sign simple-root relations in the integral short-root G₂ carrier

Positive and negative numbered simple-root subgroups at distinct nodes commute over every
commutative ring. These are the mixed-sign zero-commutator Chevalley relations, allowing
opposite-sign root factors to be reordered without changing their parameters. The proof uses
the Serre relation and the represented Kostant root-subgroup commutation theorem, so it also
retains the divided-square terms of the short-root matrices in characteristics two and three.

The integral toral closure is not identified with the pinned simply connected group scheme of
G₂; these relations transfer to that group only along such an identification. Nor is this
integral carrier identified with the carrier generated over the prime field.

## Main results

* `commute_rootSubgroupPoints_inl_inr`: the positive-negative relation at distinct nodes.
* `commute_rootSubgroupPoints_inr_inl`: the negative-positive relation at distinct nodes.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25–26.

The transport through the matrix inclusion follows
`TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations`, using
`TauCeti.UniversalEnvelopingAlgebra.commute_kostantRootSubgroupMatrix`.
-/

public section

namespace TauCeti.G2ShortRoot.IntegralToralClosure

open TauCeti.UniversalEnvelopingAlgebra

universe u

/-- A positive and a negative numbered simple-root subgroup at distinct nodes commute over
every commutative ring. -/
theorem commute_rootSubgroupPoints_inl_inr {i j : Fin 2} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inl i) A s) (rootSubgroupPoints (.inr j) A t) := by
  have hlie :
      ⁅TauCeti.serreRootGenerator CartanMatrix.G₂ (.inl i),
        TauCeti.serreRootGenerator CartanMatrix.G₂ (.inr j)⁆ = 0 := by
    simpa only [TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr] using
      TauCeti.lie_serreE_serreF_of_ne ℚ CartanMatrix.G₂ hij
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, coe_rootSubgroupPoints_eq_kostantRootSubgroupMatrix] using
    (commute_kostantRootSubgroupMatrix
      (TauCeti.serreRootGenerator CartanMatrix.G₂) (TauCeti.serreH ℚ CartanMatrix.G₂)
      rep lattice.toAddSubgroup rep_kostantForm_mem_lattice latticeBasis hlie
      (isNilpotent_rep_serreRootGenerator (.inl i))
      (isNilpotent_rep_serreRootGenerator (.inr j))
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm s)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t)).eq

/-- A negative and a positive numbered simple-root subgroup at distinct nodes commute over
every commutative ring. -/
theorem commute_rootSubgroupPoints_inr_inl {i j : Fin 2} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inr i) A s) (rootSubgroupPoints (.inl j) A t) :=
  (commute_rootSubgroupPoints_inl_inr hij.symm A t s).symm

end TauCeti.G2ShortRoot.IntegralToralClosure

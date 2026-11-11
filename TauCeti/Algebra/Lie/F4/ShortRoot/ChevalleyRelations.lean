/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Carrier
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.ChevalleyRelations

/-!
# Commuting simple-root subgroups of the short-root F₄ carrier

The positive and negative numbered simple-root subgroups of the integral short-root carrier
satisfy the zero-commutator Chevalley relations over every commutative ring. Roots of the same
sign commute at nonadjacent nodes, and roots of opposite signs commute at distinct nodes.
These relations allow root factors to be collected without imposing characteristic or
reducedness assumptions on the coefficient ring.

The carrier's Serre presentation uses the transpose of the Bourbaki Cartan matrix. The public
same-sign hypotheses use the Bourbaki matrix itself; its symmetric zero pattern makes these
conditions equivalent. The proof uses integral Kostant root subgroups, not the false assertion
that all root operators on the short-root module have square zero.

The carrier is not identified with the pinned simply connected group scheme of its diagram.
Its constructions transfer to that pinned group only along such an identification, once proved.
No adjacent-node commutator formula or carrier identification is asserted here.

## Main results

* `commute_rootSubgroupPoints_inl_inl` and `commute_rootSubgroupPoints_inr_inr`:
  same-sign root points commute at nonadjacent nodes.
* `commute_rootSubgroupPoints_inl_inr` and `commute_rootSubgroupPoints_inr_inl`:
  opposite-sign root points commute at distinct nodes.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25–26.

The specialization follows `TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations`, using
`TauCeti.UniversalEnvelopingAlgebra.commute_kostantRootSubgroupMatrix`.
-/

public section

namespace TauCeti.F4ShortRoot

open TauCeti.UniversalEnvelopingAlgebra

universe u

local notation "CM" => CartanMatrix.F₄.transpose
local notation "rootGen" => TauCeti.serreRootGenerator CM
local notation "cartanGen" => TauCeti.serreH ℚ CM

private theorem commute_rootSubgroupPoints_of_lie_eq_zero
    {i j : Fin 4 ⊕ Fin 4} (hij : ⁅rootGen i, rootGen j⁆ = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints i A s) (rootSubgroupPoints j A t) := by
  apply Commute.of_map (f := (points A).subtype) Subtype.val_injective
  simpa only [Subgroup.subtype_apply, coe_rootSubgroupPoints] using
    (commute_kostantRootSubgroupMatrix rootGen cartanGen rep
      lattice.toAddSubgroup rep_kostantForm_mem_lattice latticeBasis hij
      (isNilpotent_rep_serreRootGenerator i) (isNilpotent_rep_serreRootGenerator j)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm s)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t))

/-- Positive numbered simple-root subgroups at nonadjacent Bourbaki nodes commute over every
commutative ring. -/
theorem commute_rootSubgroupPoints_inl_inl {i j : Fin 4} (hij : CartanMatrix.F₄ i j = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inl i) A s) (rootSubgroupPoints (.inl j) A t) := by
  have hzero : CartanMatrix.F₄ i j = 0 ↔ CartanMatrix.F₄ j i = 0 := by
    simpa only [DynkinType.cartanMatrix_F4] using
      DynkinType.cartanMatrix_apply_eq_zero_iff_symm .F4 i j
  have hji := hzero.mp hij
  have hlie : ⁅rootGen (.inl i), rootGen (.inl j)⁆ = 0 := by
    simp [TauCeti.serreRootGenerator_inl, Matrix.transpose_apply, hji]
  exact commute_rootSubgroupPoints_of_lie_eq_zero hlie A s t

/-- Negative numbered simple-root subgroups at nonadjacent Bourbaki nodes commute over every
commutative ring. -/
theorem commute_rootSubgroupPoints_inr_inr {i j : Fin 4} (hij : CartanMatrix.F₄ i j = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inr i) A s) (rootSubgroupPoints (.inr j) A t) := by
  have hzero : CartanMatrix.F₄ i j = 0 ↔ CartanMatrix.F₄ j i = 0 := by
    simpa only [DynkinType.cartanMatrix_F4] using
      DynkinType.cartanMatrix_apply_eq_zero_iff_symm .F4 i j
  have hji := hzero.mp hij
  have hlie : ⁅rootGen (.inr i), rootGen (.inr j)⁆ = 0 := by
    simp [TauCeti.serreRootGenerator_inr, Matrix.transpose_apply, hji]
  exact commute_rootSubgroupPoints_of_lie_eq_zero hlie A s t

/-- A positive and a negative numbered simple-root subgroup at distinct nodes commute over
every commutative ring. -/
theorem commute_rootSubgroupPoints_inl_inr {i j : Fin 4} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inl i) A s) (rootSubgroupPoints (.inr j) A t) := by
  have hlie : ⁅rootGen (.inl i), rootGen (.inr j)⁆ = 0 := by
    simpa only [TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr] using
      TauCeti.lie_serreE_serreF_of_ne ℚ CM hij
  exact commute_rootSubgroupPoints_of_lie_eq_zero hlie A s t

/-- A negative and a positive numbered simple-root subgroup at distinct nodes commute over
every commutative ring. -/
theorem commute_rootSubgroupPoints_inr_inl {i j : Fin 4} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints (.inr i) A s) (rootSubgroupPoints (.inl j) A t) :=
  (commute_rootSubgroupPoints_inl_inr hij.symm A t s).symm

end TauCeti.F4ShortRoot

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import TauCeti.Algebra.Bigraded.Stabilization
public import TauCeti.KnotTheory.Grid.Homology.FullyBlockedBigraded
public import TauCeti.KnotTheory.Grid.SmallGrid.Gradings

/-!
# An explicit basis for small-grid homology

The fully blocked differential vanishes on grids of size at most two. Consequently every grid
state gives a cycle, no nonzero cycle is a boundary, and the corresponding homology classes form
a basis. This file makes those generators explicit.

For a grid diagram `G` of size `n ≤ 2`, `fullyBlockedCycleOfLeTwo G hn x` is the cycle represented
by the single grid state `x`, and `fullyBlockedHomologyClassOfLeTwo G hn x` is its homology class.
The basis `fullyBlockedHomologyBasisOfLeTwo G hn` consists of exactly these classes. Its
coordinate formula identifies the coefficient of a class at `x` with the coefficient of any
cycle representative at `x`.

At size two, the basis has the two states `GridState.twoByTwoId` and
`GridState.twoByTwoSwap`. For the standard two-by-two unknot diagram their already-computed
`(M_O, A)` bigradings are `(-1, -1)` and `(0, 0)`, respectively
(`maslovOℤ_twoByTwo_twoByTwoId`, `alexander_twoByTwo_twoByTwoId`,
`maslovOℤ_twoByTwo_twoByTwoSwap`, and `alexander_twoByTwo_twoByTwoSwap`). Thus the basis here
turns the separate dimension and grading calculations into an explicit computation of the
fully blocked homology. In bigraded form, each homogeneous piece of the homology has one
dimension for each state of its bidegree, and the Poincaré series of the standard two-by-two
diagram is the series `TauCeti.Bigraded.W` of the stabilization factor.

## Main definitions

* `TauCeti.GridDiagram.fullyBlockedCycleOfLeTwo`: the cycle supported on one grid state.
* `TauCeti.GridDiagram.fullyBlockedHomologyClassOfLeTwo`: its homology class.
* `TauCeti.GridDiagram.fullyBlockedHomologyBasisOfLeTwo`: the basis of small-grid homology
  indexed by grid states.

## Main results

* `TauCeti.GridDiagram.fullyBlockedHomologyBasisOfLeTwo_apply`: every basis vector is the
  homology class of its indexing state.
* `TauCeti.GridDiagram.fullyBlockedHomologyBasisOfLeTwo_repr_mk`: the coordinates of a
  homology class are the coefficients of any cycle representative.
* `TauCeti.GridDiagram.fullyBlockedHomologyBasisOfLeTwo_repr_class`: a single-state class has
  the corresponding singleton coordinate vector.
* `TauCeti.GridDiagram.fullyBlockedHomologyClassOfLeTwo_ne_zero` and
  `TauCeti.GridDiagram.fullyBlockedHomologyClassOfLeTwo_injective`: the state classes are
  nonzero and pairwise distinct.
* `TauCeti.OddComponentGridDiagram.finrank_bigradedFullyBlockedHomologyPiece_of_le_two`: each
  homogeneous piece has dimension the number of states of its bidegree.
* `TauCeti.OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_twoByTwo`: the
  standard two-by-two diagram has Poincaré series `W`.

## References

This advances the “Grid homology computes” acceptance criterion in
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, specifically the computation of the
two-by-two unknot grid with its bigradings and the visible rank-two stabilization factor. The
fully blocked complex and its grading conventions follow Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapters 3 and 4.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The fully blocked cycle supported on a single grid state when the grid size is at most two.

The size hypothesis makes the fully blocked differential zero, so the singleton chain is a
cycle. -/
noncomputable def fullyBlockedCycleOfLeTwo (hn : n ≤ 2) (x : GridState n) :
    G.fullyBlockedCycles :=
  ⟨Finsupp.single x 1, G.mem_fullyBlockedCycles_of_le_two hn _⟩

/-- The chain underlying the small-grid cycle supported on `x` is the singleton chain at `x`. -/
@[simp]
theorem fullyBlockedCycleOfLeTwo_coe (hn : n ≤ 2) (x : GridState n) :
    (G.fullyBlockedCycleOfLeTwo hn x : GridChain (ZMod 2) n) = Finsupp.single x 1 :=
  (rfl)

/-- The fully blocked homology class represented by a single grid state in size at most two. -/
noncomputable def fullyBlockedHomologyClassOfLeTwo (hn : n ≤ 2) (x : GridState n) :
    G.fullyBlockedHomology :=
  Submodule.Quotient.mk (G.fullyBlockedCycleOfLeTwo hn x)

/-- Under the small-grid equivalence from homology to the chain module, the class represented by
`x` becomes the singleton chain at `x`. -/
@[simp]
theorem fullyBlockedHomologyEquivChainOfLeTwo_class (hn : n ≤ 2) (x : GridState n) :
    G.fullyBlockedHomologyEquivChainOfLeTwo hn
        (G.fullyBlockedHomologyClassOfLeTwo hn x) =
      Finsupp.single x 1 := by
  rw [fullyBlockedHomologyClassOfLeTwo,
    G.fullyBlockedHomologyEquivChainOfLeTwo_apply_mk]
  exact G.fullyBlockedCycleOfLeTwo_coe hn x

/-- The basis of fully blocked homology in grid size at most two, indexed by grid states.

It is obtained by transporting the standard singleton basis of the grid chain module through
the inverse of `fullyBlockedHomologyEquivChainOfLeTwo`. -/
noncomputable def fullyBlockedHomologyBasisOfLeTwo (hn : n ≤ 2) :
    Module.Basis (GridState n) (ZMod 2) G.fullyBlockedHomology :=
  Finsupp.basisSingleOne.map (G.fullyBlockedHomologyEquivChainOfLeTwo hn).symm

/-- A vector of the small-grid homology basis is the class represented by its indexing grid
state. -/
@[simp]
theorem fullyBlockedHomologyBasisOfLeTwo_apply (hn : n ≤ 2) (x : GridState n) :
    G.fullyBlockedHomologyBasisOfLeTwo hn x =
      G.fullyBlockedHomologyClassOfLeTwo hn x := by
  apply (G.fullyBlockedHomologyEquivChainOfLeTwo hn).injective
  simp [fullyBlockedHomologyBasisOfLeTwo]

/-- The coordinates of the class of a small-grid cycle are its chain coefficients.

Since the differential and the boundary submodule both vanish, passing to homology does not
change any coefficient. -/
@[simp]
theorem fullyBlockedHomologyBasisOfLeTwo_repr_mk (hn : n ≤ 2) (c : G.fullyBlockedCycles) :
    (G.fullyBlockedHomologyBasisOfLeTwo hn).repr (Submodule.Quotient.mk c) =
      (c : GridChain (ZMod 2) n) := by
  rw [fullyBlockedHomologyBasisOfLeTwo, Module.Basis.map_repr]
  exact G.fullyBlockedHomologyEquivChainOfLeTwo_apply_mk hn c

/-- The coordinate vector of the homology class represented by `x` is the singleton vector at
`x`. -/
@[simp]
theorem fullyBlockedHomologyBasisOfLeTwo_repr_class (hn : n ≤ 2) (x : GridState n) :
    (G.fullyBlockedHomologyBasisOfLeTwo hn).repr (G.fullyBlockedHomologyClassOfLeTwo hn x) =
      Finsupp.single x 1 := by
  rw [fullyBlockedHomologyClassOfLeTwo,
    G.fullyBlockedHomologyBasisOfLeTwo_repr_mk]
  exact G.fullyBlockedCycleOfLeTwo_coe hn x

/-- Each single-state homology class is nonzero in grid size at most two. -/
theorem fullyBlockedHomologyClassOfLeTwo_ne_zero (hn : n ≤ 2) (x : GridState n) :
    G.fullyBlockedHomologyClassOfLeTwo hn x ≠ 0 := by
  rw [← G.fullyBlockedHomologyBasisOfLeTwo_apply hn x]
  exact (G.fullyBlockedHomologyBasisOfLeTwo hn).ne_zero x

/-- Distinct grid states determine distinct fully blocked homology classes in size at most two. -/
theorem fullyBlockedHomologyClassOfLeTwo_injective (hn : n ≤ 2) :
    Function.Injective (G.fullyBlockedHomologyClassOfLeTwo hn) := by
  intro x y hxy
  rw [← G.fullyBlockedHomologyBasisOfLeTwo_apply hn x,
    ← G.fullyBlockedHomologyBasisOfLeTwo_apply hn y] at hxy
  exact (G.fullyBlockedHomologyBasisOfLeTwo hn).injective hxy

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

local notation "F" => ZMod 2

/-- On grids of size at most two the differential vanishes, so the bidegree-`g` piece of fully
blocked homology has one dimension for each grid state of bidegree `g`. -/
theorem finrank_bigradedFullyBlockedHomologyPiece_of_le_two (hn : n ≤ 2) (g : ℤ × ℤ) :
    Module.finrank F (G.bigradedFullyBlockedHomologyPiece g) =
      (Finset.univ.filter fun x : GridState n => G.bidegree x = g).card := by
  let e := G.1.fullyBlockedHomologyEquivChainOfLeTwo hn
  have hmap : (G.bigradedFullyBlockedHomologyPiece g).map e.toLinearMap =
      LinearMap.range (G.bigradedChainInclusion F g) := by
    ext c
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, ⟨d, hd⟩, rfl⟩ := (mem_bigradedFullyBlockedHomologyPiece_iff_exists G).mp hy
      rw [LinearEquiv.coe_coe, GridDiagram.fullyBlockedHomologyEquivChainOfLeTwo_apply_mk]
      exact ⟨d, hd⟩
    · rintro ⟨d, rfl⟩
      refine ⟨Submodule.Quotient.mk ⟨_, G.1.mem_fullyBlockedCycles_of_le_two hn
        (G.bigradedChainInclusion F g d)⟩,
        (mem_bigradedFullyBlockedHomologyPiece_iff_exists G).mpr ⟨_, ⟨d, rfl⟩, rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, GridDiagram.fullyBlockedHomologyEquivChainOfLeTwo_apply_mk]
  rw [(e.submoduleMap _).finrank_eq, hmap,
    LinearMap.finrank_range_of_inj (G.bigradedChainInclusion_injective F g),
    finrank_bigradedChainPiece]

/-- The standard two-by-two diagram has fully blocked Poincaré series `W`: its two states give
one generator in bidegree `(-1, -1)` and one in bidegree `(0, 0)`. -/
theorem bigradedFullyBlockedHomologyPoincareSeries_twoByTwo :
    twoByTwo.bigradedFullyBlockedHomologyPoincareSeries = Bigraded.W := by
  have huniv : (Finset.univ : Finset (GridState 2)) =
      {GridState.twoByTwoId, GridState.twoByTwoSwap} :=
    (Finset.eq_univ_of_forall fun x => by
      rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with rfl | rfl <;> simp).symm
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun g => ?_)
  rw [coeff_bigradedFullyBlockedHomologyPoincareSeries,
    finrank_bigradedFullyBlockedHomologyPiece_of_le_two _ le_rfl, Finset.card_filter, huniv,
    Finset.sum_pair GridState.twoByTwoId_ne_twoByTwoSwap, bidegree_twoByTwo_twoByTwoId,
    bidegree_twoByTwo_twoByTwoSwap]
  rw [← one_mul Bigraded.W, Bigraded.coeff_mul_W]
  obtain ⟨a, b⟩ := g
  simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    Prod.mk_add_mk, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
  split_ifs <;> omega

end OddComponentGridDiagram

end TauCeti

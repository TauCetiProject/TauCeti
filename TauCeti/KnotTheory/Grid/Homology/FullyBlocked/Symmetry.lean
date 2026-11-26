/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.HalfTurn
public import TauCeti.KnotTheory.Grid.Differential.Symmetry
public import TauCeti.KnotTheory.Grid.Grading.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Grading.HalfTurn
public import TauCeti.KnotTheory.Grid.Homology.FullyBlocked.Bigraded
public import TauCeti.KnotTheory.Grid.Homology.Symmetry

/-!
# Symmetries of fully blocked grid homology

For a grid diagram `G` with an odd number of components, a cyclic permutation of the rows or of
the columns, the diagonal reflection and the half-turn each relabel grid states, intertwine the
fully blocked differentials and preserve the `(O-Maslov, Alexander)` bidegree of every state. So
they preserve the Poincaré series `P(G)` of the fully blocked grid homology `GH~(G)`.

## Main results

* `OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining`: a
  relabeling of grid states that intertwines the fully blocked differentials and preserves
  bidegrees identifies the Poincaré series of `GH~`.
* `OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_relabelRows_finRotate`,
  `OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_relabelColumns_finRotate`,
  `OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_transpose`,
  `OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_rotate`: the cyclic
  permutations, the diagonal reflection and the half-turn preserve the Poincaré series of `GH~`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapters 3 and 4.
-/

public section

namespace TauCeti.OddComponentGridDiagram

open GridDiagram

variable {n : ℕ}

local notation "F" => ZMod 2
local notation "P" => bigradedFullyBlockedHomologyPoincareSeries


/-- A linear equivalence of grid chains that intertwines the fully blocked differentials and moves
each grid state to a grid state of the same bidegree identifies the Poincaré series of fully
blocked homology. -/
theorem bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining
    (G G' : OddComponentGridDiagram n) (e : GridChain F n ≃ₗ[F] GridChain F n)
    (he : ∀ c, G'.val.fullyBlockedDifferential (e c) = e (G.val.fullyBlockedDifferential c))
    (σ : GridState n → GridState n) (heσ : ∀ x, e (Finsupp.single x 1) = Finsupp.single (σ x) 1)
    (hσ : ∀ x, G'.bidegree (σ x) = G.bidegree x) :
    P G = P G' := by
  refine G.bigradedFullyBlockedHomologyPoincareSeries_eq_of_linearEquiv
    (G.val.fullyBlockedHomologyEquivOfIntertwining G'.val e he) fun g y => ?_
  induction y using Submodule.Quotient.induction_on with
  | H z =>
    rw [bigradedFullyBlockedHomologyProjection_mk, fullyBlockedHomologyEquivOfIntertwining_apply_mk,
      fullyBlockedHomologyEquivOfIntertwining_apply_mk, bigradedFullyBlockedHomologyProjection_mk]
    congr 1
    ext1
    simp only [fullyBlockedCyclesEquivOfIntertwining_apply]
    have h := G.map_bigradedChainInclusion_bigradedChainProjection G' e.toLinearMap 0
      (fun x y hy => by
        rw [LinearEquiv.coe_coe, heσ, Finsupp.single_apply, ite_eq_right_iff]
        rintro rfl
        exact absurd (by rw [add_zero, hσ]) hy)
      g z
    rwa [add_zero] at h

variable (G : OddComponentGridDiagram n)

/-- A cyclic permutation of the rows preserves the Poincaré series of `GH~`. -/
@[simp]
theorem bigradedFullyBlockedHomologyPoincareSeries_relabelRows_finRotate :
    P (G.relabelRows (finRotate n)) = P G :=
  (bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining G _
    (GridChain.relabelRowsEquiv (finRotate n))
    (by simpa only [val_relabelRows] using
      G.val.fullyBlockedDifferential_relabelRows_finRotate_apply) _
    (fun x => GridChain.relabelRowsEquiv_single _ x 1)
    (G.bidegree_relabelRows_finRotate)).symm

/-- A cyclic permutation of the columns preserves the Poincaré series of `GH~`. -/
@[simp]
theorem bigradedFullyBlockedHomologyPoincareSeries_relabelColumns_finRotate :
    P (G.relabelColumns (finRotate n)) = P G :=
  (bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining G _
    (GridChain.relabelColumnsEquiv (finRotate n))
    (by simpa only [val_relabelColumns] using
      G.val.fullyBlockedDifferential_relabelColumns_finRotate_apply) _
    (fun x => GridChain.relabelColumnsEquiv_single _ x 1)
    (G.bidegree_relabelColumns_finRotate)).symm

/-- The diagonal reflection preserves the Poincaré series of `GH~`. -/
@[simp]
theorem bigradedFullyBlockedHomologyPoincareSeries_transpose : P G.transpose = P G :=
  (bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining G _
    (GridChain.transposeEquiv F n)
    (LinearMap.congr_fun G.val.fullyBlockedDifferential_transpose) _
    (fun x => GridChain.transposeEquiv_single x 1) G.bidegree_transpose).symm

/-- The half-turn preserves the Poincaré series of `GH~`. -/
@[simp]
theorem bigradedFullyBlockedHomologyPoincareSeries_rotate : P G.rotate = P G :=
  (bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining G _
    (GridChain.halfTurnEquiv F) G.val.fullyBlockedDifferential_rotate_halfTurnEquiv _
    (fun x => GridChain.halfTurnEquiv_single F x 1) G.bidegree_rotate_halfTurn).symm

end TauCeti.OddComponentGridDiagram

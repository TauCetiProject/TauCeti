/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Invariance
public import TauCeti.KnotTheory.Grid.Move.Unknot
import TauCeti.KnotTheory.Grid.SmallGrid.SimplyBlocked.Series

/-!
# Bigraded simply blocked grid homology invariants of grid knots

For a grid link `L` with one component (`hL : L.IsKnot`) over a field `K` of characteristic two,
this file descends the bigraded Poincaré series and Alexander-graded Euler characteristic of simply
blocked grid homology `G-hat` from knot grid diagrams to `L`:

* `GridLink.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries`: the finite `(O-Maslov, Alexander)`
  Poincaré series of `G-hat` of any presenting knot grid diagram and any blocked column.
* `GridLink.IsKnot.gradedSimplyBlockedHomologyEulerChar`: the resulting Alexander-graded Euler
  characteristic `Bigraded.euler (...)` in `LaurentPolynomial ℤ`.

Independence of both the presenting knot diagram and the choice of blocked column follows from
`GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_movesTo`. The evaluation
lemmas `bigradedSimplyBlockedHomologyPoincareSeries_eq_of_toGridLink_eq` and
`bigradedSimplyBlockedHomologyPoincareSeries_toGridLink` let callers compute the series on any
chosen presenting diagram and blocked column without unfolding the representative chosen in the
definition.

As an immediate consequence, every standard unknot grid `GridDiagram.unknot n` (for any grid size
`n + 2` and blocked column `i`) and the grid knot `GridLink.unknot` have bigraded simply blocked
Poincaré series `1` and Alexander-graded Euler characteristic `1`.

These invariants are defined intrinsically for grid knots (grid links with one component); no
comparison with topological embeddings in `S³` is used here.

## Main definitions

* `TauCeti.GridLink.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries`: the bigraded Poincaré
  series of `G-hat` of a grid knot over a field of characteristic two.
* `TauCeti.GridLink.IsKnot.gradedSimplyBlockedHomologyEulerChar`: the Alexander-graded Euler
  characteristic of `G-hat` of a grid knot.

## Main results

* `TauCeti.GridLink.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_toGridLink_eq` and
  `TauCeti.GridLink.IsKnot.gradedSimplyBlockedHomologyEulerChar_eq_of_toGridLink_eq`: evaluate both
  invariants on any presenting knot diagram and blocked column.
* `TauCeti.GridDiagram.bigradedSimplyBlockedHomologyPoincareSeries_unknot` and
  `TauCeti.GridLink.bigradedSimplyBlockedHomologyPoincareSeries_unknot`: both invariants equal `1`
  on standard unknot grids of every size and on `GridLink.unknot`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 4 and 5.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.GridDiagram

variable (n : ℕ) (K : Type*) [Field K] [CharP K 2] (i : Fin (n + 2))

/-- Every standard unknot grid `unknot n` of size `n + 2`, with any blocked column `i`, has
bigraded simply blocked Poincaré series `1` (one copy of `K` in bidegree `(0, 0)`). -/
@[simp]
theorem bigradedSimplyBlockedHomologyPoincareSeries_unknot :
    (isKnot_unknot n).bigradedSimplyBlockedHomologyPoincareSeries K i = 1 := by
  have hm : (unknot n).MovesTo twoByTwo := by
    rw [← toGridLink_eq_iff_movesTo, toGridLink_unknot, ← unknot_zero, toGridLink_unknot]
  exact ((isKnot_unknot n).bigradedSimplyBlockedHomologyPoincareSeries_eq_of_movesTo K
    twoByTwo.isKnot_of_two hm i 0).trans (bigradedSimplyBlockedHomologyPoincareSeries_twoByTwo K)

/-- Every standard unknot grid `unknot n` of size `n + 2`, with any blocked column `i`, has
Alexander-graded simply blocked Euler characteristic `1`. -/
@[simp]
theorem gradedSimplyBlockedHomologyEulerChar_unknot :
    (isKnot_unknot n).gradedSimplyBlockedHomologyEulerChar K i = 1 := by
  rw [IsKnot.gradedSimplyBlockedHomologyEulerChar_eq_euler,
    bigradedSimplyBlockedHomologyPoincareSeries_unknot, map_one]

end TauCeti.GridDiagram

namespace TauCeti.GridLink.IsKnot

variable {L : GridLink} (hL : L.IsKnot) (K : Type*) [Field K] [CharP K 2]

/-- The `(O-Maslov, Alexander)` bigraded Poincaré series of simply blocked grid homology `G-hat` of
a grid knot over a field `K` of characteristic two.

By `GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_movesTo`, it is
independent of both the presenting knot diagram and the choice of blocked column. -/
def bigradedSimplyBlockedHomologyPoincareSeries : Bigraded.Series :=
  let G := Classical.choose L.exists_gridDiagram
  let hG : G.2.IsKnot :=
    (isKnot_toGridLink G.2).mp ((Classical.choose_spec L.exists_gridDiagram).symm ▸ hL)
  hG.bigradedSimplyBlockedHomologyPoincareSeries K ⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩

/-- Evaluate `bigradedSimplyBlockedHomologyPoincareSeries` on any knot grid diagram presenting `L`
and any blocked column `i`. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_eq_of_toGridLink_eq
    {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (h : G.toGridLink = L) (i : Fin n) :
    hL.bigradedSimplyBlockedHomologyPoincareSeries K =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K i := by
  unfold bigradedSimplyBlockedHomologyPoincareSeries
  apply GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_movesTo
  exact ((Classical.choose L.exists_gridDiagram).2.toGridLink_eq_iff_movesTo).mp
    ((Classical.choose_spec L.exists_gridDiagram).trans h.symm)

/-- On the grid knot presented by a diagram `G`, `bigradedSimplyBlockedHomologyPoincareSeries`
agrees with the diagram series at any blocked column `i`. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_toGridLink
    {n : ℕ} {G : GridDiagram n} (hG : G.toGridLink.IsKnot) (i : Fin n) :
    hG.bigradedSimplyBlockedHomologyPoincareSeries K =
      ((isKnot_toGridLink G).mp hG).bigradedSimplyBlockedHomologyPoincareSeries K i :=
  hG.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_toGridLink_eq K
    ((isKnot_toGridLink G).mp hG) rfl i

/-- The total dimension of `bigradedSimplyBlockedHomologyPoincareSeries` equals the `K`-dimension
of `G-hat` on any presenting knot diagram `G` and blocked column `i`. -/
theorem totalDim_bigradedSimplyBlockedHomologyPoincareSeries_eq_of_toGridLink_eq
    {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (h : G.toGridLink = L) (i : Fin n) :
    Bigraded.totalDim (hL.bigradedSimplyBlockedHomologyPoincareSeries K) =
      Module.finrank K
        ((ModuleCat.restrictScalars
          (MvPolynomial.C : K →+* MvPolynomial {c : Fin n // c ≠ i} K)).obj
            (hG.simplyBlockedHomology K i)) := by
  rw [hL.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_toGridLink_eq K hG h i,
    hG.totalDim_bigradedSimplyBlockedHomologyPoincareSeries K i]

/-- The Alexander-graded Euler characteristic of simply blocked grid homology `G-hat` of a grid
knot over `K`. -/
def gradedSimplyBlockedHomologyEulerChar : LaurentPolynomial ℤ :=
  Bigraded.euler (hL.bigradedSimplyBlockedHomologyPoincareSeries K)

/-- `gradedSimplyBlockedHomologyEulerChar` is `Bigraded.euler` applied to the bigraded Poincaré
series of the grid knot. -/
theorem gradedSimplyBlockedHomologyEulerChar_eq_euler :
    hL.gradedSimplyBlockedHomologyEulerChar K =
      Bigraded.euler (hL.bigradedSimplyBlockedHomologyPoincareSeries K) :=
  (rfl)

/-- Evaluate `gradedSimplyBlockedHomologyEulerChar` on any knot grid diagram presenting `L` and any
blocked column `i`. -/
theorem gradedSimplyBlockedHomologyEulerChar_eq_of_toGridLink_eq
    {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (h : G.toGridLink = L) (i : Fin n) :
    hL.gradedSimplyBlockedHomologyEulerChar K =
      hG.gradedSimplyBlockedHomologyEulerChar K i := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hL.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_toGridLink_eq K hG h i,
    GridDiagram.IsKnot.gradedSimplyBlockedHomologyEulerChar_eq_euler]

/-- On the grid knot presented by `G`, `gradedSimplyBlockedHomologyEulerChar` agrees with the
diagram's Euler characteristic at any blocked column `i`. -/
theorem gradedSimplyBlockedHomologyEulerChar_toGridLink
    {n : ℕ} {G : GridDiagram n} (hG : G.toGridLink.IsKnot) (i : Fin n) :
    hG.gradedSimplyBlockedHomologyEulerChar K =
      ((isKnot_toGridLink G).mp hG).gradedSimplyBlockedHomologyEulerChar K i :=
  hG.gradedSimplyBlockedHomologyEulerChar_eq_of_toGridLink_eq K
    ((isKnot_toGridLink G).mp hG) rfl i

end TauCeti.GridLink.IsKnot

namespace TauCeti.GridLink

variable (K : Type*) [Field K] [CharP K 2]

/-- The unknot, as a grid knot independently of grid size, has bigraded simply blocked Poincaré
series `1`. -/
@[simp]
theorem bigradedSimplyBlockedHomologyPoincareSeries_unknot :
    isKnot_unknot.bigradedSimplyBlockedHomologyPoincareSeries K = 1 := by
  rw [IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_toGridLink_eq _ K
    (GridDiagram.isKnot_unknot 0) (GridDiagram.toGridLink_unknot 0) 0,
    GridDiagram.bigradedSimplyBlockedHomologyPoincareSeries_unknot]

/-- The unknot, as a grid knot independently of grid size, has Alexander-graded simply blocked
Euler characteristic `1`. -/
@[simp]
theorem gradedSimplyBlockedHomologyEulerChar_unknot :
    isKnot_unknot.gradedSimplyBlockedHomologyEulerChar K = 1 := by
  rw [IsKnot.gradedSimplyBlockedHomologyEulerChar_eq_euler,
    bigradedSimplyBlockedHomologyPoincareSeries_unknot, map_one]

end TauCeti.GridLink

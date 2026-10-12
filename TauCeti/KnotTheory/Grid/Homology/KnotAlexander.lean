/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Alexander
public import TauCeti.KnotTheory.Grid.Homology.Finite
public import TauCeti.Algebra.Module.GradedModule.NonTorsionDegree

/-!
# The Alexander grading on knot grid homology over `R[U]`

For a knot grid the Alexander grading of the concrete cycle quotient transports to the
categorical unblocked homology `GH⁻`. The knot module structure identifies the action of `U`
with that of every grid variable. Since each grid variable lowers Alexander degree by one,
so does `U`. Finite generation then bounds above the Alexander degrees containing a
non-torsion class. These are the grading and boundedness properties used to define the
grid concordance invariant from the top non-torsion degree.

The Alexander grading and the convention that `U` has degree `-1` follow
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 4 and 6.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (R : Type*)
  [CommRing R] [CharP R 2]

/-- The Alexander grading of the `R[U]`-module `GH⁻` of a knot grid. -/
noncomputable def alexanderUnblockedHomologyGrading : InternalGrading R (G.unblockedHomology R) :=
  (hG.toOddComponentGridDiagram).alexanderUnblockedHomologyGrading R

/-- Membership in a knot grid's Alexander piece is membership in the corresponding piece of
the concrete cycle quotient. -/
@[simp]
theorem mem_alexanderUnblockedHomologyGrading_piece_iff (a : ℤ)
    (y : G.unblockedHomology R) :
    y ∈ (hG.alexanderUnblockedHomologyGrading R).piece a ↔
      (G.unblockedHomologyIso R).hom y ∈
        ((hG.toOddComponentGridDiagram).alexanderHomologyGrading R).piece a :=
  (hG.toOddComponentGridDiagram).mem_alexanderUnblockedHomologyGrading_piece_iff R a y

/-- Multiplication by `U` lowers the Alexander grading of knot grid homology by one. -/
theorem X_smul_mem_alexanderUnblockedHomologyGrading_piece {a : ℤ}
    {y : G.unblockedHomology R}
    (hy : y ∈ (hG.alexanderUnblockedHomologyGrading R).piece a) :
    letI := hG.unblockedHomologyModule R
    (Polynomial.X : Polynomial R) • y ∈
      (hG.alexanderUnblockedHomologyGrading R).piece (a - 1) := by
  let _ := hG.unblockedHomologyModule R
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩
  rw [hG.X_smul_unblockedHomology i y]
  exact (hG.toOddComponentGridDiagram).X_smul_mem_alexanderUnblockedHomologyGrading_piece R i hy

/-- The Alexander degrees containing a non-torsion class of `GH⁻` are bounded above. -/
theorem bddAbove_nonTorsionDegrees_alexanderUnblockedHomologyGrading
    [IsNoetherianRing R] :
    letI := hG.unblockedHomologyModule R
    BddAbove (hG.alexanderUnblockedHomologyGrading R).nonTorsionDegrees := by
  let _ := hG.unblockedHomologyModule R
  exact @InternalGrading.bddAbove_nonTorsionDegrees R (G.unblockedHomology R)
    _ _ _ _ hG.isScalarTower_unblockedHomology
    (hG.alexanderUnblockedHomologyGrading R) 1
    (hG.finite_unblockedHomology (G := G) R) (fun {p} {y} hy => by
      exact hG.X_smul_mem_alexanderUnblockedHomologyGrading_piece R hy)

end GridDiagram.IsKnot

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Coarsen
public import TauCeti.KnotTheory.Grid.Homology.Alexander
public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Basic

/-!
# Coarsening the bigrading of `GH⁻` to the Alexander grading

For a grid diagram with an odd number of link components, projecting bidegrees `(m, a)` onto
their second coordinate `a` coarsens the `(O-Maslov, Alexander)` bigrading of `GC⁻` to its
Alexander grading (`OddComponentGridDiagram.coarsen_bigradedChainMinusGrading_snd` in
`TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain`). Over a commutative ring of characteristic two,
the same projection coarsens the induced bigrading on unblocked grid homology `GH⁻` to
`alexanderUnblockedHomologyGrading` (`coarsen_bigradedUnblockedHomologyGrading_snd` in
`TauCeti.KnotTheory.Grid.Homology.Bigraded.Basic`), so the coarsened piece family agrees with the
Alexander pieces (`coarsenGrading_bigradedUnblockedHomologyPiece_snd`) and each Alexander piece of
`GH⁻` is the supremum of its Maslov subpieces
(`iSup_bigradedUnblockedHomologyPiece_eq_alexanderUnblockedHomologyGrading_piece`).

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 4.6.
-/

public section

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- Coarsening the Maslov--Alexander homology pieces along `Prod.snd` recovers the Alexander
homology pieces. -/
@[simp]
theorem coarsenGrading_bigradedUnblockedHomologyPiece_snd :
    coarsenGrading (G.bigradedUnblockedHomologyPiece R) Prod.snd =
      (G.alexanderUnblockedHomologyGrading R).piece := by
  have hp : (G.bigradedUnblockedHomologyGrading R).piece = G.bigradedUnblockedHomologyPiece R :=
    funext (G.bigradedUnblockedHomologyGrading_piece R)
  simpa only [InternalGrading.coarsen_piece, hp] using
    congrArg InternalGrading.piece (G.coarsen_bigradedUnblockedHomologyGrading_snd R)

/-- Each Alexander piece of `GH⁻` is the supremum of the Maslov--Alexander pieces with that
Alexander degree. -/
@[simp]
theorem iSup_bigradedUnblockedHomologyPiece_eq_alexanderUnblockedHomologyGrading_piece (a : ℤ) :
    ⨆ m : ℤ, G.bigradedUnblockedHomologyPiece R (m, a) =
      (G.alexanderUnblockedHomologyGrading R).piece a := by
  rw [← coarsenGrading_snd, G.coarsenGrading_bigradedUnblockedHomologyPiece_snd R]

end TauCeti.OddComponentGridDiagram

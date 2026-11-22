/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Basic

/-!
# Finite generation of the Maslov--Alexander pieces of `GH⁻`

For a grid diagram with an odd number of link components, each Maslov--Alexander chain piece
`bigradedChainMinusPiece R g` is finitely generated over `R`
(`OddComponentGridDiagram.finite_bigradedChainMinusPiece` in
`TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain`; see `TauCeti.KnotTheory.Grid.Homology.Alexander`
for the Alexander-graded homology pieces).

Over a Noetherian commutative ring `R`, this finiteness passes to the homogeneous cycle pieces
`bigradedUnblockedCyclesPiece R g` as submodules of the chain pieces. In characteristic two, over
any commutative ring `R` (without a Noetherian hypothesis), base change from `ZMod 2` gives finite
generation of the homogeneous cycle pieces, and hence of the homogeneous homology pieces
`bigradedUnblockedHomologyPiece R g` (and the bundled pieces
`(bigradedUnblockedHomologyGrading R).piece g`) as images of those cycles under
`unblockedHomologyClass`. In particular, over any field of characteristic two, every homogeneous
piece of `GH⁻` is finite-dimensional.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 4.6.
-/

public section

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*)

section Cycles

variable [CommRing R] [IsNoetherianRing R]

/-- Over a Noetherian commutative ring, each Maslov--Alexander cycle piece of `GC⁻` is finitely
generated over the ground ring. -/
instance finite_bigradedUnblockedCyclesPiece (g : ℤ × ℤ) :
    Module.Finite R (G.bigradedUnblockedCyclesPiece R g) := by
  have : IsNoetherian R ((G.bigradedChainMinusGrading R).piece g) :=
    isNoetherian_of_isNoetherianRing_of_finite R ↥((G.bigradedChainMinusGrading R).piece g)
  rw [← G.ker_bigradedChainMinusGrading_piece R g]
  infer_instance

end Cycles

section Homology

variable [CommRing R] [CharP R 2]

/-- Over any commutative ring of characteristic two, each Maslov--Alexander piece of the cycles
of `GC⁻` is finitely generated over the ground ring. -/
instance finite_ker_bigradedChainMinusGrading_piece (g : ℤ × ℤ) :
    Module.Finite R (((G.bigradedChainMinusGrading R).ker
      (G.isHomogeneous_unblockedDifferential_bigradedChainMinusGrading R)).piece g) := by
  have h := G.finite_ker_unblockedDifferential_bigradedChainMinusPiece R g
  rw [← G.bigradedChainMinusGrading_piece R g] at h
  exact Module.Finite.equiv
    ((G.bigradedChainMinusGrading R).kerPieceEquivKerRestrict
      (G.isHomogeneous_unblockedDifferential_bigradedChainMinusGrading R) g).symm

/-- Over any commutative ring of characteristic two, each Maslov--Alexander cycle piece of `GC⁻`
is finitely generated over the ground ring. -/
instance finite_bigradedUnblockedCyclesPiece_of_charP_two (g : ℤ × ℤ) :
    Module.Finite R (G.bigradedUnblockedCyclesPiece R g) := by
  rw [← G.ker_bigradedChainMinusGrading_piece R g]
  infer_instance

/-- Each Maslov--Alexander piece of `GH⁻` is the image of the corresponding cycle piece under
`unblockedHomologyClass`. -/
theorem bigradedUnblockedHomologyPiece_eq_map (g : ℤ × ℤ) :
    G.bigradedUnblockedHomologyPiece R g =
      (G.bigradedUnblockedCyclesPiece R g).map
        ((G.val.unblockedHomologyClass R).restrictScalars R) := by
  ext y
  simpa only [Submodule.mem_map, mem_bigradedUnblockedCyclesPiece,
    LinearMap.restrictScalars_apply] using G.mem_bigradedUnblockedHomologyPiece_iff R

/-- Over any commutative ring of characteristic two, each bundled piece of
`bigradedUnblockedHomologyGrading` is finitely generated over the ground ring. -/
instance finite_bigradedUnblockedHomologyGrading_piece (g : ℤ × ℤ) :
    Module.Finite R ((G.bigradedUnblockedHomologyGrading R).piece g) := by
  rw [G.bigradedUnblockedHomologyGrading_eq R]
  infer_instance

/-- Over any commutative ring of characteristic two, each Maslov--Alexander piece of `GH⁻` is
finitely generated over the ground ring. -/
instance finite_bigradedUnblockedHomologyPiece (g : ℤ × ℤ) :
    Module.Finite R (G.bigradedUnblockedHomologyPiece R g) := by
  rw [← G.bigradedUnblockedHomologyGrading_piece R g]
  infer_instance

end Homology

end TauCeti.OddComponentGridDiagram

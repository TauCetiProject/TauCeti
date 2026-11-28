/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Basic
public import TauCeti.KnotTheory.Grid.Stabilization.Components
public import TauCeti.KnotTheory.Grid.Stabilization.Map.Grading
public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.Basic

/-!
# The bigrading of the north-east stabilization map

The north-east corner `X`-stabilization has new `O`-marking in the north-east corner of its
block. Its comparison map is the conjugate of the south-west comparison by torus half-turns.
Both half-turns preserve the absolute `O`-Maslov and Alexander gradings, and variable reversal
preserves total monomial degree. Consequently the specified north-east chain map has bidegree
`(0, 0)`, with each coefficient variable in bidegree `(-2, -1)`.

Chain-level bigrading preservation holds over any commutative ring. In characteristic two,
the bigrading descends to the specified bijective semilinear map on unblocked homology; its inverse
also preserves bidegrees, giving ground-ring linear equivalences on every homogeneous homology
piece. An odd component count is required only to use integer Alexander degrees.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3, 4.6 and 5.2;
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.2.
The homology piece equivalences adapt the south-west stabilization comparison in
`TauCeti.KnotTheory.Grid.Stabilization.Bigraded`
(`OddComponentGridDiagram.stabilizeXHomologyPieceEquiv`).
-/

public section

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (s : Fin n)

/-- The north-east corner `X`-stabilization of a diagram with an odd number of components. -/
abbrev stabilizeXSucc : OddComponentGridDiagram (n + 1) :=
  ⟨G.val.stabilizeX s.succ (G.val.X s).succ s,
    (G.val.componentCount_stabilizeX _ _ _).symm ▸ G.property⟩

/-- The underlying north-east stabilized diagram. -/
@[simp]
theorem val_stabilizeXSucc :
    (G.stabilizeXSucc s).val = G.val.stabilizeX s.succ (G.val.X s).succ s :=
  (rfl)

/-- A half-turn exchanges the north-east and south-west corner stabilizations. -/
@[simp]
theorem rotate_stabilizeXSucc : (G.stabilizeXSucc s).rotate = G.rotate.stabilizeX s.rev := by
  apply Subtype.ext
  simp only [val_stabilizeX, GridDiagram.rotate_stabilizeX_succ]

variable (R : Type*) [CommRing R]

/-- The north-east stabilization chain map preserves the `O`-Maslov--Alexander bigrading. -/
theorem stabilizeXSuccChainMap_mem_bigradedChainMinusPiece {g : ℤ × ℤ}
    {c : GridChainMinus R (n + 1)}
    (hc : c ∈ (G.stabilizeXSucc s).bigradedChainMinusPiece R g) :
    G.val.stabilizeXSuccChainMap s R c ∈ G.bigradedChainMinusPiece R g := by
  have hturn := (G.stabilizeXSucc s).halfTurnRenameEquiv_mem_bigradedChainMinusPiece R hc
  rw [rotate_stabilizeXSucc] at hturn
  have hmap := G.rotate.stabilizeXCoefficientFormula_mem_bigradedChainMinusPiece s.rev R hturn
  have hout := G.rotate.halfTurnRenameEquiv_mem_bigradedChainMinusPiece R hmap
  rw [rotate_rotate] at hout
  rw [GridDiagram.stabilizeXSuccChainMap_apply, GridDiagram.stabilizeXChainMap_apply]
  exact hout

variable [CharP R 2]

/-- The specified north-east stabilization comparison preserves the `O`-Maslov--Alexander
bigrading on `GH⁻`. -/
theorem stabilizeXSuccHomologyMap_mem_bigradedUnblockedHomologyPiece {g : ℤ × ℤ}
    {y : (G.stabilizeXSucc s).val.unblockedHomology R}
    (hy : y ∈ (G.stabilizeXSucc s).bigradedUnblockedHomologyPiece R g) :
    G.val.stabilizeXSuccHomologyMap s R y ∈ G.bigradedUnblockedHomologyPiece R g := by
  obtain ⟨z, hz, rfl⟩ := ((G.stabilizeXSucc s).mem_bigradedUnblockedHomologyPiece_iff R).mp hy
  rw [GridDiagram.stabilizeXSuccHomologyMap_unblockedHomologyClass]
  exact G.unblockedHomologyClass_mem_bigradedUnblockedHomologyPiece R
    (G.stabilizeXSuccChainMap_mem_bigradedChainMinusPiece s R hz)

/-- The north-east stabilization comparison reflects homology bidegrees as well as preserving
them. -/
@[simp]
theorem stabilizeXSuccHomologyMap_mem_bigradedUnblockedHomologyPiece_iff (g : ℤ × ℤ)
    (y : (G.stabilizeXSucc s).val.unblockedHomology R) :
    G.val.stabilizeXSuccHomologyMap s R y ∈ G.bigradedUnblockedHomologyPiece R g ↔
      y ∈ (G.stabilizeXSucc s).bigradedUnblockedHomologyPiece R g := by
  simpa only [GridDiagram.stabilizeXSuccHomologyEquiv_apply] using
    (G.stabilizeXSucc s).mem_bigradedUnblockedHomologyPiece_iff_of_linearEquiv R G
      (G.val.stabilizeXSuccHomologyEquiv s R)
      (fun _ _ hy ↦ by
        simpa only [GridDiagram.stabilizeXSuccHomologyEquiv_apply] using
          G.stabilizeXSuccHomologyMap_mem_bigradedUnblockedHomologyPiece s R hy)
      g y

/-- The specified north-east stabilization comparison identifies each homogeneous homology piece
with the piece of the same bidegree in the original grid. -/
noncomputable def stabilizeXSuccHomologyPieceEquiv (g : ℤ × ℤ) :
    (G.stabilizeXSucc s).bigradedUnblockedHomologyPiece R g ≃ₗ[R]
      G.bigradedUnblockedHomologyPiece R g :=
  (G.stabilizeXSucc s).bigradedUnblockedHomologyPieceEquivOfMem R G
    (G.val.stabilizeXSuccHomologyEquiv s R)
    (fun _ _ hy ↦ by
      simpa only [GridDiagram.stabilizeXSuccHomologyEquiv_apply] using
        G.stabilizeXSuccHomologyMap_mem_bigradedUnblockedHomologyPiece s R hy)
    g

/-- On homogeneous classes, the piece equivalence is the specified homology comparison. -/
@[simp]
theorem coe_stabilizeXSuccHomologyPieceEquiv_apply (g : ℤ × ℤ)
    (y : (G.stabilizeXSucc s).bigradedUnblockedHomologyPiece R g) :
    (G.stabilizeXSuccHomologyPieceEquiv s R g y : G.val.unblockedHomology R) =
      G.val.stabilizeXSuccHomologyMap s R y := by
  rw [stabilizeXSuccHomologyPieceEquiv, coe_bigradedUnblockedHomologyPieceEquivOfMem,
    GridDiagram.stabilizeXSuccHomologyEquiv_apply]

/-- The inverse piece comparison is the inverse of the specified total homology equivalence. -/
@[simp]
theorem coe_stabilizeXSuccHomologyPieceEquiv_symm_apply (g : ℤ × ℤ)
    (y : G.bigradedUnblockedHomologyPiece R g) :
    ((G.stabilizeXSuccHomologyPieceEquiv s R g).symm y :
        (G.stabilizeXSucc s).val.unblockedHomology R) =
      (G.val.stabilizeXSuccHomologyEquiv s R).symm y := by
  rw [stabilizeXSuccHomologyPieceEquiv]
  exact (G.stabilizeXSucc s).coe_bigradedUnblockedHomologyPieceEquivOfMem_symm R G _ _ g y

end TauCeti.OddComponentGridDiagram

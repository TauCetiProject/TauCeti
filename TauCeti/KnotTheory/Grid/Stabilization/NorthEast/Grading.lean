/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.Basic

/-!
# The bigrading of the north-east stabilization map

The north-east corner `X`-stabilization has new `O`-marking in the north-east corner of its
block. Its comparison map is the conjugate of the south-west comparison by torus half-turns.
Both half-turns preserve the absolute `O`-Maslov and Alexander gradings, and variable reversal
preserves total monomial degree. Consequently the specified north-east chain map has bidegree
`(0, 0)`, with each coefficient variable in bidegree `(-2, -1)`.

The Alexander comparison descends to the specified bijective semilinear map on unblocked
homology. An odd component count is required only to use integer Alexander degrees; the
coefficient ring can be any commutative ring of characteristic two.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 5.2;
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.2.
-/

public section

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (s : Fin n)

/-- The north-east corner `X`-stabilization of a diagram with an odd number of components. -/
abbrev stabilizeXSucc : OddComponentGridDiagram (n + 1) :=
  ⟨G.1.stabilizeX s.succ (G.1.X s).succ s,
    (G.1.componentCount_stabilizeX _ _ _).symm ▸ G.2⟩

/-- The underlying north-east stabilized diagram. -/
@[simp]
theorem val_stabilizeXSucc :
    (G.stabilizeXSucc s).1 = G.1.stabilizeX s.succ (G.1.X s).succ s :=
  (rfl)

/-- A half-turn exchanges the north-east and south-west corner stabilizations. -/
@[simp]
theorem rotate_stabilizeXSucc : (G.stabilizeXSucc s).rotate = G.rotate.stabilizeX s.rev := by
  apply Subtype.ext
  simp only [val_stabilizeX, GridDiagram.rotate_stabilizeX_succ]

variable (R : Type*) [CommRing R] [CharP R 2]

/-- The north-east stabilization chain map preserves the `O`-Maslov--Alexander bigrading. -/
theorem stabilizeXSuccChainMap_mem_bigradedChainMinusPiece {g : ℤ × ℤ}
    {c : GridChainMinus R (n + 1)}
    (hc : c ∈ (G.stabilizeXSucc s).bigradedChainMinusPiece R g) :
    G.1.stabilizeXSuccChainMap s R c ∈ G.bigradedChainMinusPiece R g := by
  have hturn := (G.stabilizeXSucc s).halfTurnRenameEquiv_mem_bigradedChainMinusPiece R hc
  rw [rotate_stabilizeXSucc] at hturn
  have hmap := G.rotate.stabilizeXCoefficientFormula_mem_bigradedChainMinusPiece s.rev R hturn
  have hout := G.rotate.halfTurnRenameEquiv_mem_bigradedChainMinusPiece R hmap
  rw [rotate_rotate] at hout
  rw [GridDiagram.stabilizeXSuccChainMap_apply, GridDiagram.stabilizeXChainMap_apply]
  exact hout

/-- The north-east stabilization chain map preserves the integer Alexander grading. -/
theorem stabilizeXSuccChainMap_mem_alexanderChainMinusPiece {a : ℤ}
    {c : GridChainMinus R (n + 1)}
    (hc : c ∈ (G.stabilizeXSucc s).alexanderChainMinusPiece R a) :
    G.1.stabilizeXSuccChainMap s R c ∈ G.alexanderChainMinusPiece R a := by
  have hturn := (G.stabilizeXSucc s).halfTurnRenameEquiv_mem_alexanderChainMinusPiece R hc
  rw [rotate_stabilizeXSucc] at hturn
  have hmap := G.rotate.stabilizeXMap_mem_alexanderChainMinusPiece s.rev R hturn
  rw [GridDiagram.stabilizeXMap_f_apply] at hmap
  have hout := G.rotate.halfTurnRenameEquiv_mem_alexanderChainMinusPiece R hmap
  rw [rotate_rotate] at hout
  rw [GridDiagram.stabilizeXSuccChainMap_apply, GridDiagram.stabilizeXChainMap_apply]
  exact hout

/-- The specified north-east stabilization comparison preserves Alexander degree on `GH⁻`. -/
theorem stabilizeXSuccHomologyMap_mem_alexanderUnblockedHomologyGrading_piece {a : ℤ}
    {y : (G.stabilizeXSucc s).1.unblockedHomology R}
    (hy : y ∈ ((G.stabilizeXSucc s).alexanderUnblockedHomologyGrading R).piece a) :
    G.1.stabilizeXSuccHomologyMap s R y ∈
      (G.alexanderUnblockedHomologyGrading R).piece a := by
  rw [mem_alexanderUnblockedHomologyGrading_piece_iff, mem_alexanderHomologyGrading_piece_iff]
    at hy ⊢
  obtain ⟨w, hw, heq⟩ := hy
  obtain rfl : y = (G.stabilizeXSucc s).1.unblockedHomologyClass R w := by
    apply (ModuleCat.mono_iff_injective
      ((G.stabilizeXSucc s).1.unblockedHomologyIso R).hom).mp inferInstance
    rw [GridDiagram.unblockedHomologyIso_hom_unblockedHomologyClass, heq]
  rw [GridDiagram.stabilizeXSuccHomologyMap_unblockedHomologyClass]
  refine ⟨⟨G.1.stabilizeXSuccChainMap s R w,
    G.1.stabilizeXSuccChainMap_mem_ker s R w.2⟩,
    G.stabilizeXSuccChainMap_mem_alexanderChainMinusPiece s R hw, ?_⟩
  exact (GridDiagram.unblockedHomologyIso_hom_unblockedHomologyClass _ _ _).symm

end TauCeti.OddComponentGridDiagram

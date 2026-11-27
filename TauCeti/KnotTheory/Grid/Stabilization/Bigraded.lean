/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Basic
public import TauCeti.KnotTheory.Grid.Stabilization.Components
public import TauCeti.KnotTheory.Grid.Stabilization.Homology
public import TauCeti.KnotTheory.Grid.Stabilization.Map.Grading

/-!
# Bigraded stabilization invariance of unblocked grid homology

For the stabilization splitting an `X`-marking, the comparison on `GH⁻` is a bijection and
preserves both O-Maslov and Alexander degrees. Its inverse also preserves the bigrading,
giving specified linear equivalences on every homogeneous homology piece.

Chain-level preservation holds over a commutative ring. Homology-level preservation,
reflection, and the piece equivalences require characteristic two (`[CommRing R] [CharP R 2]`).

The equivalences are over the ground ring. The total comparison retains its semilinearity
along the renaming that merges the two variables in the stabilization block. Only the
stabilization `G.stabilizeX s.castSucc (G.X s).castSucc s` is treated here.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2;
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.2.
-/

public section

open MvPolynomial

namespace TauCeti

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (s : Fin n)
    (R : Type*) [CommRing R]

/-- The stabilization comparison on chains preserves both gradings. -/
theorem stabilizeXChainMap_mem_bigradedChainMinusPiece {g : ℤ × ℤ}
    {c : GridChainMinus R (n + 1)} (hc : c ∈ bigradedChainMinusPiece
      ⟨G.val.stabilizeX s.castSucc (G.val.X s).castSucc s,
        (G.val.componentCount_stabilizeX _ _ _).symm ▸ G.property⟩ R g) :
    G.val.stabilizeXChainMap s R c ∈ G.bigradedChainMinusPiece R g := by
  have hG' : G.stabilizeX s = ⟨G.val.stabilizeX s.castSucc (G.val.X s).castSucc s,
      (G.val.componentCount_stabilizeX _ _ _).symm ▸ G.property⟩ := Subtype.ext (G.val_stabilizeX s)
  rw [← hG'] at hc
  rw [GridDiagram.stabilizeXChainMap_apply]
  exact G.stabilizeXCoefficientFormula_mem_bigradedChainMinusPiece s R hc

variable [CharP R 2]

/-- The stabilization comparison on homology preserves both O-Maslov and Alexander degrees. -/
theorem stabilizeXHomologyMap_mem_bigradedUnblockedHomologyPiece {g : ℤ × ℤ}
    {y : (G.val.stabilizeX s.castSucc (G.val.X s).castSucc s).unblockedHomology R}
    (hy : y ∈ bigradedUnblockedHomologyPiece
      ⟨G.val.stabilizeX s.castSucc (G.val.X s).castSucc s,
        (G.val.componentCount_stabilizeX _ _ _).symm ▸ G.property⟩ R g) :
    G.val.stabilizeXHomologyMap s R y ∈ G.bigradedUnblockedHomologyPiece R g := by
  obtain ⟨z, hz, rfl⟩ := (mem_bigradedUnblockedHomologyPiece_iff _ R).mp hy
  rw [GridDiagram.stabilizeXHomologyMap_unblockedHomologyClass]
  exact G.unblockedHomologyClass_mem_bigradedUnblockedHomologyPiece R
    (G.stabilizeXChainMap_mem_bigradedChainMinusPiece s R hz)

/-- The comparison reflects homology bidegrees as well as preserving them. -/
@[simp]
theorem stabilizeXHomologyMap_mem_bigradedUnblockedHomologyPiece_iff (g : ℤ × ℤ)
    (y : (G.val.stabilizeX s.castSucc (G.val.X s).castSucc s).unblockedHomology R) :
    G.val.stabilizeXHomologyMap s R y ∈ G.bigradedUnblockedHomologyPiece R g ↔
      y ∈ bigradedUnblockedHomologyPiece
        ⟨G.val.stabilizeX s.castSucc (G.val.X s).castSucc s,
          (G.val.componentCount_stabilizeX _ _ _).symm ▸ G.property⟩ R g := by
  simpa only [GridDiagram.stabilizeXHomologyEquiv_apply] using
    mem_bigradedUnblockedHomologyPiece_iff_of_linearEquiv
      ⟨G.val.stabilizeX s.castSucc (G.val.X s).castSucc s,
        (G.val.componentCount_stabilizeX _ _ _).symm ▸ G.property⟩
      R G (G.val.stabilizeXHomologyEquiv s R)
      (fun _ _ hy ↦ by
        simpa only [GridDiagram.stabilizeXHomologyEquiv_apply] using
          G.stabilizeXHomologyMap_mem_bigradedUnblockedHomologyPiece s R hy)
      g y

/-- The specified stabilization comparison identifies each homogeneous homology piece with the
piece of the same bidegree in the original grid. -/
noncomputable def stabilizeXHomologyPieceEquiv (g : ℤ × ℤ) :
    bigradedUnblockedHomologyPiece
      ⟨G.val.stabilizeX s.castSucc (G.val.X s).castSucc s,
        (G.val.componentCount_stabilizeX _ _ _).symm ▸ G.property⟩ R g ≃ₗ[R]
      G.bigradedUnblockedHomologyPiece R g :=
  bigradedUnblockedHomologyPieceEquivOfMem
    ⟨G.val.stabilizeX s.castSucc (G.val.X s).castSucc s,
      (G.val.componentCount_stabilizeX _ _ _).symm ▸ G.property⟩
    R G (G.val.stabilizeXHomologyEquiv s R)
    (fun _ _ hy ↦ by
      simpa only [GridDiagram.stabilizeXHomologyEquiv_apply] using
        G.stabilizeXHomologyMap_mem_bigradedUnblockedHomologyPiece s R hy)
    g

/-- On homogeneous classes, the piece equivalence is the specified homology comparison. -/
@[simp]
theorem coe_stabilizeXHomologyPieceEquiv_apply (g : ℤ × ℤ)
    (y : bigradedUnblockedHomologyPiece
      ⟨G.val.stabilizeX s.castSucc (G.val.X s).castSucc s,
        (G.val.componentCount_stabilizeX _ _ _).symm ▸ G.property⟩ R g) :
    (G.stabilizeXHomologyPieceEquiv s R g y : G.val.unblockedHomology R) =
      G.val.stabilizeXHomologyMap s R y := by
  rw [stabilizeXHomologyPieceEquiv, coe_bigradedUnblockedHomologyPieceEquivOfMem,
    GridDiagram.stabilizeXHomologyEquiv_apply]

/-- The inverse piece comparison is the inverse of the specified total homology equivalence. -/
@[simp]
theorem coe_stabilizeXHomologyPieceEquiv_symm_apply (g : ℤ × ℤ)
    (y : G.bigradedUnblockedHomologyPiece R g) :
    ((G.stabilizeXHomologyPieceEquiv s R g).symm y :
        (G.val.stabilizeX s.castSucc (G.val.X s).castSucc s).unblockedHomology R) =
      (G.val.stabilizeXHomologyEquiv s R).symm y := by
  rw [stabilizeXHomologyPieceEquiv]
  exact coe_bigradedUnblockedHomologyPieceEquivOfMem_symm _ R G _ _ g y

end OddComponentGridDiagram

end TauCeti

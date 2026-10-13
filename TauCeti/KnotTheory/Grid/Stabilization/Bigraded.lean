/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded
public import TauCeti.KnotTheory.Grid.Stabilization.Homology

/-!
# Bigraded stabilization invariance of unblocked grid homology

For the stabilization splitting an `X`-marking, the comparison on `GH⁻` is a bijection and
preserves both O-Maslov and Alexander degrees. Its inverse also preserves the bigrading,
giving specified linear equivalences on every homogeneous homology piece.

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
    (R : Type*) [CommRing R] [CharP R 2]

/-- The stabilization comparison on chains preserves both gradings. -/
theorem stabilizeXChainMap_mem_bigradedChainMinusPiece {g : ℤ × ℤ}
    {c : GridChainMinus R (n + 1)} (hc : c ∈ bigradedChainMinusPiece
      ⟨G.1.stabilizeX s.castSucc (G.1.X s).castSucc s,
        (G.1.componentCount_stabilizeX _ _ _).symm ▸ G.2⟩ R g) :
    G.1.stabilizeXChainMap s R c ∈ G.bigradedChainMinusPiece R g := by
  have hG' : G.stabilizeX s = ⟨G.1.stabilizeX s.castSucc (G.1.X s).castSucc s,
      (G.1.componentCount_stabilizeX _ _ _).symm ▸ G.2⟩ := Subtype.ext (G.val_stabilizeX s)
  rw [← hG'] at hc
  have h := G.stabilizeXMap_mem_bigradedChainMinusPiece s R hc
  rwa [GridDiagram.stabilizeXMap_f_apply, ← GridDiagram.stabilizeXChainMap_apply] at h

/-- The stabilization comparison on homology preserves both O-Maslov and Alexander degrees. -/
theorem stabilizeXHomologyMap_mem_bigradedUnblockedHomologyPiece {g : ℤ × ℤ}
    {y : (G.1.stabilizeX s.castSucc (G.1.X s).castSucc s).unblockedHomology R}
    (hy : y ∈ bigradedUnblockedHomologyPiece
      ⟨G.1.stabilizeX s.castSucc (G.1.X s).castSucc s,
        (G.1.componentCount_stabilizeX _ _ _).symm ▸ G.2⟩ R g) :
    G.1.stabilizeXHomologyMap s R y ∈ G.bigradedUnblockedHomologyPiece R g := by
  obtain ⟨z, hz, rfl⟩ := (mem_bigradedUnblockedHomologyPiece_iff _ R).mp hy
  rw [GridDiagram.stabilizeXHomologyMap_unblockedHomologyClass]
  exact G.unblockedHomologyClass_mem_bigradedUnblockedHomologyPiece R
    (G.stabilizeXChainMap_mem_bigradedChainMinusPiece s R hz)

/-- The comparison reflects homology bidegrees as well as preserving them. -/
@[simp]
theorem stabilizeXHomologyMap_mem_bigradedUnblockedHomologyPiece_iff (g : ℤ × ℤ)
    (y : (G.1.stabilizeX s.castSucc (G.1.X s).castSucc s).unblockedHomology R) :
    G.1.stabilizeXHomologyMap s R y ∈ G.bigradedUnblockedHomologyPiece R g ↔
      y ∈ bigradedUnblockedHomologyPiece
        ⟨G.1.stabilizeX s.castSucc (G.1.X s).castSucc s,
          (G.1.componentCount_stabilizeX _ _ _).symm ▸ G.2⟩ R g := by
  classical
  let G' : OddComponentGridDiagram (n + 1) := ⟨G.1.stabilizeX s.castSucc
    (G.1.X s).castSucc s, (G.1.componentCount_stabilizeX _ _ _).symm ▸ G.2⟩
  let := (G.isInternal_bigradedUnblockedHomologyPiece R).chooseDecomposition
  let := (G'.isInternal_bigradedUnblockedHomologyPiece R).chooseDecomposition
  constructor
  · intro hy
    have hproj := DirectSum.map_decompose_shift
      (G'.bigradedUnblockedHomologyPiece R)
      (G.bigradedUnblockedHomologyPiece R) (G.1.stabilizeXHomologyMap s R).toAddMonoidHom
      id Function.injective_id (fun _ _ hz =>
        G.stabilizeXHomologyMap_mem_bigradedUnblockedHomologyPiece s R hz) g y
    simp only [LinearMap.toAddMonoidHom_coe, id_eq] at hproj
    rw [DirectSum.decompose_of_mem_same _ hy] at hproj
    have heq := (G.1.stabilizeXHomologyMap_bijective s R).injective hproj
    rw [← heq]
    exact SetLike.coe_mem _
  · exact G.stabilizeXHomologyMap_mem_bigradedUnblockedHomologyPiece s R

/-- The specified stabilization comparison identifies each homogeneous homology piece with the
piece of the same bidegree in the original grid. -/
noncomputable def stabilizeXHomologyPieceEquiv (g : ℤ × ℤ) :
    bigradedUnblockedHomologyPiece
      ⟨G.1.stabilizeX s.castSucc (G.1.X s).castSucc s,
        (G.1.componentCount_stabilizeX _ _ _).symm ▸ G.2⟩ R g ≃ₗ[R]
      G.bigradedUnblockedHomologyPiece R g :=
  (G.1.stabilizeXHomologyEquiv s R).ofSubmodules _ _ (by
    ext y
    rw [Submodule.mem_map_equiv]
    have h := G.stabilizeXHomologyMap_mem_bigradedUnblockedHomologyPiece_iff s R g
      ((G.1.stabilizeXHomologyEquiv s R).symm y)
    rw [← GridDiagram.stabilizeXHomologyEquiv_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm)

/-- On homogeneous classes, the piece equivalence is the specified homology comparison. -/
@[simp]
theorem coe_stabilizeXHomologyPieceEquiv_apply (g : ℤ × ℤ)
    (y : bigradedUnblockedHomologyPiece
      ⟨G.1.stabilizeX s.castSucc (G.1.X s).castSucc s,
        (G.1.componentCount_stabilizeX _ _ _).symm ▸ G.2⟩ R g) :
    (G.stabilizeXHomologyPieceEquiv s R g y : G.1.unblockedHomology R) =
      G.1.stabilizeXHomologyMap s R y := by
  rw [stabilizeXHomologyPieceEquiv, LinearEquiv.ofSubmodules_apply,
    GridDiagram.stabilizeXHomologyEquiv_apply]

/-- The inverse piece comparison is the inverse of the specified total homology equivalence. -/
@[simp]
theorem coe_stabilizeXHomologyPieceEquiv_symm_apply (g : ℤ × ℤ)
    (y : G.bigradedUnblockedHomologyPiece R g) :
    ((G.stabilizeXHomologyPieceEquiv s R g).symm y :
        (G.1.stabilizeX s.castSucc (G.1.X s).castSucc s).unblockedHomology R) =
      (G.1.stabilizeXHomologyEquiv s R).symm y := by
  rw [stabilizeXHomologyPieceEquiv, LinearEquiv.ofSubmodules_symm_apply]

end OddComponentGridDiagram

end TauCeti

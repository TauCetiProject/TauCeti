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
      ⟨G.1.stabilizeX s.castSucc (G.1.X s).castSucc s,
        (G.1.componentCount_stabilizeX _ _ _).symm ▸ G.2⟩ R g) :
    G.1.stabilizeXChainMap s R c ∈ G.bigradedChainMinusPiece R g := by
  classical
  have hG' : G.stabilizeX s = ⟨G.1.stabilizeX s.castSucc (G.1.X s).castSucc s,
      (G.1.componentCount_stabilizeX _ _ _).symm ▸ G.2⟩ := Subtype.ext (G.val_stabilizeX s)
  rw [← hG', mem_bigradedChainMinusPiece] at hc
  rw [mem_bigradedChainMinusPiece]
  intro x e he
  rw [GridDiagram.stabilizeXChainMap_apply, Finsupp.mapRange_apply] at he
  -- Trace an output monomial through renaming, the off-center projection, and a rectangle.
  obtain ⟨u, hu, rfl⟩ : ∃ u ∈ (G.1.stabilizeXOffCenterToCenter s R
      (G.1.stabilizeXOffCenterProjection s R c) x).support, u.mapDomain s.predAbove = e := by
    by_contra! h
    exact (MvPolynomial.mem_support_iff.mp he) (coeff_rename_eq_zero _ _ _ fun u hu =>
      MvPolynomial.notMem_support_iff.mp fun hu' => h u hu' hu)
  rw [GridDiagram.stabilizeXOffCenterToCenter_apply, Finsupp.sum] at hu
  obtain ⟨y, -, huy⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hu)
  obtain ⟨d, hd, d', hd', rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ huy)
  obtain ⟨r, hr, rfl⟩ :=
    GridDiagram.exists_mem_XHomotopyRectangles_of_mem_support_XHomotopyCoefficient _ R hd'
  rw [GridDiagram.stabilizeXOffCenterProjection_apply] at hd
  have hM := G.1.maslovOℤ_stabilizeX_eq_of_isEmpty s x
    ((GridDiagram.mem_XHomotopyRectangles _ _ r).mp hr).1
  have hA := G.1.alexander_stabilizeX_eq_of_mem_XHomotopyRectangles s x hr
  rw [← val_stabilizeX, alexander_eq_intCast, G.alexander_eq_intCast] at hA
  have hA' : (G.stabilizeX s).alexanderℤ y.1 = G.alexanderℤ x -
      ((G.stabilizeX s).1.OColumns r.toGridRectangle).card := by
    exact_mod_cast hA
  rw [val_stabilizeX] at hA'
  rw [← hc y.1 d hd]
  -- The rectangle grading shifts cancel the degree of its coefficient monomial.
  refine Prod.ext ?_ ?_ <;>
    simp only [monomialBidegree_fst, monomialBidegree_snd, Finsupp.degree_mapDomain, map_add,
      map_sum, Finsupp.degree_single, Finset.sum_const, smul_eq_mul, mul_one, val_stabilizeX] <;>
    push_cast <;> omega

variable [CharP R 2]

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
  let G' : OddComponentGridDiagram (n + 1) := ⟨G.1.stabilizeX s.castSucc
    (G.1.X s).castSucc s, (G.1.componentCount_stabilizeX _ _ _).symm ▸ G.2⟩
  have he : LinearMap.IsHomogeneous (G.1.stabilizeXHomologyEquiv s R).toLinearMap
      (G'.bigradedUnblockedHomologyGrading R).piece
      (G.bigradedUnblockedHomologyGrading R).piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro p z hz
    rw [bigradedUnblockedHomologyGrading_piece] at hz
    simpa only [add_zero, bigradedUnblockedHomologyGrading_piece,
      LinearEquiv.coe_coe, GridDiagram.stabilizeXHomologyEquiv_apply] using
      G.stabilizeXHomologyMap_mem_bigradedUnblockedHomologyPiece s R hz
  constructor
  · intro hy
    rw [← bigradedUnblockedHomologyGrading_piece,
      ← GridDiagram.stabilizeXHomologyEquiv_apply] at hy
    have h := he.linearEquiv_symm.map_mem hy
    simpa only [add_zero, bigradedUnblockedHomologyGrading_piece,
      LinearEquiv.coe_coe, ← GridDiagram.stabilizeXHomologyEquiv_apply,
      LinearEquiv.symm_apply_apply] using h
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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Basic
public import TauCeti.KnotTheory.Grid.SimplyBlocked.HalfTurn
public import TauCeti.KnotTheory.Grid.Homology.HatBigrading

/-!
# The half-turn on one-variable-specialization grid homology

Blocking a single `O`-marking agrees with simply blocked homology `G-hat` for knot grids.
For links, simply blocked homology instead blocks one `O`-marking per component.

The half-turn exchanges south-west and north-east corner stabilizations while transporting
the blocked `O`-marking from `i` to `i.rev`. This feeds the north-east stabilization comparison
in `Stabilization/NorthEast/SimplyBlocked.lean`.

Over characteristic-two commutative rings, the semilinear homology equivalence is defined for
arbitrary grid diagrams. On odd-component diagrams it preserves the full `(O-Maslov, Alexander)`
bigrading. Its coefficient-linear presentation uses `ModuleCat.restrictScalars`, and restricts
to each homogeneous piece. The equivalence and its inverse are characterized on cycle classes.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2.
-/

public section

open CategoryTheory

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n)
  (R : Type*) [CommRing R] [CharP R 2] (i : Fin n)

local notation "σ" => ((AlgEquiv.toRingEquiv (simplyBlockedHalfTurnRenameEquiv R i)) :
  MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ i.rev} R)
local notation "BaseA" => ModuleCat.restrictScalars
  (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)
local notation "BaseB" => ModuleCat.restrictScalars
  (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i.rev} R)

/-- The half-turn identifies the cycle modules of any grid diagram, transporting the blocked
marking along `Fin.rev`. -/
noncomputable def oneVariableSpecializationRotateCyclesEquiv :
    LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom ≃ₛₗ[σ]
      LinearMap.ker ((G.rotate.simplyBlockedComplex R i.rev).d () ()).hom :=
  oneVariableSpecializationCyclesEquivOfIntertwining R i i.rev σ
    (GridChain.simplyBlockedHalfTurnEquiv R i)
    (G.simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv R i)

/-- On explicit chains, the cycle equivalence is the half-turn with variable renaming. -/
@[simp]
theorem simplyBlockedChainEquiv_oneVariableSpecializationRotateCyclesEquiv
    (z : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) :
    G.rotate.simplyBlockedChainEquiv R i.rev (G.oneVariableSpecializationRotateCyclesEquiv R i z) =
      GridChain.simplyBlockedHalfTurnEquiv R i (G.simplyBlockedChainEquiv R i z) := by
  exact simplyBlockedChainEquiv_oneVariableSpecializationCyclesEquivOfIntertwining
    R i i.rev σ (GridChain.simplyBlockedHalfTurnEquiv R i)
      (G.simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv R i) z

/-- The inverse cycle equivalence is the inverse half-turn on explicit chains. -/
@[simp]
theorem simplyBlockedChainEquiv_oneVariableSpecializationRotateCyclesEquiv_symm
    (z : LinearMap.ker ((G.rotate.simplyBlockedComplex R i.rev).d () ()).hom) :
    G.simplyBlockedChainEquiv R i ((G.oneVariableSpecializationRotateCyclesEquiv R i).symm z) =
      (GridChain.simplyBlockedHalfTurnEquiv R i).symm
        (G.rotate.simplyBlockedChainEquiv R i.rev z) := by
  exact simplyBlockedChainEquiv_oneVariableSpecializationCyclesEquivOfIntertwining_symm
    R i i.rev σ (GridChain.simplyBlockedHalfTurnEquiv R i)
      (G.simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv R i) z

/-- The half-turn on one-variable specialization homology of an arbitrary grid diagram,
semilinear along the renaming of surviving variables. -/
noncomputable def oneVariableSpecializationRotateHomologyEquiv :
    (G.simplyBlockedComplex R i).homology () ≃ₛₗ[σ]
      (G.rotate.simplyBlockedComplex R i.rev).homology () :=
  oneVariableSpecializationHomologyEquivOfIntertwining R i i.rev σ
    (GridChain.simplyBlockedHalfTurnEquiv R i)
    (G.simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv R i)

/-- A cycle class maps to the class of its half-turned cycle. -/
@[simp↓]
theorem oneVariableSpecializationRotateHomologyEquiv_oneVariableSpecializationHomologyClass
    (z : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) :
    G.oneVariableSpecializationRotateHomologyEquiv R i
        (G.oneVariableSpecializationHomologyClass R i z) =
      G.rotate.oneVariableSpecializationHomologyClass R i.rev
        (G.oneVariableSpecializationRotateCyclesEquiv R i z) := by
  exact oneVariableSpecializationHomologyEquivOfIntertwining_oneVariableSpecializationHomologyClass
    R i i.rev σ (GridChain.simplyBlockedHalfTurnEquiv R i)
      (G.simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv R i) z

/-- The inverse maps a cycle class by the inverse cycle equivalence. -/
@[simp↓]
theorem oneVariableSpecializationRotateHomologyEquiv_symm_oneVariableSpecializationHomologyClass
    (z : LinearMap.ker ((G.rotate.simplyBlockedComplex R i.rev).d () ()).hom) :
    (G.oneVariableSpecializationRotateHomologyEquiv R i).symm
        (G.rotate.oneVariableSpecializationHomologyClass R i.rev z) =
      G.oneVariableSpecializationHomologyClass R i
        ((G.oneVariableSpecializationRotateCyclesEquiv R i).symm z) := by
  exact
    oneVariableSpecializationHomologyEquivOfIntertwining_symm_oneVariableSpecializationHomologyClass
      R i i.rev σ (GridChain.simplyBlockedHalfTurnEquiv R i)
        (G.simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv R i) z

/-- The half-turn is linear over coefficient scalars on the specified restricted-scalar carriers. -/
noncomputable def oneVariableSpecializationRotateHomologyCoefficientEquiv :
    (BaseA).obj ((G.simplyBlockedComplex R i).homology ()) ≃ₗ[R]
      (BaseB).obj ((G.rotate.simplyBlockedComplex R i.rev).homology ()) :=
  ModuleCat.restrictScalarsLinearEquiv
    (MvPolynomial.C : R →+* _) (MvPolynomial.C : R →+* _)
    (G.oneVariableSpecializationRotateHomologyEquiv R i)
    (simplyBlockedHalfTurnRenameEquiv_C R i)

/-- Restricting coefficient scalars preserves the half-turn. -/
theorem oneVariableSpecializationRotateHomologyCoefficientEquiv_apply
    (y : (BaseA).obj ((G.simplyBlockedComplex R i).homology ())) :
    G.oneVariableSpecializationRotateHomologyCoefficientEquiv R i y =
      G.oneVariableSpecializationRotateHomologyEquiv R i y := by
  exact ModuleCat.restrictScalarsLinearEquiv_apply
    (MvPolynomial.C : R →+* _) (MvPolynomial.C : R →+* _)
    (G.oneVariableSpecializationRotateHomologyEquiv R i)
    (simplyBlockedHalfTurnRenameEquiv_C R i) y

/-- Restricting coefficient scalars preserves the inverse half-turn. -/
theorem oneVariableSpecializationRotateHomologyCoefficientEquiv_symm_apply
    (y : (BaseB).obj ((G.rotate.simplyBlockedComplex R i.rev).homology ())) :
    (G.oneVariableSpecializationRotateHomologyCoefficientEquiv R i).symm y =
      (G.oneVariableSpecializationRotateHomologyEquiv R i).symm y := by
  exact ModuleCat.restrictScalarsLinearEquiv_symm_apply
    (MvPolynomial.C : R →+* _) (MvPolynomial.C : R →+* _)
    (G.oneVariableSpecializationRotateHomologyEquiv R i)
    (simplyBlockedHalfTurnRenameEquiv_C R i) y

end TauCeti.GridDiagram

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)
  (R : Type*) [CommRing R] [CharP R 2] (i : Fin n)

local notation "BaseA" => ModuleCat.restrictScalars
  (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)
local notation "BaseB" => ModuleCat.restrictScalars
  (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i.rev} R)

/-- The half-turn preserves both homology degrees on every odd-component grid diagram. -/
theorem isHomogeneous_oneVariableSpecializationRotateHomologyCoefficientEquiv :
    LinearMap.IsHomogeneous
      (G.1.oneVariableSpecializationRotateHomologyCoefficientEquiv R i).toLinearMap
      (G.bigradedHatHomologyGrading R i).piece
      (G.rotate.bigradedHatHomologyGrading R i.rev).piece 0 := by
  apply G.isHomogeneous_oneVariableSpecializationHomologyMap R i G.rotate i.rev
    (G.1.oneVariableSpecializationRotateHomologyCoefficientEquiv R i).toLinearMap
    (G.1.oneVariableSpecializationRotateCyclesEquiv R i)
  · intro z
    exact (G.1.oneVariableSpecializationRotateHomologyCoefficientEquiv_apply R i _).trans
      (G.1.oneVariableSpecializationRotateHomologyEquiv_oneVariableSpecializationHomologyClass
        R i z)
  · intro g z hz
    rw [GridDiagram.simplyBlockedChainEquiv_oneVariableSpecializationRotateCyclesEquiv]
    exact (G.simplyBlockedHalfTurnEquiv_mem_bigradedChainHatPiece_iff R i).2 hz

/-- The coefficient-linear half-turn preserves and reflects homogeneous-piece membership. -/
@[simp↓]
theorem oneVariableSpecializationRotateHomologyCoefficientEquiv_mem_bigradedHatHomologyPiece_iff
    (g : ℤ × ℤ) (y : (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) :
    G.1.oneVariableSpecializationRotateHomologyCoefficientEquiv R i y ∈
        G.rotate.bigradedHatHomologyPiece R i.rev g ↔
      y ∈ G.bigradedHatHomologyPiece R i g := by
  simpa only [bigradedHatHomologyGrading_piece] using
    LinearMap.IsHomogeneous.linearEquiv_mem_piece_iff
      (G.isHomogeneous_oneVariableSpecializationRotateHomologyCoefficientEquiv R i) g y

/-- The coefficient-linear inverse half-turn preserves and reflects piece membership. -/
@[simp↓]
theorem
    oneVariableSpecializationRotateHomologyCoefficientEquiv_symm_mem_bigradedHatHomologyPiece_iff
    (g : ℤ × ℤ) (y : (BaseB).obj ((G.1.rotate.simplyBlockedComplex R i.rev).homology ())) :
    (G.1.oneVariableSpecializationRotateHomologyCoefficientEquiv R i).symm y ∈
        G.bigradedHatHomologyPiece R i g ↔
      y ∈ G.rotate.bigradedHatHomologyPiece R i.rev g := by
  simpa only [bigradedHatHomologyGrading_piece] using
    LinearMap.IsHomogeneous.linearEquiv_mem_piece_iff
      (G.isHomogeneous_oneVariableSpecializationRotateHomologyCoefficientEquiv R i).linearEquiv_symm
      g y

/-- The half-turn preserves and reflects homogeneous-piece membership. -/
@[simp↓]
theorem oneVariableSpecializationRotateHomologyEquiv_mem_bigradedHatHomologyPiece_iff
    (g : ℤ × ℤ) (y : (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) :
    (G.1.oneVariableSpecializationRotateHomologyEquiv R i y :
        (BaseB).obj ((G.1.rotate.simplyBlockedComplex R i.rev).homology ())) ∈
        G.rotate.bigradedHatHomologyPiece R i.rev g ↔
      y ∈ G.bigradedHatHomologyPiece R i g := by
  rw [← GridDiagram.oneVariableSpecializationRotateHomologyCoefficientEquiv_apply]
  exact G.oneVariableSpecializationRotateHomologyCoefficientEquiv_mem_bigradedHatHomologyPiece_iff
    R i g y

/-- The inverse half-turn preserves and reflects homogeneous-piece membership. -/
@[simp↓]
theorem oneVariableSpecializationRotateHomologyEquiv_symm_mem_bigradedHatHomologyPiece_iff
    (g : ℤ × ℤ) (y : (BaseB).obj ((G.1.rotate.simplyBlockedComplex R i.rev).homology ())) :
    ((G.1.oneVariableSpecializationRotateHomologyEquiv R i).symm y :
        (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) ∈
        G.bigradedHatHomologyPiece R i g ↔
      y ∈ G.rotate.bigradedHatHomologyPiece R i.rev g := by
  rw [← GridDiagram.oneVariableSpecializationRotateHomologyCoefficientEquiv_symm_apply]
  exact
    G.oneVariableSpecializationRotateHomologyCoefficientEquiv_symm_mem_bigradedHatHomologyPiece_iff
      R i g y

/-- The half-turn identifies the pieces of the same bidegree on odd-component diagrams. -/
noncomputable def oneVariableSpecializationRotateHomologyPieceEquiv (g : ℤ × ℤ) :
    G.bigradedHatHomologyPiece R i g ≃ₗ[R] G.rotate.bigradedHatHomologyPiece R i.rev g :=
  let he := G.isHomogeneous_oneVariableSpecializationRotateHomologyCoefficientEquiv R i
  (LinearEquiv.ofEq _ _ (G.bigradedHatHomologyGrading_piece R i g).symm).trans
    ((he.pieceEquiv g).trans
      (LinearEquiv.ofEq _ _ (G.rotate.bigradedHatHomologyGrading_piece R i.rev g)))

/-- The piece equivalence is the restriction of the total half-turn. -/
@[simp↓]
theorem coe_oneVariableSpecializationRotateHomologyPieceEquiv_apply (g : ℤ × ℤ)
    (y : G.bigradedHatHomologyPiece R i g) :
    (G.oneVariableSpecializationRotateHomologyPieceEquiv R i g y :
        (BaseB).obj ((G.1.rotate.simplyBlockedComplex R i.rev).homology ())) =
      G.1.oneVariableSpecializationRotateHomologyCoefficientEquiv R i y.1 := by
  simp only [oneVariableSpecializationRotateHomologyPieceEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearMap.IsHomogeneous.coe_pieceEquiv_apply]

/-- The inverse piece equivalence is the restriction of the total inverse half-turn. -/
@[simp↓]
theorem coe_oneVariableSpecializationRotateHomologyPieceEquiv_symm_apply (g : ℤ × ℤ)
    (y : G.rotate.bigradedHatHomologyPiece R i.rev g) :
    ((G.oneVariableSpecializationRotateHomologyPieceEquiv R i g).symm y :
        (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) =
      (G.1.oneVariableSpecializationRotateHomologyCoefficientEquiv R i).symm y.1 := by
  simp only [oneVariableSpecializationRotateHomologyPieceEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply,
    LinearMap.IsHomogeneous.coe_pieceEquiv_symm_apply]

end TauCeti.OddComponentGridDiagram

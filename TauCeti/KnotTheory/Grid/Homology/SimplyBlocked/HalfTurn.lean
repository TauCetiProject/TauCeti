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
# The half-turn on simply blocked grid homology

The half-turn exchanges south-west and north-east corner stabilizations while transporting
the blocked `O`-marking from `i` to `i.rev`. This feeds the north-east stabilization comparison
in `Stabilization/NorthEast/SimplyBlocked.lean`.

Over characteristic-two commutative rings, the semilinear homology equivalence is defined for
arbitrary grid diagrams. On odd-component diagrams it preserves the full `(O-Maslov, Alexander)`
bigrading. Its coefficient-linear presentation uses `ModuleCat.restrictScalars`, and restricts
to each homogeneous piece. The equivalence and its inverse are characterized on cycle classes.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2.
The quotient descent follows the existing simply blocked reflection, using Mathlib's
`LinearEquiv.ofSubmodules` and `Submodule.Quotient.equiv`.
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
  apply (GridChain.simplyBlockedHalfTurnEquiv R i).injective
  rw [← simplyBlockedChainEquiv_oneVariableSpecializationRotateCyclesEquiv,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

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
  rw [LinearEquiv.symm_apply_eq,
    oneVariableSpecializationRotateHomologyEquiv_oneVariableSpecializationHomologyClass,
    LinearEquiv.apply_symm_apply]

/-- The half-turn is linear over coefficient scalars on the specified restricted-scalar carriers. -/
noncomputable def oneVariableSpecializationRotateHomologyLinearEquiv :
    (BaseA).obj ((G.simplyBlockedComplex R i).homology ()) ≃ₗ[R]
      (BaseB).obj ((G.rotate.simplyBlockedComplex R i.rev).homology ()) :=
  oneVariableSpecializationHomologyCoefficientEquiv R i i.rev σ
    (G.oneVariableSpecializationRotateHomologyEquiv R i)
    (simplyBlockedHalfTurnRenameEquiv_C R i)

/-- Restricting coefficient scalars preserves the half-turn. -/
theorem oneVariableSpecializationRotateHomologyLinearEquiv_apply
    (y : (BaseA).obj ((G.simplyBlockedComplex R i).homology ())) :
    G.oneVariableSpecializationRotateHomologyLinearEquiv R i y =
      G.oneVariableSpecializationRotateHomologyEquiv R i y := by
  exact oneVariableSpecializationHomologyCoefficientEquiv_apply R i i.rev σ
    (G.oneVariableSpecializationRotateHomologyEquiv R i)
    (simplyBlockedHalfTurnRenameEquiv_C R i) y

/-- Restricting coefficient scalars preserves the inverse half-turn. -/
theorem oneVariableSpecializationRotateHomologyLinearEquiv_symm_apply
    (y : (BaseB).obj ((G.rotate.simplyBlockedComplex R i.rev).homology ())) :
    (G.oneVariableSpecializationRotateHomologyLinearEquiv R i).symm y =
      (G.oneVariableSpecializationRotateHomologyEquiv R i).symm y := by
  exact oneVariableSpecializationHomologyCoefficientEquiv_symm_apply R i i.rev σ
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
theorem isHomogeneous_oneVariableSpecializationRotateHomologyLinearEquiv :
    LinearMap.IsHomogeneous (G.1.oneVariableSpecializationRotateHomologyLinearEquiv R i).toLinearMap
      (G.bigradedHatHomologyGrading R i).piece
      (G.rotate.bigradedHatHomologyGrading R i.rev).piece 0 := by
  apply G.isHomogeneous_oneVariableSpecializationHomologyMap R i G.rotate i.rev
    (G.1.oneVariableSpecializationRotateHomologyLinearEquiv R i).toLinearMap
    (G.1.oneVariableSpecializationRotateCyclesEquiv R i)
  · intro z
    exact (G.1.oneVariableSpecializationRotateHomologyLinearEquiv_apply R i _).trans
      (G.1.oneVariableSpecializationRotateHomologyEquiv_oneVariableSpecializationHomologyClass
        R i z)
  · intro g z hz
    rw [GridDiagram.simplyBlockedChainEquiv_oneVariableSpecializationRotateCyclesEquiv]
    exact (G.simplyBlockedHalfTurnEquiv_mem_bigradedChainHatPiece_iff R i).2 hz

/-- The half-turn preserves and reflects homogeneous-piece membership. -/
@[simp↓]
theorem oneVariableSpecializationRotateHomologyEquiv_mem_bigradedHatHomologyPiece_iff
    (g : ℤ × ℤ) (y : (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) :
    (G.1.oneVariableSpecializationRotateHomologyEquiv R i y :
        (BaseB).obj ((G.1.rotate.simplyBlockedComplex R i.rev).homology ())) ∈
        G.rotate.bigradedHatHomologyPiece R i.rev g ↔
      y ∈ G.bigradedHatHomologyPiece R i g := by
  rw [← GridDiagram.oneVariableSpecializationRotateHomologyLinearEquiv_apply]
  exact G.homologyEquiv_mem_bigradedHatHomologyPiece_iff R i G.rotate i.rev
    (G.1.oneVariableSpecializationRotateHomologyLinearEquiv R i)
    (G.isHomogeneous_oneVariableSpecializationRotateHomologyLinearEquiv R i) g y

/-- The inverse half-turn preserves and reflects homogeneous-piece membership. -/
@[simp↓]
theorem oneVariableSpecializationRotateHomologyEquiv_symm_mem_bigradedHatHomologyPiece_iff
    (g : ℤ × ℤ) (y : (BaseB).obj ((G.1.rotate.simplyBlockedComplex R i.rev).homology ())) :
    ((G.1.oneVariableSpecializationRotateHomologyEquiv R i).symm y :
        (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) ∈
        G.bigradedHatHomologyPiece R i g ↔
      y ∈ G.rotate.bigradedHatHomologyPiece R i.rev g := by
  have h := G.rotate.homologyEquiv_mem_bigradedHatHomologyPiece_iff R i.rev G i
    (G.1.oneVariableSpecializationRotateHomologyLinearEquiv R i).symm
    (G.isHomogeneous_oneVariableSpecializationRotateHomologyLinearEquiv R i).linearEquiv_symm g y
  rw [GridDiagram.oneVariableSpecializationRotateHomologyLinearEquiv_symm_apply] at h
  exact h

/-- The half-turn identifies the pieces of the same bidegree on odd-component diagrams. -/
noncomputable def oneVariableSpecializationRotateHomologyPieceEquiv (g : ℤ × ℤ) :
    G.bigradedHatHomologyPiece R i g ≃ₗ[R] G.rotate.bigradedHatHomologyPiece R i.rev g :=
  G.oneVariableSpecializationHomologyPieceEquivOfHomogeneous R i G.rotate i.rev
    (G.1.oneVariableSpecializationRotateHomologyLinearEquiv R i)
    (G.isHomogeneous_oneVariableSpecializationRotateHomologyLinearEquiv R i) g

/-- The piece equivalence is the restriction of the total half-turn. -/
@[simp↓]
theorem coe_oneVariableSpecializationRotateHomologyPieceEquiv_apply (g : ℤ × ℤ)
    (y : G.bigradedHatHomologyPiece R i g) :
    (G.oneVariableSpecializationRotateHomologyPieceEquiv R i g y :
        (BaseB).obj ((G.1.rotate.simplyBlockedComplex R i.rev).homology ())) =
      G.1.oneVariableSpecializationRotateHomologyLinearEquiv R i y.1 := by
  rw [oneVariableSpecializationRotateHomologyPieceEquiv,
    coe_oneVariableSpecializationHomologyPieceEquivOfHomogeneous_apply]

/-- The inverse piece equivalence is the restriction of the total inverse half-turn. -/
@[simp↓]
theorem coe_oneVariableSpecializationRotateHomologyPieceEquiv_symm_apply (g : ℤ × ℤ)
    (y : G.rotate.bigradedHatHomologyPiece R i.rev g) :
    ((G.oneVariableSpecializationRotateHomologyPieceEquiv R i g).symm y :
        (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) =
      (G.1.oneVariableSpecializationRotateHomologyLinearEquiv R i).symm y.1 := by
  rw [oneVariableSpecializationRotateHomologyPieceEquiv,
    coe_oneVariableSpecializationHomologyPieceEquivOfHomogeneous_symm_apply]

end TauCeti.OddComponentGridDiagram

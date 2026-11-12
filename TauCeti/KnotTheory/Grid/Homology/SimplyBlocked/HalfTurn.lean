/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Equiv.Basic
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Basic
public import TauCeti.KnotTheory.Grid.SimplyBlocked.HalfTurn
public import TauCeti.KnotTheory.Grid.Homology.HatBigrading

/-!
# The half-turn on simply blocked grid homology

The half-turn identifies simply blocked knot-grid homology with that of the rotated diagram,
transporting the blocked column from `i` to `i.rev` and renaming surviving variables. It preserves
the full `(O-Maslov, Alexander)` bigrading and therefore identifies each homogeneous piece.
The equivalence and its inverse are characterized on cycle classes.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2.
The quotient descent follows the existing simply blocked reflection, using Mathlib's
`LinearEquiv.ofSubmodules` and `Submodule.Quotient.equiv`.
-/

public section

open CategoryTheory

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)
  (R : Type*) [CommRing R] [CharP R 2] (i : Fin n)

/-- The half-turn between the categorical chain carriers. -/
private noncomputable def simplyBlockedRotateChainEquiv :
    (G.simplyBlockedComplex R i).X () ≃ₛₗ[
      ((simplyBlockedHalfTurnRenameEquiv R i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ i.rev} R)]
      (G.rotate.simplyBlockedComplex R (i.rev)).X () :=
  (G.simplyBlockedChainEquiv R i).trans <|
    (GridChain.simplyBlockedHalfTurnEquiv R i).trans
      (G.rotate.simplyBlockedChainEquiv R (i.rev)).symm

private theorem simplyBlockedRotateChainEquiv_d
    (z : (G.simplyBlockedComplex R i).X ()) :
    (G.rotate.simplyBlockedComplex R (i.rev)).d () ()
        (simplyBlockedRotateChainEquiv R i z) =
      simplyBlockedRotateChainEquiv R i ((G.simplyBlockedComplex R i).d () () z) := by
  apply (G.rotate.simplyBlockedChainEquiv R (i.rev)).injective
  simp only [simplyBlockedRotateChainEquiv, LinearEquiv.trans_apply,
    simplyBlockedChainEquiv_d, LinearEquiv.apply_symm_apply,
    simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv]

/-- The half-turn identifies the cycle modules, transporting the blocked marking along `Fin.rev`. -/
noncomputable def simplyBlockedRotateCyclesEquiv :
    hG.simplyBlockedCycles R i ≃ₛₗ[
      ((simplyBlockedHalfTurnRenameEquiv R i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ i.rev} R)]
      (G.isKnot_rotate.mpr hG).simplyBlockedCycles R (i.rev) :=
  (simplyBlockedRotateChainEquiv R i).ofSubmodules _ _
    ((simplyBlockedRotateChainEquiv R i).map_ker_of_intertwine _ _
      (simplyBlockedRotateChainEquiv_d R i))

/-- On underlying explicit chains, the cycle equivalence is half-turn with variable renaming. -/
@[simp]
theorem simplyBlockedChainEquiv_simplyBlockedRotateCyclesEquiv
    (z : hG.simplyBlockedCycles R i) :
    G.rotate.simplyBlockedChainEquiv R (i.rev) (hG.simplyBlockedRotateCyclesEquiv R i z) =
      GridChain.simplyBlockedHalfTurnEquiv R i (G.simplyBlockedChainEquiv R i z) := by
  simp only [simplyBlockedRotateCyclesEquiv, LinearEquiv.ofSubmodules_apply,
    simplyBlockedRotateChainEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- On underlying explicit chains, the inverse cycle equivalence is inverse half-turn. -/
@[simp]
theorem simplyBlockedChainEquiv_simplyBlockedRotateCyclesEquiv_symm
    (z : (G.isKnot_rotate.mpr hG).simplyBlockedCycles R (i.rev)) :
    G.simplyBlockedChainEquiv R i ((hG.simplyBlockedRotateCyclesEquiv R i).symm z) =
      (GridChain.simplyBlockedHalfTurnEquiv R i).symm
        (G.rotate.simplyBlockedChainEquiv R (i.rev) z) := by
  apply (GridChain.simplyBlockedHalfTurnEquiv R i).injective
  rw [← simplyBlockedChainEquiv_simplyBlockedRotateCyclesEquiv,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

private theorem map_boundaries_simplyBlockedRotateCyclesEquiv :
    (hG.simplyBlockedBoundaries R i).map
        (hG.simplyBlockedRotateCyclesEquiv R i).toLinearMap =
      (G.isKnot_rotate.mpr hG).simplyBlockedBoundaries R (i.rev) := by
  have hcomp : (hG.simplyBlockedRotateCyclesEquiv R i).toLinearMap.comp
      (hG.simplyBlockedBoundaryMap R i) =
      ((G.isKnot_rotate.mpr hG).simplyBlockedBoundaryMap R i.rev).comp
        (simplyBlockedRotateChainEquiv R i).toLinearMap := by
    ext z : 1
    apply Subtype.ext
    exact (simplyBlockedRotateChainEquiv_d R i z).symm
  rw [← LinearMap.range_comp, hcomp, LinearEquiv.range_comp]

/-- The half-turn on simply blocked knot grid homology, semilinear along the renaming
of the surviving variables and with the blocked column transported to `i.rev`. -/
noncomputable def simplyBlockedHomologyRotateEquiv :
    hG.simplyBlockedHomology R i ≃ₛₗ[
      ((simplyBlockedHalfTurnRenameEquiv R i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ i.rev} R)]
      (G.isKnot_rotate.mpr hG).simplyBlockedHomology R (i.rev) :=
  (hG.simplyBlockedHomologyIsoQuotient R i).toLinearEquiv.trans <|
    (Submodule.Quotient.equiv _ _ (hG.simplyBlockedRotateCyclesEquiv R i)
      (hG.map_boundaries_simplyBlockedRotateCyclesEquiv R i)).trans
        ((G.isKnot_rotate.mpr hG).simplyBlockedHomologyIsoQuotient R (i.rev)).toLinearEquiv.symm

/-- The half-turn sends the homology class of a cycle to the class of its half-turned cycle. -/
@[simp↓]
theorem simplyBlockedHomologyRotateEquiv_oneVariableSpecializationHomologyClass
    (z : hG.simplyBlockedCycles R i) :
    hG.simplyBlockedHomologyRotateEquiv R i (G.oneVariableSpecializationHomologyClass R i z) =
      G.rotate.oneVariableSpecializationHomologyClass R (i.rev)
        (hG.simplyBlockedRotateCyclesEquiv R i z) := by
  simp only [simplyBlockedHomologyRotateEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_eq]
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply,
    simplyBlockedHomologyIsoQuotient_hom_class, simplyBlockedHomologyIsoQuotient_hom_class,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe]

/-- The inverse half-turn sends a cycle class back by the inverse cycle equivalence. -/
@[simp↓]
theorem simplyBlockedHomologyRotateEquiv_symm_oneVariableSpecializationHomologyClass
    (z : (G.isKnot_rotate.mpr hG).simplyBlockedCycles R (i.rev)) :
    (hG.simplyBlockedHomologyRotateEquiv R i).symm
        (G.rotate.oneVariableSpecializationHomologyClass R (i.rev) z) =
      G.oneVariableSpecializationHomologyClass R i
        ((hG.simplyBlockedRotateCyclesEquiv R i).symm z) := by
  rw [LinearEquiv.symm_apply_eq,
    simplyBlockedHomologyRotateEquiv_oneVariableSpecializationHomologyClass,
    LinearEquiv.apply_symm_apply]

end TauCeti.GridDiagram.IsKnot



namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)
    (R : Type*) [CommRing R] [CharP R 2] (i : Fin n)

local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "B" => MvPolynomial {c : Fin n // c ≠ i.rev} R
local notation "BaseA" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* A)
local notation "BaseB" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* B)
local notation "hrot" => G.isKnot_rotate.mpr hG

/-- The half-turn is linear over the coefficient ring, with the coefficient action on each
homology carrier selected by `ModuleCat.restrictScalars`. -/
noncomputable def simplyBlockedHomologyRotateLinearEquiv :
    (BaseA).obj (hG.simplyBlockedHomology R i) ≃ₗ[R]
      (BaseB).obj ((hrot).simplyBlockedHomology R i.rev) :=
  { (hG.simplyBlockedHomologyRotateEquiv R i).toAddEquiv with
    map_smul' := fun r x => by
      -- The selected `R`-actions are restriction along the two coefficient inclusions.
      dsimp only [ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj'] at x ⊢
      change hG.simplyBlockedHomologyRotateEquiv R i ((MvPolynomial.C r : A) • x) =
        (MvPolynomial.C r : B) • hG.simplyBlockedHomologyRotateEquiv R i x
      rw [LinearEquiv.map_smulₛₗ]
      simp only [RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
        simplyBlockedHalfTurnRenameEquiv_C] }

/-- Forgetting semilinearity retains the specified half-turn on homology classes. -/
@[simp]
theorem simplyBlockedHomologyRotateLinearEquiv_apply
    (y : (BaseA).obj (hG.simplyBlockedHomology R i)) :
    hG.simplyBlockedHomologyRotateLinearEquiv R i y =
      hG.simplyBlockedHomologyRotateEquiv R i y :=
  (rfl)

/-- The inverse coefficient-linear map is the inverse of the specified semilinear half-turn. -/
@[simp]
theorem simplyBlockedHomologyRotateLinearEquiv_symm_apply
    (y : (BaseB).obj ((hrot).simplyBlockedHomology R i.rev)) :
    (hG.simplyBlockedHomologyRotateLinearEquiv R i).symm y =
      (hG.simplyBlockedHomologyRotateEquiv R i).symm y :=
  (rfl)

/-- The half-turn preserves the `(O-Maslov, Alexander)` degree on simply blocked homology. -/
theorem isHomogeneous_simplyBlockedHomologyRotateLinearEquiv :
    LinearMap.IsHomogeneous (hG.simplyBlockedHomologyRotateLinearEquiv R i).toLinearMap
      (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading R i).piece
      ((hrot).toOddComponentGridDiagram.bigradedHatHomologyGrading R i.rev).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro g y hy
  rw [add_zero, OddComponentGridDiagram.bigradedHatHomologyGrading_piece] at ⊢
  rw [OddComponentGridDiagram.bigradedHatHomologyGrading_piece] at hy
  obtain ⟨z, hz, rfl⟩ :=
    (hG.toOddComponentGridDiagram.mem_bigradedHatHomologyPiece_iff R i).mp hy
  have hzrot : G.rotate.simplyBlockedChainEquiv R i.rev
      (hG.simplyBlockedRotateCyclesEquiv R i z) ∈
      (hrot).toOddComponentGridDiagram.bigradedChainHatPiece R i.rev g := by
    rw [simplyBlockedChainEquiv_simplyBlockedRotateCyclesEquiv]
    exact hG.toOddComponentGridDiagram.simplyBlockedHalfTurnEquiv_mem_bigradedChainHatPiece R i hz
  have h := (hrot).toOddComponentGridDiagram
    |>.oneVariableSpecializationHomologyClass_mem_bigradedHatHomologyPiece R i.rev hzrot
  have he := (hG.simplyBlockedHomologyRotateLinearEquiv_apply R i
    (G.oneVariableSpecializationHomologyClass R i z)).trans
      (hG.simplyBlockedHomologyRotateEquiv_oneVariableSpecializationHomologyClass R i z)
  exact he.symm ▸ h

/-- The half-turn identifies each simply blocked knot-homology piece with the piece of the
same bidegree in the rotated grid. -/
noncomputable def simplyBlockedHomologyRotatePieceEquiv (g : ℤ × ℤ) :
    hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g ≃ₗ[R]
      (hrot).toOddComponentGridDiagram.bigradedHatHomologyPiece R i.rev g :=
  (hG.simplyBlockedHomologyRotateLinearEquiv R i).ofSubmodules _ _ (by
    ext y
    rw [Submodule.mem_map_equiv]
    constructor
    · intro hy
      rw [← OddComponentGridDiagram.bigradedHatHomologyGrading_piece] at hy
      have h := (hG.isHomogeneous_simplyBlockedHomologyRotateLinearEquiv R i).map_mem hy
      simpa only [add_zero, OddComponentGridDiagram.bigradedHatHomologyGrading_piece,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h
    · intro hy
      rw [← OddComponentGridDiagram.bigradedHatHomologyGrading_piece] at hy
      have h := (hG.isHomogeneous_simplyBlockedHomologyRotateLinearEquiv R i)
        |>.linearEquiv_symm.map_mem hy
      simpa only [add_zero, OddComponentGridDiagram.bigradedHatHomologyGrading_piece,
        LinearEquiv.coe_coe] using h)

/-- On each homogeneous piece the half-turn is the specified total homology equivalence. -/
@[simp]
theorem coe_simplyBlockedHomologyRotatePieceEquiv_apply (g : ℤ × ℤ)
    (y : hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g) :
    (hG.simplyBlockedHomologyRotatePieceEquiv R i g y :
        (BaseB).obj ((hrot).simplyBlockedHomology R i.rev)) =
      hG.simplyBlockedHomologyRotateEquiv R i y.1 :=
  (rfl)

/-- The inverse on a homogeneous piece is the inverse of the total homology equivalence. -/
@[simp]
theorem coe_simplyBlockedHomologyRotatePieceEquiv_symm_apply (g : ℤ × ℤ)
    (y : (hrot).toOddComponentGridDiagram.bigradedHatHomologyPiece R i.rev g) :
    ((hG.simplyBlockedHomologyRotatePieceEquiv R i g).symm y :
        (BaseA).obj (hG.simplyBlockedHomology R i)) =
      (hG.simplyBlockedHomologyRotateEquiv R i).symm y.1 :=
  (rfl)

end TauCeti.GridDiagram.IsKnot

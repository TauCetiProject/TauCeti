/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Series.SimplyBlocked
public import TauCeti.KnotTheory.Grid.Stabilization.SimplyBlocked.Grading
public import TauCeti.KnotTheory.Grid.Stabilization.SimplyBlocked.Homology
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Bigraded stabilization invariance of simply blocked grid homology

Let `G` be a grid diagram of size `n` with an odd number of link components, let `s` and `i` be
columns of `G`, and let `G' = G.stabilizeX s` be the stabilization splitting the `X`-marking of
column `s`, with `j = s.castSucc.succAbove i` the column of `G'` carrying the old `O`-marking of
column `i`. Over any commutative ring `R` of characteristic two, the homologies of the one-variable
specializations at `V_j = 0` and `V_i = 0` carry the internal `(O-Maslov, Alexander)` bigradings of
`Homology/HatBigrading.lean`.

This file shows that the stabilization comparison
`GridDiagram.oneVariableSpecializationStabilizeXHomologyMap` preserves and reflects both bidegrees,
so its restricted-scalar `R`-linear equivalence is homogeneous of bidegree `(0, 0)` and restricts
to specified `R`-linear equivalences on every homogeneous homology piece
(`oneVariableSpecializationStabilizeXHomologyPieceEquiv`).

For a knot grid `G`, this gives bigraded stabilization invariance of simply blocked grid homology
`G-hat` (`GridDiagram.IsKnot.simplyBlockedStabilizeXHomologyPieceEquiv`). Unlike fully blocked
grid homology `GH~`, whose Poincaré series is multiplied by `W` under stabilization, both the
bigraded Poincaré series (`bigradedSimplyBlockedHomologyPoincareSeries_stabilizeX`) and the
Alexander-graded Euler characteristic (`gradedSimplyBlockedHomologyEulerChar_stabilizeX`) of
`G-hat` over a field of characteristic two are unchanged by `X`-stabilization.

## Main definitions

* `TauCeti.OddComponentGridDiagram.oneVariableSpecializationStabilizeXHomologyPieceEquiv`: the
  `R`-linear equivalence on bidegree-`g` homology pieces of the one-variable specialization.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedStabilizeXHomologyPieceEquiv`: the knot-grid
  specialization on bidegree-`g` pieces of `G-hat`.

## Main results

* `oneVariableSpecializationStabilizeXHomologyMap_mem_bigradedHatHomologyPiece_iff`:
  the stabilization comparison preserves and reflects homology bidegrees.
* `TauCeti.GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_stabilizeX`: over a field
  of characteristic two, `X`-stabilization preserves the bigraded Poincaré series of `G-hat`.
* `TauCeti.GridDiagram.IsKnot.gradedSimplyBlockedHomologyEulerChar_stabilizeX`: over a field of
  characteristic two, `X`-stabilization preserves the Alexander-graded Euler characteristic of
  `G-hat`.

## References

* Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2.
* Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.2
  (arXiv:math/0610559).
-/

public section

open CategoryTheory MvPolynomial

namespace TauCeti.OddComponentGridDiagram

open GridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (s i : Fin n)
  (R : Type*) [CommRing R] [CharP R 2]

local notation "j" => Fin.succAbove (Fin.castSucc s) i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R
local notation "BaseA" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* A)
local notation "BaseS" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)

/-- **The stabilization comparison on the one-variable specialization preserves the bigrading.**
Every homogeneous class of bidegree `g` in the specialization `V_{s.castSucc.succAbove i} = 0` of
`G.stabilizeX s` maps to a homogeneous class of bidegree `g` in the specialization `V_i = 0` of
`G`. -/
theorem oneVariableSpecializationStabilizeXHomologyMap_mem_bigradedHatHomologyPiece {g : ℤ × ℤ}
    {y : (BaseS).obj ((((G.stabilizeX s).1).simplyBlockedComplex R j).homology ())}
    (hy : y ∈ (G.stabilizeX s).bigradedHatHomologyPiece R j g) :
    G.1.oneVariableSpecializationStabilizeXHomologyMap s i R y ∈
      G.bigradedHatHomologyPiece R i g := by
  dsimp only [stabilizeX] at y hy ⊢
  obtain ⟨z, hz, rfl⟩ := (mem_bigradedHatHomologyPiece_iff _ R j).mp hy
  have heq : (G.1.oneVariableSpecializationStabilizeXHomologyMap s i R
      ((G.1.stabilizeX s.castSucc (G.1.X s).castSucc s).oneVariableSpecializationHomologyClass
        R j z) :
      (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) =
    G.1.oneVariableSpecializationHomologyClass R i
      (G.1.oneVariableSpecializationStabilizeXCyclesMap s i R z) :=
    G.1.oneVariableSpecializationStabilizeXHomologyMap_oneVariableSpecializationHomologyClass
      s i R z
  rw [heq]
  refine G.oneVariableSpecializationHomologyClass_mem_bigradedHatHomologyPiece R i ?_
  rw [simplyBlockedChainEquiv_oneVariableSpecializationStabilizeXCyclesMap]
  exact G.simplyBlockedStabilizeXMap_mem_bigradedChainHatPiece s i R hz

/-- As an `R`-linear equivalence, the stabilization comparison on the homology of the one-variable
specialization is homogeneous of bidegree `(0, 0)`. -/
theorem isHomogeneous_oneVariableSpecializationStabilizeXHomologyEquiv :
    LinearMap.IsHomogeneous
      (G.1.oneVariableSpecializationStabilizeXHomologyEquiv s i R).toLinearMap
      ((G.stabilizeX s).bigradedHatHomologyGrading R j).piece
      (G.bigradedHatHomologyGrading R i).piece 0 :=
  LinearMap.isHomogeneous_def.2 fun g y hy => by
    rw [bigradedHatHomologyGrading_piece] at hy
    rw [add_zero, bigradedHatHomologyGrading_piece, LinearEquiv.coe_coe,
      G.1.oneVariableSpecializationStabilizeXHomologyEquiv_apply s i R y]
    exact G.oneVariableSpecializationStabilizeXHomologyMap_mem_bigradedHatHomologyPiece s i R hy

/-- The stabilization comparison on the one-variable specialization reflects homology bidegrees as
well as preserving them. -/
@[simp]
theorem oneVariableSpecializationStabilizeXHomologyMap_mem_bigradedHatHomologyPiece_iff
    (g : ℤ × ℤ)
    (y : (BaseS).obj ((((G.stabilizeX s).1).simplyBlockedComplex R j).homology ())) :
    G.1.oneVariableSpecializationStabilizeXHomologyMap s i R y ∈
        G.bigradedHatHomologyPiece R i g ↔
      y ∈ (G.stabilizeX s).bigradedHatHomologyPiece R j g := by
  constructor
  · intro hy
    let e : (BaseS).obj ((((G.stabilizeX s).1).simplyBlockedComplex R j).homology ()) ≃ₗ[R]
        (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ()) :=
      G.1.oneVariableSpecializationStabilizeXHomologyEquiv s i R
    have he : LinearMap.IsHomogeneous e.toLinearMap
        ((G.stabilizeX s).bigradedHatHomologyGrading R j).piece
        (G.bigradedHatHomologyGrading R i).piece 0 :=
      G.isHomogeneous_oneVariableSpecializationStabilizeXHomologyEquiv s i R
    have he_apply : e y =
        (G.1.oneVariableSpecializationStabilizeXHomologyMap s i R y :
          (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) :=
      G.1.oneVariableSpecializationStabilizeXHomologyEquiv_apply s i R y
    have hz : e y ∈ (G.bigradedHatHomologyGrading R i).piece g := by
      rw [bigradedHatHomologyGrading_piece, he_apply]
      exact hy
    simpa only [add_zero, bigradedHatHomologyGrading_piece, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using he.linearEquiv_symm.map_mem hz
  · exact G.oneVariableSpecializationStabilizeXHomologyMap_mem_bigradedHatHomologyPiece s i R

/-- The stabilization comparison identifies each homogeneous piece of the homology of the
one-variable specialization with the piece of the same bidegree in the original grid. -/
noncomputable def oneVariableSpecializationStabilizeXHomologyPieceEquiv (g : ℤ × ℤ) :
    (G.stabilizeX s).bigradedHatHomologyPiece R j g ≃ₗ[R]
      G.bigradedHatHomologyPiece R i g :=
  (G.1.oneVariableSpecializationStabilizeXHomologyEquiv s i R).ofSubmodules _ _ (by
    dsimp only [stabilizeX]
    ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [LinearEquiv.coe_coe, GridDiagram.oneVariableSpecializationStabilizeXHomologyEquiv_apply]
      exact G.oneVariableSpecializationStabilizeXHomologyMap_mem_bigradedHatHomologyPiece s i R hx
    · intro hy
      let x := (G.1.oneVariableSpecializationStabilizeXHomologyEquiv s i R).symm y
      refine ⟨x, ?_, LinearEquiv.apply_symm_apply _ y⟩
      refine (G.oneVariableSpecializationStabilizeXHomologyMap_mem_bigradedHatHomologyPiece_iff
        s i R g x).mp ?_
      have hx : (G.1.oneVariableSpecializationStabilizeXHomologyMap s i R x :
          (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) = y :=
        (G.1.oneVariableSpecializationStabilizeXHomologyEquiv_apply s i R x).symm.trans
          (LinearEquiv.apply_symm_apply _ y)
      rwa [hx])

/-- On homogeneous classes, `oneVariableSpecializationStabilizeXHomologyPieceEquiv` is the
semilinear stabilization comparison. -/
@[simp]
theorem coe_oneVariableSpecializationStabilizeXHomologyPieceEquiv_apply (g : ℤ × ℤ)
    (y : (G.stabilizeX s).bigradedHatHomologyPiece R j g) :
    (G.oneVariableSpecializationStabilizeXHomologyPieceEquiv s i R g y :
        (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) =
      G.1.oneVariableSpecializationStabilizeXHomologyMap s i R y.1 :=
  G.1.oneVariableSpecializationStabilizeXHomologyEquiv_apply s i R y.1

/-- The inverse piece equivalence is the inverse of the total homology equivalence. -/
@[simp]
theorem coe_oneVariableSpecializationStabilizeXHomologyPieceEquiv_symm_apply (g : ℤ × ℤ)
    (y : G.bigradedHatHomologyPiece R i g) :
    ((G.oneVariableSpecializationStabilizeXHomologyPieceEquiv s i R g).symm y :
        (BaseS).obj ((((G.stabilizeX s).1).simplyBlockedComplex R j).homology ())) =
      (G.1.oneVariableSpecializationStabilizeXHomologyEquiv s i R).symm y :=
  (rfl)

/-- Stabilization preserves the `R`-rank of every homogeneous piece of the homology of the
one-variable specialization. -/
theorem finrank_bigradedHatHomologyPiece_stabilizeX (g : ℤ × ℤ) :
    Module.finrank R ((G.stabilizeX s).bigradedHatHomologyPiece R j g) =
      Module.finrank R (G.bigradedHatHomologyPiece R i g) :=
  (G.oneVariableSpecializationStabilizeXHomologyPieceEquiv s i R g).finrank_eq

end TauCeti.OddComponentGridDiagram

namespace TauCeti.GridDiagram.IsKnot

open OddComponentGridDiagram

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (s i : Fin n)

local notation "j" => Fin.succAbove (Fin.castSucc s) i
local notation "hG'" => Iff.mpr
  (GridDiagram.isKnot_stabilizeX G (Fin.castSucc s) (Fin.castSucc (GridDiagram.X G s)) s) hG

section CommRing

variable (R : Type*) [CommRing R] [CharP R 2]

local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R
local notation "BaseA" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* A)
local notation "BaseS" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)

/-- The stabilization comparison on `G-hat` preserves both O-Maslov and Alexander degrees. -/
theorem simplyBlockedStabilizeXHomologyMap_mem_bigradedHatHomologyPiece {g : ℤ × ℤ}
    {y : (BaseS).obj ((hG').simplyBlockedHomology R j)}
    (hy : y ∈ (hG').toOddComponentGridDiagram.bigradedHatHomologyPiece R j g) :
    hG.simplyBlockedStabilizeXHomologyMap s i R y ∈
      hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g := by
  rw [simplyBlockedStabilizeXHomologyMap_eq_oneVariableSpecializationStabilizeXHomologyMap]
  exact oneVariableSpecializationStabilizeXHomologyMap_mem_bigradedHatHomologyPiece
    hG.toOddComponentGridDiagram s i R hy

/-- The stabilization comparison on `G-hat` reflects homology bidegrees as well as preserving
them. -/
@[simp]
theorem simplyBlockedStabilizeXHomologyMap_mem_bigradedHatHomologyPiece_iff
    (g : ℤ × ℤ) (y : (BaseS).obj ((hG').simplyBlockedHomology R j)) :
    hG.simplyBlockedStabilizeXHomologyMap s i R y ∈
        hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g ↔
      y ∈ (hG').toOddComponentGridDiagram.bigradedHatHomologyPiece R j g := by
  rw [simplyBlockedStabilizeXHomologyMap_eq_oneVariableSpecializationStabilizeXHomologyMap]
  exact oneVariableSpecializationStabilizeXHomologyMap_mem_bigradedHatHomologyPiece_iff
    hG.toOddComponentGridDiagram s i R g y

/-- **Bigraded stabilization invariance of `G-hat`.** For a knot grid `G`, the stabilization
comparison identifies each homogeneous piece of `G-hat` of the stabilized grid with the piece of
the same bidegree in `G`. -/
noncomputable def simplyBlockedStabilizeXHomologyPieceEquiv (g : ℤ × ℤ) :
    (hG').toOddComponentGridDiagram.bigradedHatHomologyPiece R j g ≃ₗ[R]
      hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g :=
  oneVariableSpecializationStabilizeXHomologyPieceEquiv
    hG.toOddComponentGridDiagram s i R g

/-- The knot-facing homogeneous piece equivalence is the piece equivalence on the underlying
odd-component one-variable specialization. -/
theorem simplyBlockedStabilizeXHomologyPieceEquiv_eq (g : ℤ × ℤ) :
    hG.simplyBlockedStabilizeXHomologyPieceEquiv s i R g =
      hG.toOddComponentGridDiagram.oneVariableSpecializationStabilizeXHomologyPieceEquiv
        s i R g :=
  (rfl)

/-- On homogeneous classes, `simplyBlockedStabilizeXHomologyPieceEquiv` is the semilinear
stabilization comparison on `G-hat`. -/
@[simp]
theorem coe_simplyBlockedStabilizeXHomologyPieceEquiv_apply (g : ℤ × ℤ)
    (y : (hG').toOddComponentGridDiagram.bigradedHatHomologyPiece R j g) :
    (hG.simplyBlockedStabilizeXHomologyPieceEquiv s i R g y :
        (BaseA).obj (hG.simplyBlockedHomology R i)) =
      hG.simplyBlockedStabilizeXHomologyMap s i R y.1 := by
  rw [simplyBlockedStabilizeXHomologyPieceEquiv_eq,
    simplyBlockedStabilizeXHomologyMap_eq_oneVariableSpecializationStabilizeXHomologyMap]
  exact coe_oneVariableSpecializationStabilizeXHomologyPieceEquiv_apply
    hG.toOddComponentGridDiagram s i R g y

/-- The inverse piece equivalence on `G-hat` is the inverse of the total homology equivalence. -/
@[simp]
theorem coe_simplyBlockedStabilizeXHomologyPieceEquiv_symm_apply (g : ℤ × ℤ)
    (y : hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g) :
    ((hG.simplyBlockedStabilizeXHomologyPieceEquiv s i R g).symm y :
        (BaseS).obj ((hG').simplyBlockedHomology R j)) =
      (hG.simplyBlockedStabilizeXHomologyEquiv s i R).symm y := by
  rw [simplyBlockedStabilizeXHomologyPieceEquiv_eq,
    simplyBlockedStabilizeXHomologyEquiv_eq_oneVariableSpecializationStabilizeXHomologyEquiv]
  exact coe_oneVariableSpecializationStabilizeXHomologyPieceEquiv_symm_apply
    hG.toOddComponentGridDiagram s i R g y

/-- Stabilization preserves the `R`-rank of simply blocked knot-grid homology after restricting
scalars to the ground ring. -/
theorem finrank_restrictScalars_simplyBlockedHomology_stabilizeX :
    Module.finrank R ((BaseS).obj ((hG').simplyBlockedHomology R j)) =
      Module.finrank R ((BaseA).obj (hG.simplyBlockedHomology R i)) :=
  (hG.simplyBlockedStabilizeXHomologyEquiv s i R).finrank_eq

end CommRing

section Field

variable (R : Type*) [Field R] [CharP R 2]

/-- **Stabilization invariance of the Poincaré series of `G-hat`.** Over any field of
characteristic two, splitting the `X`-marking of column `s` and blocking the transported old
`O`-marking `s.castSucc.succAbove i` preserves the bigraded Poincaré series of simply blocked
knot-grid homology. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_stabilizeX :
    (hG').bigradedSimplyBlockedHomologyPoincareSeries R j =
      hG.bigradedSimplyBlockedHomologyPoincareSeries R i := by
  ext g
  rw [coeff_bigradedSimplyBlockedHomologyPoincareSeries,
    coeff_bigradedSimplyBlockedHomologyPoincareSeries]
  exact (hG.simplyBlockedStabilizeXHomologyPieceEquiv s i R g).finrank_eq

/-- **Stabilization invariance of the Alexander-graded Euler characteristic of `G-hat`.** Over any
field of characteristic two, `X`-stabilization preserves the Alexander-graded Euler characteristic
of simply blocked knot-grid homology. -/
theorem gradedSimplyBlockedHomologyEulerChar_stabilizeX :
    (hG').gradedSimplyBlockedHomologyEulerChar R j =
      hG.gradedSimplyBlockedHomologyEulerChar R i := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler,
    gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_stabilizeX s i R]

end Field

end TauCeti.GridDiagram.IsKnot

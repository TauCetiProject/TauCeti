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
columns of `G`, and let `G' = G.stabilizeX s` be the south-west corner `X`-stabilization
(`G.1.stabilizeX s.castSucc (G.1.X s).castSucc s` on the underlying grid) splitting the `X`-marking
of column `s`, with `j = s.castSucc.succAbove i` the column of `G'` carrying the old `O`-marking of
column `i`. Over any commutative ring `R` of characteristic two, the homologies of the one-variable
specializations at `V_j = 0` and `V_i = 0` carry the internal `(O-Maslov, Alexander)` bigradings of
`Homology/HatBigrading.lean`.

This file shows that the stabilization comparison
`GridDiagram.oneVariableSpecializationStabilizeXHomologyMap` preserves and reflects both bidegrees,
so its restricted-scalar `R`-linear equivalence is homogeneous of bidegree `(0, 0)` and restricts
to specified `R`-linear equivalences on every homogeneous homology piece
(`oneVariableSpecializationStabilizeXHomologyPieceEquiv`).

For a knot grid (`hG : G.IsKnot`), applying this equivalence to `hG.toOddComponentGridDiagram` gives
bigraded invariance of simply blocked grid homology `G-hat` under the south-west corner
`X`-stabilization `G.stabilizeX s.castSucc (G.X s).castSucc s`. Unlike fully blocked grid homology
`GH~`, whose Poincaré series is multiplied by `W` under this stabilization, both the bigraded
Poincaré series (`bigradedSimplyBlockedHomologyPoincareSeries_stabilizeX`) and the Alexander-graded
Euler characteristic (`gradedSimplyBlockedHomologyEulerChar_stabilizeX`) of `G-hat` over a field of
characteristic two are unchanged by `G.stabilizeX s.castSucc (G.X s).castSucc s`. Only this
south-west corner `X`-stabilization is treated here.

## Main definitions

* `TauCeti.OddComponentGridDiagram.oneVariableSpecializationStabilizeXHomologyPieceEquiv`: the
  `R`-linear equivalence on bidegree-`g` homology pieces of the one-variable specialization.

## Main results

* `oneVariableSpecializationStabilizeXHomologyMap_mem_bigradedHatHomologyPiece_iff`:
  the stabilization comparison preserves and reflects homology bidegrees.
* `TauCeti.GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_stabilizeX`: over a field
  of characteristic two, the south-west corner `X`-stabilization
  `G.stabilizeX s.castSucc (G.X s).castSucc s` preserves the bigraded Poincaré series of `G-hat`.
* `TauCeti.GridDiagram.IsKnot.gradedSimplyBlockedHomologyEulerChar_stabilizeX`: over a field of
  characteristic two, the south-west corner `X`-stabilization
  `G.stabilizeX s.castSucc (G.X s).castSucc s` preserves the Alexander-graded Euler characteristic
  of `G-hat`.

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
  -- Unfold semireducible `OddComponentGridDiagram.stabilizeX` so `(G.stabilizeX s).1` reduces by
  -- projection at `implicit` transparency (`dsimp only [val_stabilizeX]` makes no progress here).
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
    -- Unfold semireducible `OddComponentGridDiagram.stabilizeX` so the ambient module carrier
    -- `(G.stabilizeX s).1` matches the domain of `oneVariableSpecializationStabilizeXHomologyEquiv`
    -- at `implicit` transparency.
    dsimp only [stabilizeX]
    ext y
    rw [Submodule.mem_map_equiv]
    have h := G.oneVariableSpecializationStabilizeXHomologyMap_mem_bigradedHatHomologyPiece_iff
      s i R g ((G.1.oneVariableSpecializationStabilizeXHomologyEquiv s i R).symm y)
    rw [← GridDiagram.oneVariableSpecializationStabilizeXHomologyEquiv_apply,
      LinearEquiv.apply_symm_apply] at h
    exact h.symm)

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

/-- The south-west corner `X`-stabilization `G.stabilizeX s` preserves the `R`-rank of every
homogeneous piece of the homology of the one-variable specialization. -/
theorem finrank_bigradedHatHomologyPiece_stabilizeX (g : ℤ × ℤ) :
    Module.finrank R ((G.stabilizeX s).bigradedHatHomologyPiece R j g) =
      Module.finrank R (G.bigradedHatHomologyPiece R i g) :=
  (G.oneVariableSpecializationStabilizeXHomologyPieceEquiv s i R g).finrank_eq

end TauCeti.OddComponentGridDiagram

namespace TauCeti.GridDiagram.IsKnot

open OddComponentGridDiagram

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (s i : Fin n)
  (R : Type*) [Field R] [CharP R 2]

local notation "j" => Fin.succAbove (Fin.castSucc s) i
local notation "hG'" => Iff.mpr
  (GridDiagram.isKnot_stabilizeX G (Fin.castSucc s) (Fin.castSucc (GridDiagram.X G s)) s) hG

/-- **South-west `X`-stabilization invariance of the Poincaré series of `G-hat`.** Over any field of
characteristic two, the south-west corner `X`-stabilization
`G.stabilizeX s.castSucc (G.X s).castSucc s` (blocking the transported old `O`-marking
`s.castSucc.succAbove i`) preserves the bigraded Poincaré series of simply blocked knot-grid
homology. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_stabilizeX :
    (hG').bigradedSimplyBlockedHomologyPoincareSeries R j =
      hG.bigradedSimplyBlockedHomologyPoincareSeries R i := by
  have hstab : (hG').toOddComponentGridDiagram = hG.toOddComponentGridDiagram.stabilizeX s :=
    Subtype.ext (hG.toOddComponentGridDiagram.val_stabilizeX s).symm
  ext g
  rw [coeff_bigradedSimplyBlockedHomologyPoincareSeries,
    coeff_bigradedSimplyBlockedHomologyPoincareSeries, hstab]
  exact hG.toOddComponentGridDiagram.finrank_bigradedHatHomologyPiece_stabilizeX s i R g

/-- **South-west `X`-stabilization invariance of the Alexander-graded Euler characteristic of
`G-hat`.** Over any field of characteristic two, the south-west corner `X`-stabilization
`G.stabilizeX s.castSucc (G.X s).castSucc s` (blocking the transported old `O`-marking
`s.castSucc.succAbove i`) preserves the Alexander-graded Euler characteristic of simply blocked
knot-grid homology. -/
theorem gradedSimplyBlockedHomologyEulerChar_stabilizeX :
    (hG').gradedSimplyBlockedHomologyEulerChar R j =
      hG.gradedSimplyBlockedHomologyEulerChar R i := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler,
    gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_stabilizeX s i R]

end TauCeti.GridDiagram.IsKnot

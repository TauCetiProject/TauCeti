/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.HalfTurn
public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.Grading
public import TauCeti.KnotTheory.Grid.Stabilization.SimplyBlocked.Bigraded

/-!
# North-east stabilization of one-variable-specialization homology

The north-east corner `X`-stabilization inserts a column after the split column `s` and a row
after its `X`-marking. The old `O`-marking of column `i` then lies in column
`s.succ.succAbove i`. Blocking that marking gives one-variable-specialization homology in the
same absolute `(O-Maslov, Alexander)` bidegrees as the original diagram whenever its component
count is odd. For knots this specialization is simply blocked homology.

This file specifies a coefficient-linear equivalence on total homology and every homogeneous
piece, with cycle-class and subtype-projection equations. A half-turn
identifies the north-east stabilized source with the south-west stabilization of the rotated
grid, including the transported blocked marking. Thus the equivalence retains the grading
normalization and the choice of blocked marking. For knots over a field of characteristic two,
the bigraded Poincaré series and Alexander-graded Euler characteristic are unchanged.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2.
-/

public section

open CategoryTheory

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s i : Fin n)
  (R : Type*) [CommRing R] [CharP R 2]

local notation "G'" => G.stabilizeX (Fin.succ s) (Fin.succ (G.X s)) s
local notation "H" => G.rotate.stabilizeX (Fin.castSucc s.rev)
  (Fin.castSucc (G.rotate.X s.rev)) s.rev
local notation "j" => Fin.succAbove (Fin.succ s) i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R
local notation "BaseA" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* A)
local notation "BaseS" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)

private theorem rotate_stabilizeX_succ_index :
    ((G').rotate, (j).rev) =
      (H, s.rev.castSucc.succAbove i.rev) := by
  apply Prod.ext
  · exact G.rotate_stabilizeX_succ s
  · simp only [Fin.rev_succAbove, Fin.rev_succ]

private noncomputable def stabilizeXSuccSourceEquiv :
    (ModuleCat.restrictScalars (MvPolynomial.C : R →+*
      MvPolynomial {c : Fin (n + 1) // c ≠ (j).rev} R)).obj
        (((G').rotate.simplyBlockedComplex R (j).rev).homology ()) ≃ₗ[R]
      (ModuleCat.restrictScalars (MvPolynomial.C : R →+*
        MvPolynomial {c : Fin (n + 1) // c ≠ s.rev.castSucc.succAbove i.rev} R)).obj
        (((H).simplyBlockedComplex R
          (s.rev.castSucc.succAbove i.rev)).homology ()) :=
  LinearEquiv.cast (R := R) (M := fun p : GridDiagram (n + 1) × Fin (n + 1) =>
    (ModuleCat.restrictScalars (MvPolynomial.C : R →+*
      MvPolynomial {c : Fin (n + 1) // c ≠ p.2} R)).obj
        ((p.1.simplyBlockedComplex R p.2).homology ()))
    (i := ((G').rotate, (j).rev))
    («j» := (H, s.rev.castSucc.succAbove i.rev))
    (G.rotate_stabilizeX_succ_index s i)

/-- The north-east comparison on cycles of the one-variable specialization. The middle
identification records the rotated diagram and the transported blocked marking. -/
noncomputable def oneVariableSpecializationStabilizeXSuccCyclesMap
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom :=
  (G.oneVariableSpecializationRotateCyclesEquiv R i).symm
    (G.rotate.oneVariableSpecializationStabilizeXCyclesMap s.rev i.rev R
      (Eq.mp (congrArg (fun p : GridDiagram (n + 1) × Fin (n + 1) =>
        ↥(LinearMap.ker ((p.1.simplyBlockedComplex R p.2).d () ()).hom))
          (G.rotate_stabilizeX_succ_index s i))
        ((G').oneVariableSpecializationRotateCyclesEquiv R j z)))

/-- The cycle comparison is the conjugate of the south-west cycle map by half-turns.
The middle transport identifies the rotated stabilized diagram and its blocked marking. -/
theorem oneVariableSpecializationStabilizeXSuccCyclesMap_def
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    G.oneVariableSpecializationStabilizeXSuccCyclesMap s i R z =
      (G.oneVariableSpecializationRotateCyclesEquiv R i).symm
        (G.rotate.oneVariableSpecializationStabilizeXCyclesMap s.rev i.rev R
          (Eq.mp (congrArg (fun p : GridDiagram (n + 1) × Fin (n + 1) =>
            ↥(LinearMap.ker ((p.1.simplyBlockedComplex R p.2).d () ()).hom))
              (show ((G').rotate, (j).rev) =
                  (H, s.rev.castSucc.succAbove i.rev) from by
                apply Prod.ext
                · exact G.rotate_stabilizeX_succ s
                · simp only [Fin.rev_succAbove, Fin.rev_succ]))
            ((G').oneVariableSpecializationRotateCyclesEquiv R j z))) := by
  unfold oneVariableSpecializationStabilizeXSuccCyclesMap
  rfl

private theorem stabilizeXSuccSourceEquiv_homologyClass
    (z : LinearMap.ker
      (((G').rotate.simplyBlockedComplex R (j).rev).d () ()).hom) :
    G.stabilizeXSuccSourceEquiv s i R
        ((G').rotate.oneVariableSpecializationHomologyClass R (j).rev z) =
      (H).oneVariableSpecializationHomologyClass R
        (s.rev.castSucc.succAbove i.rev)
        (Eq.mp (congrArg (fun p : GridDiagram (n + 1) × Fin (n + 1) =>
          ↥(LinearMap.ker ((p.1.simplyBlockedComplex R p.2).d () ()).hom))
            (G.rotate_stabilizeX_succ_index s i)) z) := by
  have aux (p q : GridDiagram (n + 1) × Fin (n + 1)) (h : p = q)
      (z : LinearMap.ker ((p.1.simplyBlockedComplex R p.2).d () ()).hom) :
      LinearEquiv.cast (R := R) (M := fun p : GridDiagram (n + 1) × Fin (n + 1) =>
        (ModuleCat.restrictScalars (MvPolynomial.C : R →+*
          MvPolynomial {c : Fin (n + 1) // c ≠ p.2} R)).obj
            ((p.1.simplyBlockedComplex R p.2).homology ())) (i := p) («j» := q) h
          (p.1.oneVariableSpecializationHomologyClass R p.2 z) =
        q.1.oneVariableSpecializationHomologyClass R q.2
          (Eq.mp (congrArg (fun p : GridDiagram (n + 1) × Fin (n + 1) =>
            ↥(LinearMap.ker ((p.1.simplyBlockedComplex R p.2).d () ()).hom)) h) z) := by
    subst q
    rfl
  exact aux _ _ (G.rotate_stabilizeX_succ_index s i) z

/-- The north-east stabilization comparison on total one-variable-specialization homology,
linear over the ground ring. It conjugates the south-west comparison by half-turns. -/
noncomputable def oneVariableSpecializationStabilizeXSuccHomologyEquiv :
    (BaseS).obj (((G').simplyBlockedComplex R j).homology ()) ≃ₗ[R]
      (BaseA).obj ((G.simplyBlockedComplex R i).homology ()) :=
  (((G').oneVariableSpecializationRotateHomologyLinearEquiv R j).trans
    (G.stabilizeXSuccSourceEquiv s i R)).trans
      ((G.rotate.oneVariableSpecializationStabilizeXHomologyEquiv s.rev i.rev R).trans
        (G.oneVariableSpecializationRotateHomologyLinearEquiv R i).symm)

/-- The total north-east comparison sends a cycle class to the class of its cycle image. -/
theorem oneVariableSpecializationStabilizeXSuccHomologyEquiv_oneVariableSpecializationHomologyClass
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    (G.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R
        ((G').oneVariableSpecializationHomologyClass R j z :
          (BaseS).obj (((G').simplyBlockedComplex R j).homology ())) :
            (G.simplyBlockedComplex R i).homology ()) =
      G.oneVariableSpecializationHomologyClass R i
        (G.oneVariableSpecializationStabilizeXSuccCyclesMap s i R z) := by
  rw [oneVariableSpecializationStabilizeXSuccHomologyEquiv]
  -- Expand the composition on its restricted-scalar carriers before using the public equations.
  change (G.oneVariableSpecializationRotateHomologyLinearEquiv R i).symm
    (G.rotate.oneVariableSpecializationStabilizeXHomologyEquiv s.rev i.rev R
      (G.stabilizeXSuccSourceEquiv s i R
        ((G').oneVariableSpecializationRotateHomologyLinearEquiv R j
          ((G').oneVariableSpecializationHomologyClass R j z)))) = _
  -- The class and its coefficient-linear presentation share their carrier via restrictScalars.
  erw [oneVariableSpecializationRotateHomologyLinearEquiv_symm_apply,
    oneVariableSpecializationStabilizeXHomologyEquiv_apply,
    oneVariableSpecializationRotateHomologyLinearEquiv_apply,
    oneVariableSpecializationRotateHomologyEquiv_oneVariableSpecializationHomologyClass,
    stabilizeXSuccSourceEquiv_homologyClass,
    oneVariableSpecializationStabilizeXHomologyMap_oneVariableSpecializationHomologyClass,
    oneVariableSpecializationRotateHomologyEquiv_symm_oneVariableSpecializationHomologyClass,
    oneVariableSpecializationStabilizeXSuccCyclesMap_def]

/-- The inverse total comparison recovers the class of a cycle from its north-east image. -/
theorem
    oneVariableSpecializationStabilizeXSuccHomologyEquiv_symm_oneVariableSpecializationHomologyClass
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    ((G.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).symm
        (G.oneVariableSpecializationHomologyClass R i
          (G.oneVariableSpecializationStabilizeXSuccCyclesMap s i R z) :
            (BaseA).obj ((G.simplyBlockedComplex R i).homology ())) :
              ((G').simplyBlockedComplex R j).homology ()) =
      (G').oneVariableSpecializationHomologyClass R j z := by
  rw [←
    oneVariableSpecializationStabilizeXSuccHomologyEquiv_oneVariableSpecializationHomologyClass
      G s i R z]
  exact (G.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).symm_apply_apply _

end TauCeti.GridDiagram

namespace TauCeti.OddComponentGridDiagram

open GridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (s i : Fin n)
  (R : Type*) [CommRing R] [CharP R 2]

local notation "j" => Fin.succAbove (Fin.succ s) i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R
local notation "BaseA" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* A)
local notation "BaseS" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)

private theorem stabilizeXSuccSourceEquiv_mem_iff (g : ℤ × ℤ)
    (y : (ModuleCat.restrictScalars (MvPolynomial.C : R →+*
      MvPolynomial {c : Fin (n + 1) // c ≠ (j).rev} R)).obj
        (((G.stabilizeXSucc s).rotate.1.simplyBlockedComplex R (j).rev).homology ())) :
    G.1.stabilizeXSuccSourceEquiv s i R y ∈
        (G.rotate.stabilizeX s.rev).bigradedHatHomologyPiece R
          (s.rev.castSucc.succAbove i.rev) g ↔
      y ∈ (G.stabilizeXSucc s).rotate.bigradedHatHomologyPiece R (j).rev g := by
  have aux (p q : OddComponentGridDiagram (n + 1) × Fin (n + 1)) (h : p = q)
      (y : (ModuleCat.restrictScalars (MvPolynomial.C : R →+*
        MvPolynomial {c : Fin (n + 1) // c ≠ p.2} R)).obj
          ((p.1.1.simplyBlockedComplex R p.2).homology ())) :
      LinearEquiv.cast (R := R) (M := fun p : GridDiagram (n + 1) × Fin (n + 1) =>
        (ModuleCat.restrictScalars (MvPolynomial.C : R →+*
          MvPolynomial {c : Fin (n + 1) // c ≠ p.2} R)).obj
            ((p.1.simplyBlockedComplex R p.2).homology ()))
        (congrArg (fun p : OddComponentGridDiagram (n + 1) × Fin (n + 1) => (p.1.1, p.2)) h) y ∈
          q.1.bigradedHatHomologyPiece R q.2 g ↔
        y ∈ p.1.bigradedHatHomologyPiece R p.2 g := by
    subst q
    rfl
  dsimp only [stabilizeXSucc, stabilizeX] at y ⊢
  exact aux
    ((G.stabilizeXSucc s).rotate, (j).rev)
    (G.rotate.stabilizeX s.rev, s.rev.castSucc.succAbove i.rev) (by
      apply Prod.ext
      · exact G.rotate_stabilizeXSucc s
      · simp only [Fin.rev_succAbove, Fin.rev_succ]) y

/-- The north-east comparison preserves and reflects the absolute homology bidegree. -/
@[simp]
theorem oneVariableSpecializationStabilizeXSuccHomologyEquiv_mem_bigradedHatHomologyPiece_iff
    (g : ℤ × ℤ)
    (y : (BaseS).obj (((G.stabilizeXSucc s).1.simplyBlockedComplex R j).homology ())) :
    G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R y ∈
        G.bigradedHatHomologyPiece R i g ↔
      y ∈ (G.stabilizeXSucc s).bigradedHatHomologyPiece R j g := by
  rw [GridDiagram.oneVariableSpecializationStabilizeXSuccHomologyEquiv]
  -- Keep the selected restricted-scalar carriers while expanding the composite equivalence.
  change (G.1.oneVariableSpecializationRotateHomologyLinearEquiv R i).symm
    (G.rotate.1.oneVariableSpecializationStabilizeXHomologyEquiv s.rev i.rev R
      (G.1.stabilizeXSuccSourceEquiv s i R
        ((G.stabilizeXSucc s).1.oneVariableSpecializationRotateHomologyLinearEquiv R j y))) ∈
      G.bigradedHatHomologyPiece R i g ↔ _
  -- Membership uses the same carrier before and after restricting coefficient scalars.
  erw [GridDiagram.oneVariableSpecializationRotateHomologyLinearEquiv_symm_apply,
    G.oneVariableSpecializationRotateHomologyEquiv_symm_mem_bigradedHatHomologyPiece_iff]
  erw [GridDiagram.oneVariableSpecializationStabilizeXHomologyEquiv_apply,
    G.rotate.oneVariableSpecializationStabilizeXHomologyMap_mem_bigradedHatHomologyPiece_iff,
    G.stabilizeXSuccSourceEquiv_mem_iff,
    GridDiagram.oneVariableSpecializationRotateHomologyLinearEquiv_apply]
  exact oneVariableSpecializationRotateHomologyEquiv_mem_bigradedHatHomologyPiece_iff
    (G.stabilizeXSucc s) R j g y

/-- The inverse north-east comparison preserves and reflects the absolute homology bidegree. -/
@[simp]
theorem oneVariableSpecializationStabilizeXSuccHomologyEquiv_symm_mem_bigradedHatHomologyPiece_iff
    (g : ℤ × ℤ) (y : (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) :
    (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).symm y ∈
        (G.stabilizeXSucc s).bigradedHatHomologyPiece R j g ↔
      y ∈ G.bigradedHatHomologyPiece R i g := by
  simpa only [LinearEquiv.apply_symm_apply] using
    (G.oneVariableSpecializationStabilizeXSuccHomologyEquiv_mem_bigradedHatHomologyPiece_iff s i R g
      ((G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).symm y)).symm

/-- The north-east total homology comparison is homogeneous of bidegree zero. -/
theorem isHomogeneous_oneVariableSpecializationStabilizeXSuccHomologyEquiv :
    LinearMap.IsHomogeneous
      (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).toLinearMap
      ((G.stabilizeXSucc s).bigradedHatHomologyGrading R j).piece
      (G.bigradedHatHomologyGrading R i).piece 0 :=
  LinearMap.isHomogeneous_def.2 fun g y hy => by
    rw [bigradedHatHomologyGrading_piece] at hy
    rw [add_zero, bigradedHatHomologyGrading_piece, LinearEquiv.coe_coe]
    exact (G.oneVariableSpecializationStabilizeXSuccHomologyEquiv_mem_bigradedHatHomologyPiece_iff
      s i R g y).2 hy

/-- North-east `X`-stabilization identifies each homogeneous piece, blocking the transported old
`O`-marking and preserving absolute `O`-Maslov and Alexander bidegrees. -/
noncomputable def simplyBlockedHomologyStabilizeXSuccPieceEquiv (g : ℤ × ℤ) :
    (G.stabilizeXSucc s).bigradedHatHomologyPiece R j g ≃ₗ[R]
      G.bigradedHatHomologyPiece R i g :=
  (G.stabilizeXSucc s).oneVariableSpecializationHomologyPieceEquivOfHomogeneous R j G i
    (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R)
    (G.isHomogeneous_oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R) g

/-- The piece comparison is the restriction of the total homology comparison. -/
@[simp↓]
theorem coe_simplyBlockedHomologyStabilizeXSuccPieceEquiv_apply (g : ℤ × ℤ)
    (y : (G.stabilizeXSucc s).bigradedHatHomologyPiece R j g) :
    (G.simplyBlockedHomologyStabilizeXSuccPieceEquiv s i R g y :
        (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) =
      G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R y := by
  exact (G.stabilizeXSucc s).coe_oneVariableSpecializationHomologyPieceEquivOfHomogeneous_apply
    R j G i (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R)
    (G.isHomogeneous_oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R) g y

/-- The inverse piece comparison is the restriction of the inverse total comparison. -/
@[simp↓]
theorem coe_simplyBlockedHomologyStabilizeXSuccPieceEquiv_symm_apply (g : ℤ × ℤ)
    (y : G.bigradedHatHomologyPiece R i g) :
    ((G.simplyBlockedHomologyStabilizeXSuccPieceEquiv s i R g).symm y :
        (BaseS).obj (((G.stabilizeXSucc s).1.simplyBlockedComplex R j).homology ())) =
      (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).symm y := by
  exact
    (G.stabilizeXSucc s).coe_oneVariableSpecializationHomologyPieceEquivOfHomogeneous_symm_apply
      R j G i (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R)
      (G.isHomogeneous_oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R) g y

/-- North-east `X`-stabilization preserves the coefficient-ring rank in every bidegree. -/
theorem finrank_bigradedHatHomologyPiece_stabilizeXSucc (g : ℤ × ℤ) :
    Module.finrank R ((G.stabilizeXSucc s).bigradedHatHomologyPiece R j g) =
      Module.finrank R (G.bigradedHatHomologyPiece R i g) :=
  (G.simplyBlockedHomologyStabilizeXSuccPieceEquiv s i R g).finrank_eq

end TauCeti.OddComponentGridDiagram

namespace TauCeti.GridDiagram.IsKnot

open OddComponentGridDiagram

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (s i : Fin n)
  (K : Type*) [Field K] [CharP K 2]

local notation "j" => Fin.succAbove (Fin.succ s) i
local notation "hG'" => Iff.mpr
  (GridDiagram.isKnot_stabilizeX G (Fin.succ s) (Fin.succ (GridDiagram.X G s)) s) hG

/-- North-east corner `X`-stabilization preserves the bigraded Poincaré series of simply
blocked knot-grid homology, blocking the transported old `O`-marking. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_stabilizeX_succ :
    (hG').bigradedSimplyBlockedHomologyPoincareSeries K j =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K i := by
  have hstab : (hG').toOddComponentGridDiagram = hG.toOddComponentGridDiagram.stabilizeXSucc s :=
    Subtype.ext rfl
  ext g
  rw [coeff_bigradedSimplyBlockedHomologyPoincareSeries,
    coeff_bigradedSimplyBlockedHomologyPoincareSeries, hstab]
  exact hG.toOddComponentGridDiagram.finrank_bigradedHatHomologyPiece_stabilizeXSucc s i K g

/-- North-east corner `X`-stabilization preserves the Alexander-graded Euler characteristic of
simply blocked knot-grid homology, blocking the transported old `O`-marking. -/
theorem gradedSimplyBlockedHomologyEulerChar_stabilizeX_succ :
    (hG').gradedSimplyBlockedHomologyEulerChar K j =
      hG.gradedSimplyBlockedHomologyEulerChar K i := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler,
    gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_stabilizeX_succ s i K]

end TauCeti.GridDiagram.IsKnot

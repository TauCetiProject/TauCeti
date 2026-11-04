/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Carrier
public import TauCeti.Algebra.Lie.Sl2.Integration
import TauCeti.LinearAlgebra.Matrix.Step
import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Long rank-one maps on the short-root F4 module

The two long simple roots of the twenty-six-dimensional F₄ module have square-zero raising and
lowering operators. Their products are the projections onto weights of coroot coordinate `1`
and `-1`. Integrating these matrix units gives faithful SL₂ maps over every commutative ring,
including nonreduced rings and characteristic two. Upper and lower transvections have the
prescribed root parameters, and the diagonal torus has the prescribed simple-coroot values.

The nodes are indexed by `Fin 2`, embedded in the Bourbaki `Fin 4` by `Fin.castAdd 2`; thus they
are exactly the long nodes, not a renumbering of the whole diagram. This file constructs matrix
maps only. Their restriction to the prime-field carrier is in `PrimeField.RankOne.Long`.

The construction uses `TauCeti.Sl2.squareZeroSL2Hom` and the existing integral short-root matrices.
The root/coroot comparison follows the rank-one interface in `TauCeti.E7Minuscule`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, Chapter 6.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.
-/

public section

open scoped Matrix MatrixGroups

namespace TauCeti.F4ShortRoot

open TauCeti.DynkinType

private theorem long_raising_lowering (i : Fin 2) :
    raisingMatrix (i.castAdd 2) * loweringMatrix (i.castAdd 2) =
      Matrix.diagonal (fun b => if f4ShortRootWeight b (i.castAdd 2) = 1 then 1 else 0) := by
  ext a b
  rw [((Matrix.isStep_of_apply (raisingMatrix_apply (i.castAdd 2))).mul
    (Matrix.isStep_of_apply (loweringMatrix_apply (i.castAdd 2)))).apply,
    Matrix.diagonal_apply]
  revert i a b
  decide +kernel

private theorem long_lowering_raising (i : Fin 2) :
    loweringMatrix (i.castAdd 2) * raisingMatrix (i.castAdd 2) =
      Matrix.diagonal (fun b => if f4ShortRootWeight b (i.castAdd 2) = -1 then 1 else 0) := by
  ext a b
  rw [((Matrix.isStep_of_apply (loweringMatrix_apply (i.castAdd 2))).mul
    (Matrix.isStep_of_apply (raisingMatrix_apply (i.castAdd 2)))).apply,
    Matrix.diagonal_apply]
  revert i a b
  decide +kernel

private theorem long_raising_lowering_raising (i : Fin 2) :
    raisingMatrix (i.castAdd 2) * loweringMatrix (i.castAdd 2) * raisingMatrix (i.castAdd 2) =
      raisingMatrix (i.castAdd 2) := by
  ext a b
  rw [(((Matrix.isStep_of_apply (raisingMatrix_apply (i.castAdd 2))).mul
    (Matrix.isStep_of_apply (loweringMatrix_apply (i.castAdd 2)))).mul
    (Matrix.isStep_of_apply (raisingMatrix_apply (i.castAdd 2)))).apply, raisingMatrix_apply]
  revert i a b
  decide +kernel

private theorem long_lowering_raising_lowering (i : Fin 2) :
    loweringMatrix (i.castAdd 2) * raisingMatrix (i.castAdd 2) * loweringMatrix (i.castAdd 2) =
      loweringMatrix (i.castAdd 2) := by
  ext a b
  rw [(((Matrix.isStep_of_apply (loweringMatrix_apply (i.castAdd 2))).mul
    (Matrix.isStep_of_apply (raisingMatrix_apply (i.castAdd 2)))).mul
    (Matrix.isStep_of_apply (loweringMatrix_apply (i.castAdd 2)))).apply, loweringMatrix_apply]
  revert i a b
  decide +kernel

-- Standard blocks: coordinates (3,4) at node 0 and (2,3) at node 1.
private def longBlock (i : Fin 2) (a : Fin 2) : Fin 26 :=
  if i = 0 then (if a = 0 then 3 else 4) else (if a = 0 then 2 else 3)

private theorem longBlock_data (i : Fin 2) :
    Function.Injective (longBlock i) ∧
    (∀ a b, raisingMatrix (i.castAdd 2) (longBlock i a) (longBlock i b) =
      if a = 0 ∧ b = 1 then 1 else 0) ∧
    (∀ a b, loweringMatrix (i.castAdd 2) (longBlock i a) (longBlock i b) =
      if a = 1 ∧ b = 0 then 1 else 0) ∧
    (∀ a, f4ShortRootWeight (longBlock i a) (i.castAdd 2) = if a = 0 then 1 else -1) := by
  simp only [raisingMatrix_apply, loweringMatrix_apply]
  revert i
  decide +kernel

variable (R : Type*) [CommRing R] (i : Fin 2)

/-- The faithful SL₂ action at a long simple node of the short-root F₄ module. It acts by the
standard representation on each two-element weight string and fixes the remaining summand. -/
noncomputable def longRankOneGL : SL(2, R) →* GL (Fin 26) R :=
  Sl2.squareZeroSL2Hom
    ((raisingMatrix (i.castAdd 2)).map (Int.cast : ℤ → R))
    ((loweringMatrix (i.castAdd 2)).map (Int.cast : ℤ → R))
    (by rw [← Matrix.map_mul_intCast, raisingMatrix_mul_self_of_lt_two _ i.isLt]; simp)
    (by rw [← Matrix.map_mul_intCast, loweringMatrix_mul_self_of_lt_two _ i.isLt]; simp)
    (by rw [← Matrix.map_mul_intCast, ← Matrix.map_mul_intCast,
          long_raising_lowering_raising])
    (by rw [← Matrix.map_mul_intCast, ← Matrix.map_mul_intCast,
          long_lowering_raising_lowering])

/-- Entrywise formula for the long-node action, with its two endpoint projections explicit. -/
theorem coe_longRankOneGL (g : SL(2, R)) :
    (longRankOneGL R i g : Matrix (Fin 26) (Fin 26) R) =
      1 + (g 0 0 - 1) • Matrix.diagonal
          (fun b => if f4ShortRootWeight b (i.castAdd 2) = 1 then 1 else 0) +
        g 0 1 • (raisingMatrix (i.castAdd 2)).map (Int.cast : ℤ → R) +
        g 1 0 • (loweringMatrix (i.castAdd 2)).map (Int.cast : ℤ → R) +
        (g 1 1 - 1) • Matrix.diagonal
          (fun b => if f4ShortRootWeight b (i.castAdd 2) = -1 then 1 else 0) := by
  rw [longRankOneGL, Sl2.coe_squareZeroSL2Hom, ← Matrix.map_mul_intCast,
    ← Matrix.map_mul_intCast, long_raising_lowering, long_lowering_raising]
  simp only [Matrix.diagonal_map (Int.cast_zero (R := R)), apply_ite,
    Int.cast_one, Int.cast_zero]

/-- The long-node action is faithful over every commutative ring. -/
theorem longRankOneGL_injective : Function.Injective (longRankOneGL R i) := by
  intro g h heq
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  have he := congrArg
    (fun k : GL (Fin 26) R => (k : Matrix _ _ R) (longBlock i a) (longBlock i b)) heq
  rcases longBlock_data i with ⟨hinj, hraise, hlower, hweight⟩
  simp only [coe_longRankOneGL, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
    Matrix.one_apply, Matrix.map_apply, hinj.eq_iff, hraise, hlower, hweight] at he
  fin_cases a <;> fin_cases b <;> simpa using he

/-- The upper transvection maps to the numbered positive-root point with unchanged parameter. -/
@[simp]
theorem longRankOneGL_upper_transvection (t : R) :
    longRankOneGL R i (Matrix.SpecialLinearGroup.transvection
      (by decide : (0 : Fin 2) ≠ 1) t) =
        (rootSubgroupPoints (.inl (i.castAdd 2)) R (Multiplicative.ofAdd t) : GL (Fin 26) R) := by
  apply Units.ext
  rw [longRankOneGL, Sl2.coe_squareZeroSL2Hom_upper,
    coe_rootSubgroupPoints_inl_of_lt_two _ i.isLt, toAdd_ofAdd]

/-- The lower transvection maps to the numbered negative-root point with unchanged parameter. -/
@[simp]
theorem longRankOneGL_lower_transvection (t : R) :
    longRankOneGL R i (Matrix.SpecialLinearGroup.transvection
      (by decide : (1 : Fin 2) ≠ 0) t) =
        (rootSubgroupPoints (.inr (i.castAdd 2)) R (Multiplicative.ofAdd t) : GL (Fin 26) R) := by
  apply Units.ext
  rw [longRankOneGL, Sl2.coe_squareZeroSL2Hom_lower,
    coe_rootSubgroupPoints_inr_of_lt_two _ i.isLt, toAdd_ofAdd]

/-- The diagonal `diag(u,u⁻¹)` maps to the weight-torus value of the numbered simple coroot. -/
@[simp]
theorem longRankOneGL_diag2nUnit (u : Rˣ) :
    longRankOneGL R i (Matrix.SpecialLinearGroup.diag2nUnit
      (by decide : (0 : Fin 2) ≠ 1) u) =
        (weightTorusPoints R (Pi.mulSingle (i.castAdd 2) u) : GL (Fin 26) R) := by
  apply Units.ext
  rw [coe_longRankOneGL, Matrix.SpecialLinearGroup.diag2nUnit_coe,
    coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Matrix.map_apply, smul_eq_mul, torusCharacter_mulSingle]
  have hw : f4ShortRootWeight b (i.castAdd 2) = -1 ∨
      f4ShortRootWeight b (i.castAdd 2) = 0 ∨ f4ShortRootWeight b (i.castAdd 2) = 1 := by
    revert i b
    decide +kernel
  by_cases hab : a = b
  · subst a
    rcases hw with hw | hw | hw <;> simp [hw]
  · simp [hab]

end TauCeti.F4ShortRoot

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic

/-!
# Rank-one maps for the short-root G₂ carrier

The seven-dimensional short-root module restricts at the short simple node to two standard
SL₂ modules and one three-dimensional divided-square module. At the long simple node it
restricts to two standard modules and three trivial modules. These decompositions give faithful
polynomial matrix actions over every commutative ring, without division by two or three.
The upper and lower transvections have exactly the existing numbered root parameters, and
the diagonal acts through the corresponding simple coroot of the weight torus.

The carrier-valued maps over fields of characteristic three and their exact images are
constructed in `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.RankOne`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The root coefficients and weight basis are those of `TauCeti.G2ShortRoot.raisingMatrix` and
`TauCeti.G2ShortRoot.weight`.
-/

public section

open scoped Matrix MatrixGroups

namespace TauCeti.G2ShortRoot

variable {R : Type*} [CommRing R]

/-- The rank-one matrix in the ordered short-root weight basis. At node zero the middle
three-by-three block is the divided-square action, with its integral coefficient two. -/
def rankOneMatrix (i : Fin 2) (g : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 7) (Fin 7) R :=
  if i = 0 then
    !![g 0 0, g 0 1, 0, 0, 0, 0, 0;
       g 1 0, g 1 1, 0, 0, 0, 0, 0;
       0, 0, g 0 0 ^ 2, 2 * g 0 0 * g 0 1, g 0 1 ^ 2, 0, 0;
       0, 0, g 0 0 * g 1 0, g 0 0 * g 1 1 + g 0 1 * g 1 0, g 0 1 * g 1 1, 0, 0;
       0, 0, g 1 0 ^ 2, 2 * g 1 0 * g 1 1, g 1 1 ^ 2, 0, 0;
       0, 0, 0, 0, 0, g 0 0, g 0 1;
       0, 0, 0, 0, 0, g 1 0, g 1 1]
  else
    !![1, 0, 0, 0, 0, 0, 0;
       0, g 0 0, g 0 1, 0, 0, 0, 0;
       0, g 1 0, g 1 1, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, g 0 0, g 0 1, 0;
       0, 0, 0, 0, g 1 0, g 1 1, 0;
       0, 0, 0, 0, 0, 0, 1]

/-- The entry formula for the two numbered rank-one block actions. -/
theorem rankOneMatrix_def (i : Fin 2) (g : Matrix (Fin 2) (Fin 2) R) :
    rankOneMatrix i g =
      if i = 0 then
        !![g 0 0, g 0 1, 0, 0, 0, 0, 0;
           g 1 0, g 1 1, 0, 0, 0, 0, 0;
           0, 0, g 0 0 ^ 2, 2 * g 0 0 * g 0 1, g 0 1 ^ 2, 0, 0;
           0, 0, g 0 0 * g 1 0, g 0 0 * g 1 1 + g 0 1 * g 1 0, g 0 1 * g 1 1, 0, 0;
           0, 0, g 1 0 ^ 2, 2 * g 1 0 * g 1 1, g 1 1 ^ 2, 0, 0;
           0, 0, 0, 0, 0, g 0 0, g 0 1;
           0, 0, 0, 0, 0, g 1 0, g 1 1]
      else
        !![1, 0, 0, 0, 0, 0, 0;
           0, g 0 0, g 0 1, 0, 0, 0, 0;
           0, g 1 0, g 1 1, 0, 0, 0, 0;
           0, 0, 0, 1, 0, 0, 0;
           0, 0, 0, 0, g 0 0, g 0 1, 0;
           0, 0, 0, 0, g 1 0, g 1 1, 0;
           0, 0, 0, 0, 0, 0, 1] := (rfl)

/-- The explicit rank-one matrix action preserves the identity. -/
@[simp]
theorem rankOneMatrix_one (i : Fin 2) : rankOneMatrix i (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [rankOneMatrix]

/-- The explicit rank-one matrix action is multiplicative, over arbitrary commutative rings. -/
theorem rankOneMatrix_mul (i : Fin 2) (g h : Matrix (Fin 2) (Fin 2) R) :
    rankOneMatrix i (g * h) = rankOneMatrix i g * rankOneMatrix i h := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [rankOneMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private def rankOneMatrixHom (i : Fin 2) : Matrix (Fin 2) (Fin 2) R →*
    Matrix (Fin 7) (Fin 7) R where
  toFun := rankOneMatrix i
  map_one' := rankOneMatrix_one i
  map_mul' := rankOneMatrix_mul i

/-- The faithful rank-one action of SL₂ on the seven-dimensional short-root module. -/
def rankOneGL (R : Type*) [CommRing R] (i : Fin 2) : SL(2, R) →* GL (Fin 7) R :=
  ((rankOneMatrixHom i).comp Matrix.SpecialLinearGroup.coeMonoidHom).toHomUnits

/-- The matrix of the rank-one action is the explicit block matrix. -/
@[simp]
theorem coe_rankOneGL (i : Fin 2) (g : SL(2, R)) :
    (rankOneGL R i g : Matrix (Fin 7) (Fin 7) R) = rankOneMatrix i g := (rfl)

/-- The standard two-dimensional summands make the rank-one action faithful over every
commutative ring, including in characteristics two and three. -/
theorem rankOneGL_injective (i : Fin 2) : Function.Injective (rankOneGL R i) := by
  intro g h heq
  have hm := congrArg (fun x : GL (Fin 7) R => (x : Matrix (Fin 7) (Fin 7) R)) heq
  rw [coe_rankOneGL, coe_rankOneGL] at hm
  apply Subtype.ext
  ext a b
  fin_cases i
  · have hentry := congrFun (congrFun hm (Fin.castLE (by decide : 2 ≤ 7) a))
      (Fin.castLE (by decide : 2 ≤ 7) b)
    fin_cases a <;> fin_cases b <;> simpa [rankOneMatrix] using hentry
  · have hentry := congrFun (congrFun hm (Fin.castAdd 5 a + 1)) (Fin.castAdd 5 b + 1)
    fin_cases a <;> fin_cases b <;> simpa [rankOneMatrix] using hentry

/-- Upper transvections have the prescribed positive simple-root parameters over every ring. -/
@[simp]
theorem rankOneGL_upper_transvection (i : Fin 2) (t : R) :
    rankOneGL R i (Matrix.SpecialLinearGroup.transvection
      (by decide : (0 : Fin 2) ≠ 1) t) =
      (IntegralToralClosure.rootSubgroupPoints (.inl i) R (Multiplicative.ofAdd t) :
        GL (Fin 7) R) := by
  apply Units.ext
  fin_cases i
  · refine Eq.trans ?_ (IntegralToralClosure.coe_rootSubgroupPoints_inl_zero R t).symm
    simp [rankOneMatrix, Matrix.SpecialLinearGroup.transvection_coe]
  · refine Eq.trans ?_ (IntegralToralClosure.coe_rootSubgroupPoints_inl_one R t).symm
    simp [rankOneMatrix, Matrix.SpecialLinearGroup.transvection_coe]

/-- Lower transvections have the prescribed negative simple-root parameters over every ring. -/
@[simp]
theorem rankOneGL_lower_transvection (i : Fin 2) (t : R) :
    rankOneGL R i (Matrix.SpecialLinearGroup.transvection
      (by decide : (1 : Fin 2) ≠ 0) t) =
      (IntegralToralClosure.rootSubgroupPoints (.inr i) R (Multiplicative.ofAdd t) :
        GL (Fin 7) R) := by
  apply Units.ext
  fin_cases i
  · refine Eq.trans ?_ (IntegralToralClosure.coe_rootSubgroupPoints_inr_zero R t).symm
    simp [rankOneMatrix, Matrix.SpecialLinearGroup.transvection_coe]
  · refine Eq.trans ?_ (IntegralToralClosure.coe_rootSubgroupPoints_inr_one R t).symm
    simp [rankOneMatrix, Matrix.SpecialLinearGroup.transvection_coe]

/-- The diagonal of SL₂ acts by the numbered simple coroot of the weight torus. -/
@[simp]
theorem rankOneGL_diag2nUnit (i : Fin 2) (u : Rˣ) :
    rankOneGL R i (Matrix.SpecialLinearGroup.diag2nUnit
      (by decide : (0 : Fin 2) ≠ 1) u) =
      (IntegralToralClosure.weightTorusPoints R (Pi.mulSingle i u) : GL (Fin 7) R) := by
  apply Units.ext
  rw [coe_rankOneGL, IntegralToralClosure.coe_weightTorusPoints_eq_diagonal,
    Matrix.SpecialLinearGroup.diag2nUnit_coe]
  ext a b
  rw [Matrix.diagonal_apply, torusCharacter_mulSingle]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [rankOneMatrix, weight_apply]

end TauCeti.G2ShortRoot

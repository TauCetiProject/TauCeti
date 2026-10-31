/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Rank-one representations on a minuscule weight basis

At a fixed simple node, the weights split into pairs of weights `1,-1` and fixed
weights of coordinate zero. A two-by-two matrix acts on every pair in that order
and fixes the remaining basis vectors. This gives a multiplicative representation;
the standard upper and lower transvections recover the table's root matrices.
-/

public section

open scoped Matrix

namespace TauCeti.MinusculeWeightTable

variable {B ι : Type*} (T : MinusculeWeightTable B ι)
variable [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- The two-by-two block action at a simple node, fixing its weight-zero space. -/
def rankOneMatrix (i : B) (g : Matrix (Fin 2) (Fin 2) R) : Matrix ι ι R :=
  fun a b ↦
    if T.weight b i = 1 then
      g 0 0 * (1 : Matrix ι ι R) a b + g 1 0 * (1 : Matrix ι ι R) a (T.reflection i b)
    else if T.weight b i = -1 then
      g 0 1 * (1 : Matrix ι ι R) a (T.reflection i b) + g 1 1 * (1 : Matrix ι ι R) a b
    else (1 : Matrix ι ι R) a b

private theorem mul_rankOneMatrix_apply (i : B) (g : Matrix (Fin 2) (Fin 2) R)
    (M : Matrix ι ι R) (a b : ι) :
    (M * T.rankOneMatrix i g) a b =
      if T.weight b i = 1 then g 0 0 * M a b + g 1 0 * M a (T.reflection i b)
      else if T.weight b i = -1 then g 0 1 * M a (T.reflection i b) + g 1 1 * M a b
      else M a b := by
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one b i with h | h | h
  all_goals simp [rankOneMatrix, h, Matrix.mul_apply, Matrix.one_apply,
    mul_add, mul_ite, Finset.sum_add_distrib, mul_comm]

omit [Fintype ι] in
/-- The block action preserves the identity matrix. -/
@[simp]
theorem rankOneMatrix_one (i : B) : T.rankOneMatrix i (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext a b
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one b i with h | h | h
  all_goals simp [rankOneMatrix, h]

/-- The block action preserves multiplication. -/
@[simp]
theorem rankOneMatrix_mul (i : B) (g h : Matrix (Fin 2) (Fin 2) R) :
    T.rankOneMatrix i (g * h) = T.rankOneMatrix i g * T.rankOneMatrix i h := by
  ext a b
  rw [mul_rankOneMatrix_apply]
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one b i with hb | hb | hb
  all_goals simp only [rankOneMatrix, hb, T.weight_reflection_self, neg_neg, neg_zero,
    Matrix.mul_apply, Fin.sum_univ_two, Int.reduceNeg, Int.reduceEq, ite_true, ite_false]
  all_goals rw [T.reflection_apply_apply]
  all_goals ring

/-- The multiplicative two-by-two block representation at a simple node. -/
def rankOneMatrixHom (i : B) : Matrix (Fin 2) (Fin 2) R →* Matrix ι ι R where
  toFun := T.rankOneMatrix i
  map_one' := T.rankOneMatrix_one i
  map_mul' := T.rankOneMatrix_mul i

omit [Fintype ι] in
/-- A nontrivial weight pair makes the matrix representation faithful. -/
theorem rankOneMatrix_injective (i : B) (hi : ∃ a, T.weight a i = -1) :
    Function.Injective (T.rankOneMatrix i : Matrix (Fin 2) (Fin 2) R → Matrix ι ι R) := by
  obtain ⟨a, ha⟩ := hi
  have hs : T.weight (T.reflection i a) i = 1 := by simp [ha]
  have hne : T.reflection i a ≠ a := by
    intro h
    rw [h, ha] at hs
    omega
  intro g h hgh
  ext j k
  have he := congrFun (congrFun hgh (if j = 0 then T.reflection i a else a))
    (if k = 0 then T.reflection i a else a)
  fin_cases j <;> fin_cases k <;>
    simpa [rankOneMatrix, ha, hs, Matrix.one_apply, hne, hne.symm] using he

/-- Restriction of the block representation to invertible matrices. -/
def rankOneGL (i : B) : GL (Fin 2) R →* GL ι R :=
  Units.map (T.rankOneMatrixHom i)

/-- The matrix underlying the block representation of an invertible matrix. -/
@[simp]
theorem coe_rankOneGL (i : B) (g : GL (Fin 2) R) :
    (T.rankOneGL i g : Matrix ι ι R) = T.rankOneMatrix i (g : Matrix (Fin 2) (Fin 2) R) := by
  simp [rankOneGL, rankOneMatrixHom]

/-- A weight pair makes the general-linear block representation faithful. -/
theorem rankOneGL_injective (i : B) (hi : ∃ a, T.weight a i = -1) :
    Function.Injective (T.rankOneGL i : GL (Fin 2) R → GL ι R) := by
  intro g h hgh
  apply Units.ext
  apply T.rankOneMatrix_injective i hi
  exact congrArg (fun x : GL ι R ↦ (x : Matrix ι ι R)) hgh

/-- Restriction of the block representation to the special linear group. -/
def rankOneSL (i : B) : Matrix.SpecialLinearGroup (Fin 2) R →* GL ι R :=
  (T.rankOneGL i).comp Matrix.SpecialLinearGroup.toGL

/-- The matrix underlying the special-linear block representation. -/
@[simp]
theorem coe_rankOneSL (i : B) (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    (T.rankOneSL i g : Matrix ι ι R) = T.rankOneMatrix i (g : Matrix (Fin 2) (Fin 2) R) := by
  simp [rankOneSL]

/-- A weight pair makes the special-linear block representation faithful. -/
theorem rankOneSL_injective (i : B) (hi : ∃ a, T.weight a i = -1) :
    Function.Injective (T.rankOneSL i : Matrix.SpecialLinearGroup (Fin 2) R → GL ι R) := by
  intro g h hgh
  apply Subtype.ext
  apply T.rankOneMatrix_injective i hi
  exact congrArg (fun x : GL ι R ↦ (x : Matrix ι ι R)) hgh

omit [Fintype ι] in
/-- The upper transvection acts by the parameterized raising unipotent. -/
theorem rankOneMatrix_upper_transvection (i : B) (t : R) :
    T.rankOneMatrix i (Matrix.transvection 0 1 t) =
      1 + t • (T.raisingMatrix i).map (Int.cast : ℤ → R) := by
  ext a b
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one b i with hb | hb | hb
  all_goals simp [rankOneMatrix, Matrix.transvection, Matrix.one_apply,
    hb, Matrix.smul_apply, smul_eq_mul, add_comm]

omit [Fintype ι] in
/-- The lower transvection acts by the parameterized lowering unipotent. -/
theorem rankOneMatrix_lower_transvection (i : B) (t : R) :
    T.rankOneMatrix i (Matrix.transvection 1 0 t) =
      1 + t • (T.loweringMatrix i).map (Int.cast : ℤ → R) := by
  ext a b
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one b i with hb | hb | hb
  all_goals simp [rankOneMatrix, Matrix.transvection, Matrix.one_apply,
    hb, Matrix.smul_apply, smul_eq_mul]

omit [Fintype ι] in
/-- A diagonal two-by-two matrix acts diagonally according to the three weights. -/
theorem rankOneMatrix_diagonal (i : B) (d : Fin 2 → R) :
    T.rankOneMatrix i (Matrix.diagonal d) = Matrix.diagonal (fun a ↦
      if T.weight a i = 1 then d 0 else if T.weight a i = -1 then d 1 else 1) := by
  ext a b
  rcases T.weight_eq_neg_one_or_eq_zero_or_eq_one b i with hb | hb | hb
  all_goals by_cases hab : a = b
  all_goals simp [rankOneMatrix, Matrix.one_apply, hb, hab]

end TauCeti.MinusculeWeightTable

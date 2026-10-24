/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic

/-!
# The volume element and even part of the split real Clifford plane

In the matrix model of `Cliff(1, 1)`, the product `z = e₁ e₂` of the coordinate generators is
the swap matrix. It satisfies `z² = 1`, `reverse z = -z`, and `star z = -z`. The even Clifford
algebra consists of the elements `a + b z`, uniquely, represented by the matrices `!![a, b; b, a]`.

These are Clifford algebra computations independent of the Spin group and its hyperbolic
parametrization. Both Bott periodicity and the Spin classification use this general layer.

## Main definitions and results

* `CliffordAlgebra.realCliffordOneOneEquivMatrix_e₀_mul_e₁`: the coordinate-generator product
  is the swap matrix.
* `CliffordAlgebra.realCliffordOneOneVolume`: the volume element, with defining equation
  `CliffordAlgebra.realCliffordOneOneVolume_def`.
* `CliffordAlgebra.exists_eq_algebraMap_add_smul_realCliffordOneOneVolume`: the even part is
  spanned by `1` and the volume element.
* `CliffordAlgebra.algebraMap_add_smul_realCliffordOneOneVolume_inj`: these coordinates are unique.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

open TauCeti
open scoped Matrix

namespace CliffordAlgebra

/-- The two coordinate generators of `Cliff(1, 1)` multiply to the swap matrix. -/
theorem realCliffordOneOneEquivMatrix_e₀_mul_e₁ :
    TauCeti.realCliffordOneOneEquivMatrix
        (_root_.CliffordAlgebra.ι (TauCeti.realCliffordForm 1 1) (Pi.single 0 1) *
          _root_.CliffordAlgebra.ι _ (Pi.single 1 1)) =
      !![(0 : ℝ), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TauCeti.realCliffordOneOneEquivMatrix_ι, Matrix.mul_apply, Fin.sum_univ_two]

/-- The product `z = e₁ e₂` of the two coordinate generators of `Cliff(1, 1)`, the generator `e₁`
squaring to `1` and `e₂` to `-1`. -/
noncomputable def realCliffordOneOneVolume : CliffordAlgebra (realCliffordForm 1 1) :=
  ι _ (Pi.single 0 1) * ι _ (Pi.single 1 1)

/-- The volume element is the product of the positive and negative coordinate generators. -/
theorem realCliffordOneOneVolume_def :
    realCliffordOneOneVolume =
      ι (realCliffordForm 1 1) (Pi.single 0 1) * ι _ (Pi.single 1 1) := (rfl)

/-- In the matrix model of `Cliff(1, 1)`, `a + b z` is the matrix `!![a, b; b, a]`. -/
theorem realCliffordOneOneEquivMatrix_algebraMap_add_smul_realCliffordOneOneVolume (a b : ℝ) :
    realCliffordOneOneEquivMatrix
        (algebraMap ℝ (CliffordAlgebra (realCliffordForm 1 1)) a + b • realCliffordOneOneVolume) =
      !![a, b; b, a] := by
  rw [map_add, map_smul, AlgEquiv.commutes, realCliffordOneOneVolume_def,
    realCliffordOneOneEquivMatrix_e₀_mul_e₁]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.algebraMap_eq_diagonal]

/-- `z² = 1`. -/
@[simp]
theorem realCliffordOneOneVolume_mul_self :
    realCliffordOneOneVolume * realCliffordOneOneVolume = 1 := by
  apply realCliffordOneOneEquivMatrix.injective
  rw [map_mul, realCliffordOneOneVolume_def,
    realCliffordOneOneEquivMatrix_e₀_mul_e₁, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `z` is even: the grade involution fixes it. -/
@[simp]
theorem involute_realCliffordOneOneVolume :
    involute realCliffordOneOneVolume = realCliffordOneOneVolume := by
  rw [realCliffordOneOneVolume_def, map_mul, involute_ι, involute_ι, neg_mul_neg]

/-- `star z = -z`. -/
@[simp]
theorem star_realCliffordOneOneVolume :
    star realCliffordOneOneVolume = -realCliffordOneOneVolume := by
  apply realCliffordOneOneEquivMatrix.injective
  rw [realCliffordOneOneVolume_def, star_mul, star_ι, star_ι, neg_mul_neg, map_mul, map_neg,
    map_mul, realCliffordOneOneEquivMatrix_ι, realCliffordOneOneEquivMatrix_ι]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `reverse z = -z`. -/
@[simp]
theorem reverse_realCliffordOneOneVolume :
    reverse realCliffordOneOneVolume = -realCliffordOneOneVolume := by
  rw [← star_realCliffordOneOneVolume, star_def, involute_realCliffordOneOneVolume]

/-- The coefficients `a` and `b` of `a + b z` are unique. -/
theorem algebraMap_add_smul_realCliffordOneOneVolume_inj {a b a' b' : ℝ} :
    algebraMap ℝ (CliffordAlgebra (realCliffordForm 1 1)) a + b • realCliffordOneOneVolume =
        algebraMap ℝ _ a' + b' • realCliffordOneOneVolume ↔ a = a' ∧ b = b' := by
  refine ⟨fun h ↦ ?_, fun ⟨ha, hb⟩ ↦ by rw [ha, hb]⟩
  have h' := congrArg realCliffordOneOneEquivMatrix h
  rw [realCliffordOneOneEquivMatrix_algebraMap_add_smul_realCliffordOneOneVolume,
    realCliffordOneOneEquivMatrix_algebraMap_add_smul_realCliffordOneOneVolume] at h'
  exact ⟨by simpa using congrFun (congrFun h' 0) 0, by simpa using congrFun (congrFun h' 0) 1⟩

/-- **The even part of `Cliff(1, 1)`.** Every even element is `a + b z` for some real `a`, `b`. -/
theorem exists_eq_algebraMap_add_smul_realCliffordOneOneVolume
    {x : CliffordAlgebra (realCliffordForm 1 1)} (hx : x ∈ even (realCliffordForm 1 1)) :
    ∃ a b : ℝ, x = algebraMap ℝ _ a + b • realCliffordOneOneVolume := by
  -- In the matrix model the even elements are the matrices `!![a, b; b, a]`: this holds for the
  -- scalars and is preserved by sums and by left multiplication by a product of two generators.
  suffices ∃ a b : ℝ, realCliffordOneOneEquivMatrix x = !![a, b; b, a] by
    obtain ⟨a, b, h⟩ := this
    exact ⟨a, b, realCliffordOneOneEquivMatrix.injective (by
      rw [h, realCliffordOneOneEquivMatrix_algebraMap_add_smul_realCliffordOneOneVolume])⟩
  replace hx : x ∈ evenOdd (realCliffordForm 1 1) 0 := by
    rwa [← even_toSubmodule, Subalgebra.mem_toSubmodule]
  induction x, hx using even_induction with
  | algebraMap r =>
    refine ⟨r, 0, ?_⟩
    rw [AlgEquiv.commutes]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.algebraMap_eq_diagonal]
  | add x y _ _ ihx ihy =>
    obtain ⟨a, b, hx⟩ := ihx
    obtain ⟨c, d, hy⟩ := ihy
    refine ⟨a + c, b + d, ?_⟩
    rw [map_add, hx, hy]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | ι_mul_ι_mul m₁ m₂ x _ ih =>
    obtain ⟨a, b, hx⟩ := ih
    refine ⟨(m₁ 0 * m₂ 0 - m₁ 1 * m₂ 1) * a + (m₁ 0 * m₂ 1 - m₁ 1 * m₂ 0) * b,
      (m₁ 0 * m₂ 0 - m₁ 1 * m₂ 1) * b + (m₁ 0 * m₂ 1 - m₁ 1 * m₂ 0) * a, ?_⟩
    rw [map_mul, map_mul, hx, realCliffordOneOneEquivMatrix_ι, realCliffordOneOneEquivMatrix_ι]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The Clifford conjugate of `a + b z` is `a - b z`. -/
theorem star_algebraMap_add_smul_realCliffordOneOneVolume (a b : ℝ) :
    star (algebraMap ℝ (CliffordAlgebra (realCliffordForm 1 1)) a + b • realCliffordOneOneVolume) =
      algebraMap ℝ _ a + (-b) • realCliffordOneOneVolume := by
  rw [star_add, star_smul, star_realCliffordOneOneVolume, star_algebraMap, smul_neg, neg_smul]

end CliffordAlgebra

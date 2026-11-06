/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ExteriorPower.Plucker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.AbsoluteValue.Int

/-!
# Nonarchimedean changes of coordinates for Plücker vectors

A matrix whose entries lie in the unit ball of a nonarchimedean absolute value
contracts the maximum norm on every exterior power. If its inverse also has
entries in the unit ball, it preserves these norms.

A maximal minor of a linearly independent family provides a pivot matrix.
Cramer's rule shows that normalizing by this matrix puts every entry in the
unit ball. This is the local row reduction used to compare exterior norms of
intersecting subspaces, without a discreteness or completeness assumption on
the valued field.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), §2.8.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative
  Subspace Theorem*, Ann. of Math. 177 (2013), §6.1, (6.12).
-/

public section

open scoped BigOperators Matrix
open Set TauCeti

namespace AbsoluteValue

variable {ι κ : Type*} [LinearOrder ι] [Fintype ι] [LinearOrder κ] {p : ℕ}

section Ring

variable {K : Type*} [CommRing K]

omit [Fintype ι] in
/-- Every maximal minor, even one with repeated columns, is bounded by the
maximum of the Plücker coordinates. -/
theorem det_submatrix_le_iSup_plucker [Finite ι] (v : AbsoluteValue K ℝ) [Nontrivial K]
    (x : Matrix (Fin p) ι K) (e : Fin p → ι) :
    v (x.submatrix id e).det ≤ ⨆ s, v (plucker x.row s) := by
  classical
  by_cases he : Function.Injective e
  · obtain ⟨σ, hσ⟩ := x.exists_det_submatrix_eq_sign_mul_plucker ⟨e, he⟩
    simp only [Function.Embedding.coeFn_mk] at hσ
    rw [hσ, map_mul, v.map_units_intCast, one_mul]
    exact Finite.le_ciSup_of_le _ le_rfl
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp he
    rw [Matrix.det_zero_of_column_eq hne (fun k ↦ by simp [hij]), map_zero]
    exact Real.iSup_nonneg_of_nonnegHomClass v _

/-- A matrix with entries in the nonarchimedean unit ball contracts the
maximum norm on every exterior power. -/
theorem iSup_plucker_mul_le (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (x : Matrix (Fin p) ι K) {A : Matrix ι κ K} (hA : ∀ i j, v (A i j) ≤ 1) :
    (⨆ s, v (plucker (x * A).row s)) ≤ ⨆ s, v (plucker x.row s) := by
  classical
  refine Real.iSup_le (fun s ↦ ?_) (Real.iSup_nonneg_of_nonnegHomClass v _)
  let e := Set.powersetCard.ofFinEmbEquiv.symm s
  have hmul : plucker (x * A).row s = (x * A.submatrix id e).det := by
    rw [plucker_apply]
    congr 1
  rw [hmul]
  have hcb := det_mul_transpose_eq_sum_plucker_mul x.row (A.submatrix id e).transpose.row
  simp only [Matrix.row_eq_self, Equiv.apply_symm_apply, Matrix.transpose_transpose] at hcb
  rw [hcb]
  by_cases hp : Nonempty (powersetCard ι p)
  · let _ := hp
    refine (hv.apply_sum_le_sup Finset.univ_nonempty).trans ?_
    refine Finset.sup'_le _ _ fun t _ ↦ ?_
    rw [map_mul]
    have hb : v (plucker (A.submatrix id e).transpose.row t) ≤ 1 := by
      refine (v.plucker_le_prod_iSup hv _ t).trans ?_
      refine (Finset.prod_le_prod₀ (fun _ _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _)
        fun i _ ↦ ?_).trans_eq (Finset.prod_const_one)
      exact Real.iSup_le (fun j ↦ hA j (e i)) zero_le_one
    exact (mul_le_of_le_one_right (v.nonneg _) hb).trans (Finite.le_ciSup_of_le _ le_rfl)
  · have : IsEmpty (powersetCard ι p) := not_nonempty_iff.mp hp
    simp only [Finset.univ_eq_empty, Finset.sum_empty, map_zero]
    exact Real.iSup_nonneg_of_nonnegHomClass v _

/-- A change of coordinates integral in both directions preserves all
nonarchimedean exterior maximum norms. -/
theorem iSup_plucker_mul_eq (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (x : Matrix (Fin p) ι K) {A B : Matrix ι ι K}
    (hA : ∀ i j, v (A i j) ≤ 1) (hB : ∀ i j, v (B i j) ≤ 1) (hAB : A * B = 1) :
    (⨆ s, v (plucker (x * A).row s)) = ⨆ s, v (plucker x.row s) := by
  apply le_antisymm (v.iSup_plucker_mul_le hv x hA)
  simpa only [Matrix.mul_assoc, hAB, Matrix.mul_one] using
    v.iSup_plucker_mul_le hv (x * A) hB

end Ring

section Field

variable {K : Type*} [Field K]

omit [Fintype ι] in
/-- A largest maximal minor is an invertible pivot matrix, and normalizing
by it puts every entry in the absolute-value unit ball. No nonarchimedean
hypothesis is needed for this pivot selection. -/
theorem exists_pivot_inv_mul_le_one [Finite ι] (v : AbsoluteValue K ℝ)
    {x : Matrix (Fin p) ι K} (hx : LinearIndependent K x.row) :
    ∃ e : Fin p ↪ ι, (x.submatrix id e).det ≠ 0 ∧
      v (x.submatrix id e).det = (⨆ s, v (plucker x.row s)) ∧
      ∀ i j, v (((x.submatrix id e)⁻¹ * x) i j) ≤ 1 := by
  classical
  let _ := Fintype.ofFinite ι
  have hp := (plucker_ne_zero_iff x.row).mpr hx
  obtain ⟨s₀, hs₀⟩ := Function.ne_iff.mp hp
  have : Nonempty (powersetCard ι p) := ⟨s₀⟩
  obtain ⟨s, hs⟩ := exists_eq_ciSup_of_finite (f := fun t ↦ v (plucker x.row t))
  let e : Fin p ↪ ι := (powersetCard.ofFinEmbEquiv.symm s).toEmbedding
  let P := x.submatrix id e
  have hP : P.det = plucker x.row s := by
    rw [plucker_apply]
    congr 1
  have hP0 : P.det ≠ 0 := by
    intro hz
    have hpos := v.pos (by simpa using hs₀)
    have hle : v (plucker x.row s₀) ≤ ⨆ t, v (plucker x.row t) :=
      Finite.le_ciSup_of_le s₀ le_rfl
    rw [← hs, ← hP, hz, map_zero] at hle
    linarith
  refine ⟨e, hP0, hP ▸ hs, fun i j ↦ ?_⟩
  have hcr := congrFun (P.det_smul_inv_mulVec_eq_cramer (fun k ↦ x k j)
    (isUnit_iff_ne_zero.mpr hP0)) i
  have heq : P.updateCol i (fun k ↦ x k j) = x.submatrix id (Function.update e i j) := by
    ext k l
    simp only [P, Matrix.updateCol_apply, Matrix.submatrix_apply, id_eq, Function.update_apply]
    split_ifs <;> rfl
  have hb := v.det_submatrix_le_iSup_plucker x (Function.update e i j)
  rw [← hs, ← hP, ← heq] at hb
  have hid : P.det * (P⁻¹ * x) i j = (P.updateCol i (fun k ↦ x k j)).det := by
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.cramer_apply] using hcr
  rw [← hid, map_mul] at hb
  exact (mul_le_mul_iff_right₀ (v.pos hP0)).mp (by simpa [mul_comm] using hb)

/-- A matrix supported on the pivot rows and the non-pivot columns, with entries in the unit ball
whenever those of a given family `B` are, and agreeing with `B` there, has square zero. -/
private theorem exists_shear (v : AbsoluteValue K ℝ) (e : Fin p ↪ ι) (B : Matrix (Fin p) ι K)
    (hb : ∀ a j, v (B a j) ≤ 1) :
    ∃ N : Matrix ι ι K, N * N = 0 ∧ (∀ i j, v (N i j) ≤ 1) ∧
      (∀ i, ∀ j ∈ range e, N i j = 0) ∧ (∀ i ∉ range e, ∀ j, N i j = 0) ∧
      ∀ a j, j ∉ range e → N (e a) j = B a j := by
  classical
  let N : Matrix ι ι K := Matrix.of
    (Function.extend e (fun a j ↦ if j ∈ range e then 0 else B a j) 0)
  have hrow (a : Fin p) (j : ι) : N (e a) j = if j ∈ range e then 0 else B a j := by
    simp [N, e.injective.extend_apply]
  have hout {i : ι} (hi : i ∉ range e) (j : ι) : N i j = 0 := by
    simp [N, Function.extend_apply' _ _ _ hi]
  have hcol (i : ι) {j : ι} (hj : j ∈ range e) : N i j = 0 := by
    by_cases hi : i ∈ range e
    · obtain ⟨a, rfl⟩ := hi
      simp [hrow, hj]
    · exact hout hi j
  refine ⟨N, ?_, fun i j ↦ ?_, hcol, fun i hi j ↦ hout hi j, fun a j hj ↦ by simp [hrow, hj]⟩
  · ext i j
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    by_cases hk : k ∈ range e
    · simp [hcol i hk]
    · simp [hout hk j]
  · by_cases hi : i ∈ range e
    · obtain ⟨a, rfl⟩ := hi
      rw [hrow]
      split_ifs
      · simp
      · exact hb a j
    · simp [hout hi j]

/-- An independent family can be supported on pivot coordinates by a change
of coordinates integral in both directions. Its pivot determinant attains the
original exterior maximum norm. Together with `iSup_plucker_mul_eq`, this
reduces local exterior-norm comparisons to a coordinate subspace. -/
theorem exists_integral_plucker_reduction (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {x : Matrix (Fin p) ι K} (hx : LinearIndependent K x.row) :
    ∃ (e : Fin p ↪ ι) (Q Q' : Matrix ι ι K),
      (x.submatrix id e).det ≠ 0 ∧
      v (x.submatrix id e).det = (⨆ s, v (plucker x.row s)) ∧
      Q * Q' = 1 ∧ Q' * Q = 1 ∧
      (∀ i j, v (Q i j) ≤ 1) ∧ (∀ i j, v (Q' i j) ≤ 1) ∧
      ∀ i j, (x * Q) i j = if j ∈ range e then x i j else 0 := by
  classical
  obtain ⟨e, he, hm, hb⟩ := v.exists_pivot_inv_mul_le_one hx
  let P := x.submatrix id e
  let B := P⁻¹ * x
  have hPB : P * B = x := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr he),
      Matrix.one_mul]
  -- Extend the off-pivot columns of the normalized family by zero on the
  -- other rows. This shear has square zero.
  obtain ⟨N, hNN, hN, hcol, hout, hrow⟩ := v.exists_shear e B hb
  have hunit (i j : ι) : v ((1 : Matrix ι ι K) i j) ≤ 1 := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hbound (i j : ι) : v ((1 - N) i j) ≤ 1 ∧ v ((1 + N) i j) ≤ 1 := by
    constructor
    · rw [Matrix.sub_apply, sub_eq_add_neg]
      exact (hv _ _).trans (max_le (hunit i j) (by simpa using hN i j))
    · exact (hv _ _).trans (max_le (hunit i j) (hN i j))
  refine ⟨e, 1 - N, 1 + N, he, hm, ?_, ?_, fun i j ↦ (hbound i j).1,
    fun i j ↦ (hbound i j).2, ?_⟩
  · simp [sub_mul, mul_add, hNN]
  · simp [mul_sub, add_mul, hNN]
  -- Summing over the pivot rows recovers P B = x off the pivot columns;
  -- the shear vanishes on the pivot columns themselves.
  · intro i j
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply]
    by_cases hj : j ∈ range e
    · simp [hj, Matrix.mul_apply, hcol _ _ hj]
    · have hsum : (x * N) i j = (P * B) i j := by
        rw [Matrix.mul_apply, Matrix.mul_apply]
        exact (Fintype.sum_of_injective e e.injective _ _
          (fun k hk ↦ by simp [hout k hk j])
          (fun a ↦ by simp [P, hrow _ _ hj])).symm
      simp [hj, hsum, hPB]

end Field

end AbsoluteValue

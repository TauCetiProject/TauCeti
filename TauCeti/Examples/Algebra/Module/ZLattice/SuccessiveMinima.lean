/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima

/-!
# Successive minima of coordinate boxes

For the standard integer lattice in real coordinate space, the unit cube has all successive
minima equal to one. The rectangle with half-widths two and one has minima one half and one,
in zero-based index order. Doubling the cube halves every minimum. In dimension zero the
index type is empty and the product of the minima is one.

The proofs work directly with `ZLattice.successiveMin`: the displayed independent integer
vectors attain the thresholds, while a nonzero integer coordinate gives the lower bounds.
-/

public section

open Set Module
open scoped Pointwise Topology NNReal
namespace TauCeti.Examples.SuccessiveMinima

/-- The standard integer lattice, spanned by the real coordinate basis over `ℤ`. -/
noncomputable def integerLattice (d : ℕ) : Submodule ℤ (Fin d → ℝ) :=
  Submodule.span ℤ (range (Pi.basisFun ℝ (Fin d)))

private theorem mem_integerLattice_iff (d : ℕ) {x : Fin d → ℝ} :
    x ∈ integerLattice d ↔ ∀ j, ∃ z : ℤ, (z : ℝ) = x j := by
  simpa [integerLattice] using (Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ x

/-- The centered coordinate box with specified nonnegative half-widths. -/
noncomputable def box {d : ℕ} (r : Fin d → ℝ≥0) : ConvexBody (Fin d → ℝ) where
  carrier := pi univ (fun i => Icc (-(r i : ℝ)) (r i : ℝ))
  convex' := convex_pi fun _ _ => convex_Icc _ _
  isCompact' := isCompact_univ_pi fun _ => isCompact_Icc
  nonempty' := ⟨0, fun i _ => ⟨neg_nonpos.mpr (r i).coe_nonneg, (r i).coe_nonneg⟩⟩

private theorem mem_box_iff {d : ℕ} (r : Fin d → ℝ≥0) (x : Fin d → ℝ) :
    x ∈ box r ↔ ∀ i, |x i| ≤ r i := by
  change (∀ i, i ∈ univ → -(r i : ℝ) ≤ x i ∧ x i ≤ (r i : ℝ)) ↔ _
  simp only [mem_univ, forall_const, abs_le]

private theorem basis_mem_integerLattice (d : ℕ) (j : Fin d) :
    Pi.basisFun ℝ (Fin d) j ∈ integerLattice d :=
  Submodule.subset_span (mem_range_self j)

private theorem one_le_abs_int {z : ℤ} (hz : z ≠ 0) : (1 : ℝ) ≤ |(z : ℝ)| := by
  exact_mod_cast (show (1 : ℤ) ≤ |z| by have := abs_pos.mpr hz; omega)

private theorem one_le_of_nonzero_mem_dilate_cube {d : ℕ} {t : ℝ} (ht : 0 ≤ t)
    {x : Fin d → ℝ} (hx : x ∈ integerLattice d) (h0 : x ≠ 0)
    (hxt : x ∈ t • (box (d := d) (fun _ => 1) : Set (Fin d → ℝ))) : 1 ≤ t := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp h0
  obtain ⟨z, hz⟩ := (mem_integerLattice_iff d).mp hx i
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz; exact hi hz.symm
  have hone : 1 ≤ |x i| := hz ▸ one_le_abs_int hz0
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hxt
  have hyi := (mem_box_iff _ _).mp hy i
  have hone' : 1 ≤ t * |y i| := by
    simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht] using hone
  exact hone'.trans ((mul_le_mul_of_nonneg_left hyi ht).trans_eq (mul_one t))

private theorem cube_vectors (d : ℕ) (i : Fin (finrank ℝ (Fin d → ℝ))) :
    ∃ v : Fin (i.val + 1) → Fin d → ℝ, LinearIndependent ℝ v ∧
      ∀ j, v j ∈ integerLattice d ∧ v j ∈ box (d := d) (fun _ => 1) := by
  classical
  have hid : i.val < d := by simpa using i.isLt
  let v : Fin (i.val + 1) → Fin d → ℝ :=
    fun j => Pi.basisFun ℝ (Fin d) (Fin.castLE (Nat.succ_le_of_lt hid) j)
  have hv : LinearIndependent ℝ v :=
    (Pi.basisFun ℝ (Fin d)).linearIndependent.comp _ (Fin.castLE_injective _)
  have hvL : ∀ j, v j ∈ integerLattice d := fun j => basis_mem_integerLattice d _
  have hvK : ∀ j, v j ∈ box (d := d) (fun _ => 1) := by
    intro j
    rw [mem_box_iff]
    intro k
    simp only [v, Pi.basisFun_apply, Pi.single_apply, NNReal.coe_one]
    split_ifs <;> norm_num
  exact ⟨v, hv, fun j => ⟨hvL j, hvK j⟩⟩

/-- Every successive minimum of the standard integer lattice in the unit cube is one. -/
theorem successiveMin_cube (d : ℕ) (i : Fin (finrank ℝ (Fin d → ℝ))) :
    ZLattice.successiveMin (integerLattice d) (box (fun _ => 1)) i = 1 := by
  obtain ⟨v, hv, hvm⟩ := cube_vectors d i
  rw [ZLattice.successiveMin_def]
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨zero_le_one, v, hv, fun j => ⟨(hvm j).1, by simpa using (hvm j).2⟩⟩
  · rintro t ⟨ht, w, hw, hwm⟩
    exact one_le_of_nonzero_mem_dilate_cube ht (hwm 0).1 (hw.ne_zero 0) (hwm 0).2

/-- The first minimum for the rectangle `[-2, 2] × [-1, 1]` is one half. -/
theorem successiveMin_rectangle_zero :
    ZLattice.successiveMin (integerLattice 2) (box ![2, 1]) ⟨0, by simp⟩ = 1 / 2 := by
  classical
  let v : Fin 1 → Fin 2 → ℝ := fun _ => Pi.basisFun ℝ (Fin 2) 0
  have hv : LinearIndependent ℝ v := by
    rw [linearIndependent_unique_iff]
    exact (Pi.basisFun ℝ (Fin 2)).ne_zero 0
  rw [ZLattice.successiveMin_def]
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨by norm_num, v, hv, fun j => ⟨basis_mem_integerLattice 2 0, ?_⟩⟩
    refine Set.mem_smul_set.mpr ⟨![2, 0], ?_, ?_⟩
    · change (![2, 0] : Fin 2 → ℝ) ∈ box ![2, 1]
      rw [mem_box_iff]
      intro k
      fin_cases k <;> norm_num
    · ext k
      fin_cases k <;> norm_num [v, Pi.basisFun_apply, Pi.single_apply]
  · rintro t ⟨ht, w, hw, hwm⟩
    obtain ⟨k, hk⟩ : ∃ k, w 0 k ≠ 0 := Function.ne_iff.mp (hw.ne_zero 0)
    obtain ⟨z, hz⟩ := (mem_integerLattice_iff 2).mp (hwm 0).1 k
    have hz0 : z ≠ 0 := by intro h; simp [h] at hz; exact hk hz.symm
    have hone : 1 ≤ |w 0 k| := hz ▸ one_le_abs_int hz0
    obtain ⟨y, hy, heq⟩ := Set.mem_smul_set.mp (hwm 0).2
    have hyk : |y k| ≤ 2 := by
      have h := (mem_box_iff _ _).mp hy k
      fin_cases k <;> norm_num at h ⊢ <;> linarith
    have hle : |w 0 k| ≤ t * 2 := by
      rw [← heq]
      simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht] using
        mul_le_mul_of_nonneg_left hyk ht
    linarith

private theorem exists_second_coordinate_ne_zero {w : Fin 2 → Fin 2 → ℝ}
    (hw : LinearIndependent ℝ w) : ∃ j, w j 1 ≠ 0 := by
  by_contra h
  push Not at h
  have hsum : ∑ j : Fin 2, (![w 1 0, -(w 0 0)] : Fin 2 → ℝ) j • w j = 0 := by
    ext k
    fin_cases k <;> simp [Fin.sum_univ_two, h, mul_comm]
  have hc := Fintype.linearIndependent_iff.mp hw _ hsum 1
  have h00 : w 0 0 = 0 := by simpa using hc
  exact hw.ne_zero 0 (by ext k; fin_cases k <;> simp [h00, h])

/-- The second minimum for the rectangle `[-2, 2] × [-1, 1]` is one. -/
theorem successiveMin_rectangle_one :
    ZLattice.successiveMin (integerLattice 2) (box ![2, 1]) ⟨1, by simp⟩ = 1 := by
  classical
  rw [ZLattice.successiveMin_def]
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨zero_le_one, Pi.basisFun ℝ (Fin 2), (Pi.basisFun ℝ (Fin 2)).linearIndependent,
      fun j => ⟨basis_mem_integerLattice 2 j, ?_⟩⟩
    rw [one_smul]
    change Pi.basisFun ℝ (Fin 2) j ∈ box ![2, 1]
    rw [mem_box_iff]
    intro k
    fin_cases j <;> fin_cases k <;> norm_num [Pi.basisFun_apply, Pi.single_apply]
  · rintro t ⟨ht, w, hw, hwm⟩
    obtain ⟨j, hj⟩ := exists_second_coordinate_ne_zero hw
    obtain ⟨z, hz⟩ := (mem_integerLattice_iff 2).mp (hwm j).1 1
    have hz0 : z ≠ 0 := by intro h; simp [h] at hz; exact hj hz.symm
    have hone : 1 ≤ |w j 1| := hz ▸ one_le_abs_int hz0
    obtain ⟨y, hy, heq⟩ := Set.mem_smul_set.mp (hwm j).2
    have hy1 : |y 1| ≤ 1 := (mem_box_iff _ _).mp hy 1
    have hle : |w j 1| ≤ t := by
      rw [← heq]
      simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht, mul_one] using
        mul_le_mul_of_nonneg_left hy1 ht
    exact hone.trans hle

/-- Doubling the cube halves all successive minima of the fixed integer lattice. -/
theorem successiveMin_double_cube (d : ℕ) (i : Fin (finrank ℝ (Fin d → ℝ))) :
    ZLattice.successiveMin (integerLattice d) ((2 : ℝ) • box (fun _ => 1)) i = 1 / 2 := by
  obtain ⟨v, hv, hvm⟩ := cube_vectors d i
  rw [ZLattice.successiveMin_def]
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨by norm_num, v, hv, fun j => ⟨(hvm j).1, ?_⟩⟩
    rw [ConvexBody.coe_smul, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
    change v j ∈ box (d := d) (fun _ => 1)
    exact (hvm j).2
  · rintro t ⟨ht, w, hw, hwm⟩
    have hmem : w 0 ∈ (t * 2) • (box (d := d) (fun _ => 1) : Set (Fin d → ℝ)) := by
      simpa only [ConvexBody.coe_smul, smul_smul] using (hwm 0).2
    have h := one_le_of_nonzero_mem_dilate_cube (mul_nonneg ht (by norm_num))
      (hwm 0).1 (hw.ne_zero 0) hmem
    linarith

/-- The zero-dimensional coordinate space has no successive-minimum index. -/
theorem isEmpty_minimumIndex_zero : IsEmpty (Fin (finrank ℝ (Fin 0 → ℝ))) := by
  simp

/-- The product of successive minima in dimension zero is the empty product, one. -/
theorem prod_successiveMin_zero :
    ∏ i, ZLattice.successiveMin (integerLattice 0) (box (fun _ => 1)) i = 1 := by
  let := isEmpty_minimumIndex_zero
  simp

end TauCeti.Examples.SuccessiveMinima

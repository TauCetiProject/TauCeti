/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Neat

/-!
# Examples of neat and non-neat complex matrices

Neatness of a rational matrix is tested on its complex eigenvalues. This file computes three
standard examples in `GL₂(ℂ)`:

* `TauCeti.isNeat_toLin_diagGL_two_inv_two`: `diag(2, 1/2)` is neat, since its eigenvalues
  generate the infinite cyclic group `2 ^ ℤ`.
* `TauCeti.not_isNeat_toLin_orderThree`: the element `(0, -1; 1, -1)` of order three of `SL₂(ℤ)`
  is not neat, as no nontrivial element of finite order is.
* `TauCeti.not_isNeat_toLin_twoMulOrderSix` and `TauCeti.not_isOfFinOrder_twoMulOrderSix`: the
  matrix `2 • (0, -1; 1, 1) = (0, -2; 2, 2)` has determinant `4`, hence infinite order, yet it
  is not neat. Its eigenvalues are `2ω` and `2ω⁻¹` for a primitive sixth root of unity `ω`, and
  their quotient `ω²` is a primitive cube root of unity. So neatness is strictly stronger than
  generating a torsion-free cyclic group.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §3, p. 34.
-/

public section

namespace TauCeti

open LinearMap.GeneralLinearGroup Matrix.GeneralLinearGroup

/-- The diagonal matrix `diag(2, 1/2)`, the image in `GL₂(ℂ)` of an element of `SL₂(ℚ)`, is
neat: its eigenvalues `2` and `1/2` generate the infinite cyclic group `2 ^ ℤ`. -/
theorem isNeat_toLin_diagGL_two_inv_two :
    IsNeat (toLin (diagGL
      ![Units.mk0 (2 : ℂ) two_ne_zero, (Units.mk0 (2 : ℂ) two_ne_zero)⁻¹])) := by
  set u := Units.mk0 (2 : ℂ) two_ne_zero
  refine isNeat_iff.mpr fun z hz hfin ↦ ?_
  rw [eigenvalueSubgroup_toLin_diagGL] at hz
  have hle : Subgroup.closure (Set.range ![u, u⁻¹]) ≤ Subgroup.zpowers u := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Subgroup.mem_zpowers u
    · exact inv_mem (Subgroup.mem_zpowers u)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hle hz)
  obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have hnorm : ‖((u ^ k : ℂˣ) : ℂ)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one])
      hm.ne'
  have hk : k = 0 := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, Units.val_mk0, Complex.norm_two] at hnorm
    exact (zpow_eq_one_iff_right₀ zero_le_two (by norm_num)).mp hnorm
  rw [hk, zpow_zero]

/-- The element `(0, -1; 1, -1)` of order three of `SL₂(ℤ)`, viewed in `GL₂(ℂ)`, is not neat:
a neat element of finite order is trivial. -/
theorem not_isNeat_toLin_orderThree :
    ¬ IsNeat (toLin (mkOfDetNeZero !![(0 : ℂ), -1; 1, -1] (by simp [Matrix.det_fin_two]))) := by
  set g := mkOfDetNeZero !![(0 : ℂ), -1; 1, -1] (by simp [Matrix.det_fin_two])
  have hg3 : g ^ 3 = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, val_mkOfDetNeZero, Units.val_one]
    simp [pow_succ, Matrix.one_fin_two]
  have hg1 : g ≠ 1 := by
    intro h
    simpa [g] using congr(($h : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
  intro hneat
  have hfin : IsOfFinOrder (toLin g) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, by rw [← map_pow, hg3, map_one]⟩
  exact hg1 (toLin.injective ((hneat.eq_one_of_isOfFinOrder hfin).trans (map_one toLin).symm))

/-- If `r` is a root of `X² - X + 1`, then `2r` is an eigenvalue of `(0, -2; 2, 2)`, with
eigenvector `(1, -r)`. -/
private theorem hasEigenvalue_twoMulOrderSix {r : ℂ} (hr : r ^ 2 - r + 1 = 0)
    (h4 : Matrix.det !![(0 : ℂ), -2; 2, 2] ≠ 0) :
    Module.End.HasEigenvalue
      (toLin (mkOfDetNeZero !![(0 : ℂ), -2; 2, 2] h4) : Module.End ℂ (Fin 2 → ℂ)) (2 * r) := by
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := ![1, -r])
    ⟨Module.End.mem_eigenspace_iff.mpr ?_, fun h ↦ by simpa using congr_fun h 0⟩
  ext i
  fin_cases i
  · simp [val_mkOfDetNeZero, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [val_mkOfDetNeZero, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination 2 * hr

/-- The matrix `2 • (0, -1; 1, 1) = (0, -2; 2, 2)` in `GL₂(ℂ)` is not neat: its eigenvalues are
`2ω` and `2(1 - ω)` for a root `ω` of `X² - X + 1`, and their quotient is a nontrivial cube root
of unity. -/
theorem not_isNeat_toLin_twoMulOrderSix :
    ¬ IsNeat (toLin (mkOfDetNeZero !![(0 : ℂ), -2; 2, 2] (by norm_num [Matrix.det_fin_two]))) := by
  intro hneat
  obtain ⟨s, hs⟩ := IsAlgClosed.isSquare (-3 : ℂ)
  set ω : ℂ := (1 + s) / 2
  have hω : ω ^ 2 - ω + 1 = 0 := by linear_combination (-1 / 4 : ℂ) * hs
  have hω' : (1 - ω) ^ 2 - (1 - ω) + 1 = 0 := by linear_combination hω
  have h0 : 2 * ω ≠ 0 := by
    refine mul_ne_zero two_ne_zero fun h ↦ ?_
    simp [h] at hω
  have h1 : 2 * (1 - ω) ≠ 0 := by
    refine mul_ne_zero two_ne_zero fun h ↦ ?_
    simp [h] at hω'
  set u₁ := Units.mk0 (2 * ω) h0
  set u₂ := Units.mk0 (2 * (1 - ω)) h1
  have hcube : u₁ ^ 3 = u₂ ^ 3 := by
    refine Units.ext ?_
    simp only [Units.val_pow_eq_pow_val, u₁, u₂, Units.val_mk0]
    linear_combination 8 * (2 * ω - 1) * hω
  have hne : u₁ ≠ u₂ := by
    intro h
    have h2 : 2 * ω = 2 * (1 - ω) := by simpa [u₁, u₂] using congr(($h : ℂ))
    have h' : ω = 1 / 2 := by linear_combination h2 / 4
    rw [h'] at hω
    norm_num at hω
  refine hne (mul_inv_eq_one.mp (isNeat_iff.mp hneat _ ?_ ?_))
  · exact mul_mem (mem_eigenvalueSubgroup_of_hasEigenvalue (hasEigenvalue_twoMulOrderSix hω _))
      (inv_mem (mem_eigenvalueSubgroup_of_hasEigenvalue (hasEigenvalue_twoMulOrderSix hω' _)))
  · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, by rw [mul_pow, inv_pow, hcube,
      mul_inv_cancel]⟩

/-- The matrix `(0, -2; 2, 2)` has determinant `4`, so it has infinite order in `GL₂(ℂ)`. -/
theorem not_isOfFinOrder_twoMulOrderSix :
    ¬ IsOfFinOrder (mkOfDetNeZero !![(0 : ℂ), -2; 2, 2] (by norm_num [Matrix.det_fin_two])) := by
  intro hfin
  obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (det.isOfFinOrder hfin)
  have hdet : ((det (mkOfDetNeZero !![(0 : ℂ), -2; 2, 2]
      (by norm_num [Matrix.det_fin_two])) : ℂˣ) : ℂ) = 4 := by
    rw [val_det_apply, val_mkOfDetNeZero, Matrix.det_fin_two]
    norm_num
  have hnorm := Complex.norm_eq_one_of_pow_eq_one
    (by rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one] : (_ : ℂ) ^ m = 1) hm.ne'
  rw [hdet] at hnorm
  norm_num at hnorm

end TauCeti

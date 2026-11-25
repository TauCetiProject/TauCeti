/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.UnitaryGroup
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm
import TauCeti.LinearAlgebra.QuadraticForm.Radical
import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.Orbit

/-!
# Transitivity of the matrix special orthogonal group on dot-product level sets

Over a field of characteristic different from two and in dimension at least two, the matrix
special orthogonal group `Matrix.specialOrthogonalGroup ι K` acts transitively on every nonzero
level set of the standard dot product `x ↦ x ⬝ᵥ x`. This is the coordinate translation of
`QuadraticMap.exists_specialOrthogonal_map_eq_of_nondegenerate` via the identification
`TauCeti.standardSpecialOrthogonalGroupEquiv` with the special orthogonal group of
`Matrix.toQuadraticForm' 1`.

Over a linearly ordered field (in particular over `ℝ`), the zero level set consists solely of `0`,
so the nonzero-norm hypothesis drops and `SO(ι, K)` acts transitively on every dot-product level
set, including spheres of any radius. Over `ℝ`, every vector is therefore a radial multiple
`√(x ⬝ᵥ x) • (g *ᵥ u)` of the rotation of any prescribed unit vector `u`.

## Main results

* `TauCeti.exists_specialOrthogonalGroup_mulVec_eq_of_dotProduct_ne_zero`: transitivity on any
  nonzero level set of `x ⬝ᵥ x` over a field of characteristic different from two, for
  `2 ≤ Fintype.card ι`.
* `TauCeti.exists_specialOrthogonalGroup_mulVec_eq_of_dotProduct_eq`: transitivity on every level
  set of `x ⬝ᵥ x` over a linearly ordered field, for `2 ≤ Fintype.card ι`.
* `TauCeti.exists_specialOrthogonalGroup_sqrt_dotProduct_smul_mulVec_eq`: over `ℝ` for
  `2 ≤ Fintype.card ι`, every vector `x` equals `Real.sqrt (x ⬝ᵥ x) • (g *ᵥ u)` for any unit
  vector `u` and some `g ∈ SO(ι, ℝ)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

namespace TauCeti

open Matrix

universe u v

variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- Over a field of characteristic different from two and in dimension at least two, the matrix
special orthogonal group acts transitively on every nonzero level set of the standard dot product
`x ↦ x ⬝ᵥ x`. -/
theorem exists_specialOrthogonalGroup_mulVec_eq_of_dotProduct_ne_zero
    {K : Type u} [Field K] [NeZero (2 : K)] (hcard : 2 ≤ Fintype.card ι)
    {x y : ι → K} (hxy : x ⬝ᵥ x = y ⬝ᵥ y) (hy : y ⬝ᵥ y ≠ 0) :
    ∃ g : Matrix.specialOrthogonalGroup ι K, (g : Matrix ι ι K) *ᵥ x = y := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  let Q := Matrix.toQuadraticForm' (1 : Matrix ι ι K)
  have hQ : Q.Nondegenerate := by
    apply LinearMap.BilinForm.Nondegenerate.toQuadraticMap
      ((Matrix.nondegenerate_toLinearMap₂'_iff).mpr (by
        rw [Matrix.nondegenerate_iff_det_ne_zero]
        simp))
    apply LinearMap.ext₂
    intro u v
    simp only [LinearMap.flip_apply, Matrix.toLinearMap₂'_apply', Matrix.one_mulVec]
    exact dotProduct_comm v u
  have hrank : 2 ≤ Module.finrank K (ι → K) := by
    simpa [Module.finrank_pi] using hcard
  obtain ⟨g, hg⟩ := QuadraticMap.exists_specialOrthogonal_map_eq_of_nondegenerate Q hQ hrank
    (by simpa only [Q, toQuadraticForm'_one_apply] using hxy)
    (by simpa only [Q, toQuadraticForm'_one_apply] using hy)
  refine ⟨standardSpecialOrthogonalGroupEquiv ((isUnit_of_invertible (2 : K)).isSMulRegular K) g,
    ?_⟩
  rw [coe_standardSpecialOrthogonalGroupEquiv_apply, LinearMap.toMatrix'_mulVec]
  exact hg

/-- Over a linearly ordered field (such as `ℝ`) and in dimension at least two, the matrix special
orthogonal group acts transitively on every level set of the standard dot product `x ↦ x ⬝ᵥ x`. -/
theorem exists_specialOrthogonalGroup_mulVec_eq_of_dotProduct_eq
    {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hcard : 2 ≤ Fintype.card ι) {x y : ι → K} (hxy : x ⬝ᵥ x = y ⬝ᵥ y) :
    ∃ g : Matrix.specialOrthogonalGroup ι K, (g : Matrix ι ι K) *ᵥ x = y := by
  by_cases hy : y ⬝ᵥ y = 0
  · have hy0 : y = 0 := dotProduct_self_eq_zero.mp hy
    have hx0 : x = 0 := dotProduct_self_eq_zero.mp (hxy.trans hy)
    exact ⟨1, by simp [hx0, hy0]⟩
  · exact exists_specialOrthogonalGroup_mulVec_eq_of_dotProduct_ne_zero hcard hxy hy

/-- Over `ℝ` and in dimension at least two, every vector `x` is the radial multiple
`Real.sqrt (x ⬝ᵥ x) • (g *ᵥ u)` of the image of any prescribed unit vector `u` under some
`g ∈ SO(ι, ℝ)`. -/
theorem exists_specialOrthogonalGroup_sqrt_dotProduct_smul_mulVec_eq
    (hcard : 2 ≤ Fintype.card ι) {u : ι → ℝ} (hu : u ⬝ᵥ u = 1) (x : ι → ℝ) :
    ∃ g : Matrix.specialOrthogonalGroup ι ℝ,
      Real.sqrt (x ⬝ᵥ x) • ((g : Matrix ι ι ℝ) *ᵥ u) = x := by
  by_cases hx : x = 0
  · exact ⟨1, by simp [hx]⟩
  · have hxx : 0 < x ⬝ᵥ x :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (x i))
        (Ne.symm (mt dotProduct_self_eq_zero.mp hx))
    have hr : Real.sqrt (x ⬝ᵥ x) ≠ 0 := (Real.sqrt_pos.mpr hxx).ne'
    set y : ι → ℝ := (Real.sqrt (x ⬝ᵥ x))⁻¹ • x
    have hyy : y ⬝ᵥ y = 1 := by
      simp only [y, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [← mul_assoc, ← mul_inv, ← sq, Real.sq_sqrt hxx.le, inv_mul_cancel₀ hxx.ne']
    obtain ⟨g, hg⟩ := exists_specialOrthogonalGroup_mulVec_eq_of_dotProduct_eq hcard
      (hu.trans hyy.symm)
    exact ⟨g, by rw [hg, smul_smul, mul_inv_cancel₀ hr, one_smul]⟩

end TauCeti

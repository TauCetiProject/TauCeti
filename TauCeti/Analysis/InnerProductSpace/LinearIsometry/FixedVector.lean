/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import TauCeti.Analysis.InnerProductSpace.Adjoint

/-!
# Fixed vectors of linear isometries

Let `f` be a linear isometry of a real inner product space `V` of dimension `n`. Its inverse is
its adjoint, so `f - 1 = f ∘ (1 - f)†` and `det (f - 1) = det f * det (1 - f)`. Since
`det (1 - f) = (-1) ^ n * det (f - 1)`, if `det f ≠ (-1) ^ n` then `det (f - 1) = 0`, and `f`
fixes a nonzero vector: an orientation-preserving isometry of an odd-dimensional space, or an
orientation-reversing isometry of an even-dimensional space, has a nonzero fixed vector.

If instead `det f = (-1) ^ n` and `f` fixes a nonzero vector `u`, composing `f` with the
reflection in the hyperplane `uᗮ` gives an isometry of determinant `-(-1) ^ n`. Its nonzero fixed
vectors are orthogonal to `u` and fixed by `f`. This is the linear algebra of Synge's theorem:
the holonomy of a closed geodesic fixes its velocity, and a second fixed vector orthogonal to it
is the initial value of a closed parallel normal field.

## Main results

* `LinearIsometryEquiv.det_sub_one_eq_det_mul_det_one_sub`: `det (f - 1) = det f * det (1 - f)`.
* `LinearIsometryEquiv.det_sub_one_eq_zero_of_det_ne`: if `det f ≠ (-1) ^ n`, then
  `det (f - 1) = 0`.
* `LinearIsometryEquiv.exists_ne_zero_apply_eq_self_of_det_ne`: if `det f ≠ (-1) ^ n`, then `f`
  fixes a nonzero vector.
* `LinearIsometryEquiv.exists_ne_zero_inner_eq_zero_apply_eq_self`: if `det f = (-1) ^ n` and `f`
  fixes a nonzero vector `u`, then `f` fixes a nonzero vector orthogonal to `u`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 9, Lemma 3.7 and the proof
  of Synge's theorem.
-/

public section

open Module

namespace LinearIsometryEquiv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For a linear isometry `f` of a real inner product space, `det (f - 1) = det f * det (1 - f)`.
In infinite dimension both sides are `1`. -/
theorem det_sub_one_eq_det_mul_det_one_sub (f : V ≃ₗᵢ[ℝ] V) :
    (f.toLinearMap - 1).det = f.toLinearMap.det * (1 - f.toLinearMap).det := by
  by_cases hV : FiniteDimensional ℝ V
  · have hadj : LinearMap.adjoint (1 - f.toLinearMap) = 1 - f.symm.toLinearMap := by
      simp [adjoint_toLinearMap_eq_symm]
    have h : f.toLinearMap - 1 = f.toLinearMap ∘ₗ LinearMap.adjoint (1 - f.toLinearMap) := by
      rw [hadj]
      ext x
      simp
    rw [h, LinearMap.det_comp, LinearMap.det_adjoint, star_trivial]
  · simp [LinearMap.det_eq_one_of_not_module_finite hV]

/-- A linear isometry `f` of an `n`-dimensional real inner product space with
`det f ≠ (-1) ^ n` satisfies `det (f - 1) = 0`. -/
theorem det_sub_one_eq_zero_of_det_ne {f : V ≃ₗᵢ[ℝ] V}
    (hf : f.toLinearMap.det ≠ (-1) ^ finrank ℝ V) : (f.toLinearMap - 1).det = 0 := by
  have h := f.det_sub_one_eq_det_mul_det_one_sub
  have hneg : f.toLinearMap - 1 = (-1 : ℝ) • (1 - f.toLinearMap) := by
    rw [neg_one_smul, neg_sub]
  rw [hneg, LinearMap.det_smul] at h ⊢
  have h2 : (1 - f.toLinearMap).det * ((-1) ^ finrank ℝ V - f.toLinearMap.det) = 0 := by
    linear_combination h
  rw [(mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hf.symm), mul_zero]

/-- **Fixed vectors of linear isometries.** A linear isometry of an `n`-dimensional real inner
product space whose determinant is not `(-1) ^ n` fixes a nonzero vector. -/
theorem exists_ne_zero_apply_eq_self_of_det_ne {f : V ≃ₗᵢ[ℝ] V}
    (hf : f.toLinearMap.det ≠ (-1) ^ finrank ℝ V) : ∃ v ≠ 0, f v = v := by
  have h := det_sub_one_eq_zero_of_det_ne hf
  have : FiniteDimensional ℝ V := by
    by_contra hV
    simp [LinearMap.det_eq_one_of_not_module_finite hV] at h
  obtain ⟨v, hv, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h)
  exact ⟨v, hv0, sub_eq_zero.mp (by simpa using hv)⟩

/-- **A second fixed vector.** A linear isometry `f` of an `n`-dimensional real inner product
space with `det f = (-1) ^ n` which fixes a nonzero vector `u` also fixes a nonzero vector
orthogonal to `u`. -/
theorem exists_ne_zero_inner_eq_zero_apply_eq_self [FiniteDimensional ℝ V] {f : V ≃ₗᵢ[ℝ] V}
    {u : V} (hu : u ≠ 0) (hfu : f u = u) (hf : f.toLinearMap.det = (-1) ^ finrank ℝ V) :
    ∃ v ≠ 0, inner ℝ v u = 0 ∧ f v = v := by
  set r : V ≃ₗᵢ[ℝ] V := (ℝ ∙ u)ᗮ.reflection
  have hdet : (r.trans f).toLinearMap.det ≠ (-1) ^ finrank ℝ V := by
    rw [toLinearEquiv_trans, LinearEquiv.coe_trans, LinearMap.det_comp, hf,
      Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hu]
    simp [neg_eq_self]
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_apply_eq_self_of_det_ne hdet
  rw [trans_apply] at hv
  have hinner : inner ℝ v u = 0 := by
    have h := r.inner_map_map v u
    rw [Submodule.reflection_orthogonalComplement_singleton_eq_neg, ← f.inner_map_map,
      hv, map_neg, hfu, inner_neg_right] at h
    linarith
  refine ⟨v, hv0, hinner, ?_⟩
  rwa [Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hinner)] at hv

end LinearIsometryEquiv

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.Rigidity
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic

/-!
# Diagonal sums of rank-one maps

For families `v : ι → E`, `w : ι → F` and real coefficients `x : ι → ℝ`, the diagonal sum
`LinearMap.diagonalSum 𝕜 v w x = ∑ᵢ xᵢ wᵢ ⊗ vᵢ` sends `y` to `∑ᵢ xᵢ ⟪vᵢ, y⟫ wᵢ`. For orthonormal
families and a nonincreasing nonnegative tuple `x`, it is the map with singular system
`(vᵢ, wᵢ, xᵢ)`, and the singular value decomposition writes every map between finite-dimensional
spaces in this form (`LinearMap.exists_orthonormal_eq_sum_singularValues_smul_rankOne`).

This file records how diagonal sums depend on their data: they are real-linear in the
coefficients; permuting the coefficients or changing the sign of one of them permutes the
vectors or changes the sign of one vector; and over two pairs of orthonormal families, diagonal
sums with the same coefficients lie in the same two-sided unitary orbit
(`LinearMap.diagonalSum_mem_twoSidedUnitaryOrbit`). These are the symmetries behind Fan dominance
and the gauge representation of unitarily invariant seminorms.
-/

public section

open Module InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section DiagonalSum

variable {ι : Type*} [Fintype ι]

variable (𝕜) in
/-- The map `∑ᵢ xᵢ wᵢ ⊗ vᵢ`, sending `y` to `∑ᵢ xᵢ ⟪vᵢ, y⟫ wᵢ`. For orthonormal families `(vᵢ)`
and `(wᵢ)` and a nonnegative tuple `x`, this is the map with singular system `(vᵢ, wᵢ, xᵢ)`. -/
noncomputable def diagonalSum (v : ι → E) (w : ι → F) (x : ι → ℝ) : E →ₗ[𝕜] F :=
  ∑ i, (x i : 𝕜) • (rankOne 𝕜 (w i) (v i)).toLinearMap

theorem diagonalSum_def (v : ι → E) (w : ι → F) (x : ι → ℝ) :
    diagonalSum 𝕜 v w x = ∑ i, (x i : 𝕜) • (rankOne 𝕜 (w i) (v i)).toLinearMap :=
  (rfl)

theorem diagonalSum_apply (v : ι → E) (w : ι → F) (x : ι → ℝ) (y : E) :
    diagonalSum 𝕜 v w x y = ∑ i, (x i : 𝕜) • ⟪v i, y⟫ • w i := by
  simp [diagonalSum]

/-- Unitaries on either side act on the vectors of a diagonal sum. -/
theorem linearIsometryEquiv_comp_diagonalSum_comp (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E)
    (v : ι → E) (w : ι → F) (x : ι → ℝ) :
    (U : F →ₗ[𝕜] F) ∘ₗ diagonalSum 𝕜 v w x ∘ₗ (V : E →ₗ[𝕜] E) =
      diagonalSum 𝕜 (V.symm ∘ v) (U ∘ w) x := by
  ext y
  simp [diagonalSum_apply, LinearIsometryEquiv.inner_map_eq_flip]

theorem diagonalSum_add_smul (v : ι → E) (w : ι → F) (x y : ι → ℝ) (a b : ℝ) :
    diagonalSum 𝕜 v w (a • x + b • y) =
      (a : 𝕜) • diagonalSum 𝕜 v w x + (b : 𝕜) • diagonalSum 𝕜 v w y := by
  simp only [diagonalSum, Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← add_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp

theorem diagonalSum_add (v : ι → E) (w : ι → F) (x y : ι → ℝ) :
    diagonalSum 𝕜 v w (x + y) = diagonalSum 𝕜 v w x + diagonalSum 𝕜 v w y := by
  simpa using diagonalSum_add_smul (𝕜 := 𝕜) v w x y 1 1

theorem diagonalSum_smul (v : ι → E) (w : ι → F) (a : ℝ) (x : ι → ℝ) :
    diagonalSum 𝕜 v w (a • x) = (a : 𝕜) • diagonalSum 𝕜 v w x := by
  simpa using diagonalSum_add_smul (𝕜 := 𝕜) v w x 0 a 0

theorem diagonalSum_neg (v : ι → E) (w : ι → F) (x : ι → ℝ) :
    diagonalSum 𝕜 v w (-x) = -diagonalSum 𝕜 v w x := by
  simpa using diagonalSum_smul (𝕜 := 𝕜) v w (-1) x

/-- Over an orthonormal family `(wᵢ)`, `‖(∑ᵢ xᵢ wᵢ ⊗ vᵢ) y‖² = ∑ᵢ xᵢ² ‖⟪vᵢ, y⟫‖²`. -/
theorem norm_diagonalSum_apply_sq (v : ι → E) {w : ι → F} (hw : Orthonormal 𝕜 w)
    (x : ι → ℝ) (y : E) :
    ‖diagonalSum 𝕜 v w x y‖ ^ 2 = ∑ i, x i ^ 2 * ‖⟪v i, y⟫‖ ^ 2 := by
  set c : ι → 𝕜 := fun i ↦ (x i : 𝕜) * ⟪v i, y⟫
  have hD : diagonalSum 𝕜 v w x y = ∑ i, c i • w i := by
    simp [c, diagonalSum_apply, smul_smul]
  have h := hw.inner_sum c c Finset.univ
  simp only [RCLike.conj_mul, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖∑ i, c i • w i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by exact_mod_cast h
  rw [hD, h']
  simp [c, norm_mul, mul_pow]

/-- Permuting the coefficients of a diagonal sum permutes its vectors. -/
theorem diagonalSum_comp_perm (v : ι → E) (w : ι → F) (x : ι → ℝ) (π : Equiv.Perm ι) :
    diagonalSum 𝕜 v w (x ∘ π) = diagonalSum 𝕜 (v ∘ π.symm) (w ∘ π.symm) x := by
  simp only [diagonalSum, Function.comp_apply]
  exact (π.symm.sum_comp fun i ↦ (x (π i) : 𝕜) • (rankOne 𝕜 (w i) (v i)).toLinearMap).symm.trans
    (by simp)

/-- Changing the sign of one coefficient of a diagonal sum changes the sign of one vector. -/
theorem diagonalSum_update_neg [DecidableEq ι] (v : ι → E) (w : ι → F) (x : ι → ℝ)
    (i : ι) :
    diagonalSum 𝕜 v w (Function.update x i (-x i)) =
      diagonalSum 𝕜 v (Function.update w i (-w i)) x := by
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [Function.update_of_ne hj]

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- Diagonal sums over two pairs of orthonormal families with the same coefficients are related by
unitaries of the source and of the target. -/
theorem diagonalSum_mem_twoSidedUnitaryOrbit {v v' : ι → E} {w w' : ι → F}
    (hv : Orthonormal 𝕜 v) (hv' : Orthonormal 𝕜 v') (hw : Orthonormal 𝕜 w)
    (hw' : Orthonormal 𝕜 w') (x : ι → ℝ) :
    diagonalSum 𝕜 v' w' x ∈ (diagonalSum 𝕜 v w x).twoSidedUnitaryOrbit := by
  classical
  obtain ⟨P, hP⟩ := TauCeti.exists_linearIsometryEquiv_of_inner_eq (v := v) (w := v') fun i j ↦ by
    rw [orthonormal_iff_ite.mp hv, orthonormal_iff_ite.mp hv']
  obtain ⟨Q, hQ⟩ := TauCeti.exists_linearIsometryEquiv_of_inner_eq (v := w) (w := w') fun i j ↦ by
    rw [orthonormal_iff_ite.mp hw, orthonormal_iff_ite.mp hw']
  refine mem_twoSidedUnitaryOrbit.mpr ⟨Q, P.symm, ?_⟩
  rw [linearIsometryEquiv_comp_diagonalSum_comp, LinearIsometryEquiv.symm_symm]
  congr 1 <;> ext i <;> simp [hP, hQ]

end DiagonalSum

end LinearMap

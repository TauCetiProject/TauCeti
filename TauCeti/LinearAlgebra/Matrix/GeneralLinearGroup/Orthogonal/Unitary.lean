/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Orthogonal.Basic

/-!
# The unitary orthogonal matrices are real

Over `𝕜 = ℝ` or `ℂ`, a matrix that is both orthogonal (`Aᵀ A = 1`) and unitary (`Aᴴ A = 1`) has
real entries, since `Aᵀ = A⁻¹ = Aᴴ`. This file identifies the unitary elements of
`TauCeti.GLOrthogonal n 𝕜` and `TauCeti.GLSpecialOrthogonal n 𝕜` with the images of the real
orthogonal and special orthogonal groups under the change of scalars
`Matrix.GeneralLinearGroup.map (algebraMap ℝ 𝕜)`. Over `ℂ` these are `O(n, ℂ) ∩ U(n) = O(n)` and
`SO(n, ℂ) ∩ U(n) = SO(n)`.

## Main results

* `TauCeti.GLOrthogonal.inf_unitarySubgroup_eq_map_real`: the unitary elements of `O(n, 𝕜)` are
  the real orthogonal matrices.
* `TauCeti.GLSpecialOrthogonal.inf_unitarySubgroup_eq_map_real`: the unitary elements of
  `SO(n, 𝕜)` are the real special orthogonal matrices.
-/

public section

open Matrix Matrix.GeneralLinearGroup

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace GLOrthogonal

variable (n) (𝕜 : Type*) [RCLike 𝕜]

/-- **`O(n, 𝕜) ∩ U(n) = O(n)`.** The unitary elements of the orthogonal group over `𝕜 = ℝ` or `ℂ`
are exactly the images of the real orthogonal matrices. -/
theorem inf_unitarySubgroup_eq_map_real :
    GLOrthogonal n 𝕜 ⊓ unitarySubgroup (GL n 𝕜) =
      (GLOrthogonal n ℝ).map (Matrix.GeneralLinearGroup.map (algebraMap ℝ 𝕜)) := by
  have hcoe (B : GL n ℝ) : ((Matrix.GeneralLinearGroup.map (algebraMap ℝ 𝕜) B : GL n 𝕜) :
      Matrix n n 𝕜) = (B : Matrix n n ℝ).map (algebraMap ℝ 𝕜) := by
    ext
    simp
  apply le_antisymm
  · rintro A ⟨hAO, hAU⟩
    have hreal := (mem_unitarySubgroup_iff_map_star_eq hAO).mp hAU
    -- The entries of `A` are real, so `A` is the image of its matrix of real parts.
    set B : Matrix n n ℝ := (A : Matrix n n 𝕜).map RCLike.re
    have hB : B.map (algebraMap ℝ 𝕜) = A := by
      ext i j
      have h := congrFun (congrFun hreal i) j
      simp only [Matrix.map_apply, RCLike.star_def] at h
      simpa [B, RCLike.algebraMap_eq_ofReal] using RCLike.conj_eq_iff_re.mp h
    have hBB : Bᵀ * B = 1 := Matrix.map_injective (algebraMap ℝ 𝕜).injective <| by
      beta_reduce
      rw [Matrix.map_mul, transpose_map, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      exact mem_iff.mp hAO
    refine ⟨⟨B, Bᵀ, mul_eq_one_comm.mp hBB, hBB⟩, mem_iff.mpr hBB, Units.ext ?_⟩
    rw [hcoe]
    exact hB
  · rintro _ ⟨B, hB, rfl⟩
    refine ⟨map_mem _ hB, (mem_unitarySubgroup_iff_map_star_eq (map_mem _ hB)).mpr ?_⟩
    rw [hcoe, Matrix.map_map]
    congr 1
    ext x
    simp [RCLike.algebraMap_eq_ofReal]

end GLOrthogonal

namespace GLSpecialOrthogonal

variable (n) (𝕜 : Type*) [RCLike 𝕜]

/-- **`SO(n, 𝕜) ∩ U(n) = SO(n)`.** The unitary elements of the special orthogonal group over
`𝕜 = ℝ` or `ℂ` are exactly the images of the real special orthogonal matrices. -/
theorem inf_unitarySubgroup_eq_map_real :
    GLSpecialOrthogonal n 𝕜 ⊓ unitarySubgroup (GL n 𝕜) =
      (GLSpecialOrthogonal n ℝ).map (Matrix.GeneralLinearGroup.map (algebraMap ℝ 𝕜)) := by
  have hdet (B : GL n ℝ) : ((Matrix.GeneralLinearGroup.map (algebraMap ℝ 𝕜) B : GL n 𝕜) :
      Matrix n n 𝕜).det = algebraMap ℝ 𝕜 (B : Matrix n n ℝ).det := by
    rw [RingHom.map_det]
    congr 1
  ext A
  constructor
  · rintro ⟨hAS, hAU⟩
    obtain ⟨B, hBO, rfl⟩ : A ∈ (GLOrthogonal n ℝ).map (Matrix.GeneralLinearGroup.map _) := by
      rw [← GLOrthogonal.inf_unitarySubgroup_eq_map_real]
      exact ⟨le_GLOrthogonal hAS, hAU⟩
    refine ⟨B, mem_iff.mpr ⟨hBO, (algebraMap ℝ 𝕜).injective ?_⟩, rfl⟩
    rw [← hdet, (mem_iff.mp hAS).2, map_one]
  · rintro ⟨B, hB, rfl⟩
    have hBO : Matrix.GeneralLinearGroup.map (algebraMap ℝ 𝕜) B ∈
        GLOrthogonal n 𝕜 ⊓ unitarySubgroup (GL n 𝕜) := by
      rw [GLOrthogonal.inf_unitarySubgroup_eq_map_real]
      exact ⟨B, le_GLOrthogonal hB, rfl⟩
    exact ⟨map_mem _ hB, hBO.2⟩

end GLSpecialOrthogonal

end TauCeti

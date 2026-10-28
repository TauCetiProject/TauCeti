/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.NormDet

/-!
# Jacobians in coarea coordinates

An invertible linear change of coordinates into a Euclidean product identifies the fibers of
its first coordinate with the second factor. The coarea Jacobian of the first coordinate times
the volume Jacobian of the inverse chart equals the area Jacobian of that fiber parametrization.
This identity is the linear algebra needed to compare change of variables with the area formula
on fibers in the coarea formula; see Evans and Gariepy, *Measure Theory and Fine Properties of
Functions*, revised edition, §3.4.2.
-/

public section

open scoped RealInnerProductSpace

namespace ContinuousLinearEquiv

variable {E F K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [FiniteDimensional ℝ K]

/-- The Jacobian identity for coarea coordinates: the coarea Jacobian of the first coordinate,
multiplied by the volume Jacobian of the inverse chart, is the area Jacobian along the fibers. -/
theorem normDet_adjoint_fst_mul_normDet_symm
    (e : E ≃L[ℝ] WithLp 2 (F × K)) :
    ((WithLp.fstₗ 2 ℝ F K) ∘ₗ e.toLinearMap).adjoint.normDet * e.symm.toLinearMap.normDet =
      (e.symm.toLinearMap ∘ₗ (WithLp.linearEquiv 2 ℝ (F × K)).symm.toLinearMap ∘ₗ
        LinearMap.inr ℝ F K).normDet := by
  classical
  let P := WithLp.linearEquiv 2 ℝ (F × K)
  let L := (WithLp.fstₗ 2 ℝ F K) ∘ₗ e.toLinearMap
  let B := e.symm.toLinearMap ∘ₗ P.symm.toLinearMap ∘ₗ LinearMap.inr ℝ F K
  let C := L.adjoint.coprod B ∘ₗ P.toLinearMap
  have hLB : L ∘ₗ B = 0 := by ext; simp [L, B, P]
  have horth (x : F) (y : K) : ⟪L.adjoint x, B y⟫ = 0 := by
    rw [LinearMap.adjoint_inner_left]
    have := LinearMap.congr_fun hLB y
    simpa using congrArg (fun z => ⟪x, z⟫) this
  have horth' (x : F) (y : K) : ⟪B y, L.adjoint x⟫ = 0 := by
    rw [real_inner_comm, horth]
  have hLL (u v : F) : ⟪L (L.adjoint u), v⟫ = ⟪L.adjoint u, L.adjoint v⟫ := by
    rw [LinearMap.adjoint_inner_right]
  -- The two columns of `C` have orthogonal ranges, so its Gram operator is block diagonal.
  have hgram : C.adjoint ∘ₗ C =
      P.symm.conj ((L ∘ₗ L.adjoint).prodMap (B.adjoint ∘ₗ B)) := by
    refine LinearMap.ext fun x => ext_inner_right ℝ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    simp only [C, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.coprod_apply,
      LinearEquiv.coe_coe, LinearMap.prodMap_apply, P, WithLp.coe_linearEquiv,
      WithLp.coe_symm_linearEquiv, WithLp.prod_inner_apply,
      inner_add_left, inner_add_right]
    simp only [horth, horth', add_zero, zero_add, LinearMap.adjoint_inner_left,
      LinearEquiv.symm_symm, WithLp.coe_linearEquiv]
    rw [hLL, ← LinearMap.adjoint_inner_left]
  have hCsq : C.normDet ^ 2 = L.adjoint.normDet ^ 2 * B.normDet ^ 2 := by
    have hC := C.normDet_sq
    have hL := L.adjoint.normDet_sq
    have hB := B.normDet_sq
    simp only [RCLike.ofReal_real_eq_id, id_eq, LinearMap.adjoint_adjoint] at hC hL hB
    rw [hC, hgram, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj,
      LinearMap.det_prodMap, ← hL, ← hB]
  have hC : C.normDet = L.adjoint.normDet * B.normDet :=
    (sq_eq_sq₀ C.normDet_nonneg (mul_nonneg L.adjoint.normDet_nonneg B.normDet_nonneg)).mp
      (by simpa [mul_pow] using hCsq)
  -- In chart coordinates, `e ∘ C` is lower triangular, with identity on the fiber block.
  let bF := stdOrthonormalBasis ℝ F
  let bK := stdOrthonormalBasis ℝ K
  let D := (P.toLinearMap ∘ₗ e.toLinearMap ∘ₗ L.adjoint)
  let T := (P.toLinearMap ∘ₗ e.toLinearMap ∘ₗ C) ∘ₗ P.symm.toLinearMap
  have hmatrix : T.toMatrix (bF.toBasis.prod bK.toBasis) (bF.toBasis.prod bK.toBasis) =
      Matrix.fromBlocks ((L ∘ₗ L.adjoint).toMatrix bF.toBasis bF.toBasis) 0
        ((LinearMap.snd ℝ F K ∘ₗ D).toMatrix bF.toBasis bK.toBasis) 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [LinearMap.toMatrix_apply, T, D, L, B, C, P, Matrix.one_apply]
  have hdet : (e.toLinearMap ∘ₗ C).det = (L ∘ₗ L.adjoint).det := by
    have hT : e.toLinearMap ∘ₗ C = P.symm.conj T := by ext; simp [T, P]
    rw [hT, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj,
      ← LinearMap.det_toMatrix (bF.toBasis.prod bK.toBasis), hmatrix,
      Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one, LinearMap.det_toMatrix]
  have heC : (e.toLinearMap ∘ₗ C).normDet = L.adjoint.normDet ^ 2 := by
    have hL := L.adjoint.normDet_sq
    simp only [RCLike.ofReal_real_eq_id, id_eq, LinearMap.adjoint_adjoint] at hL
    rw [LinearMap.normDet_eq_abs_det, hdet, ← hL, abs_of_nonneg (sq_nonneg _)]
  have hmul := LinearMap.normDet_comp_of_finrank_eq C e.toLinearMap e.toLinearEquiv.finrank_eq.symm
  have hinv := LinearMap.normDet_comp_of_finrank_eq e.toLinearMap e.symm.toLinearMap
    e.toLinearEquiv.finrank_eq
  have hsurj : Function.Surjective L := by
    intro y
    exact ⟨e.symm (WithLp.toLp 2 (y, 0)), by simp [L]⟩
  have hpos : 0 < L.adjoint.normDet := lt_of_le_of_ne L.adjoint.normDet_nonneg
    (Ne.symm fun h => (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp h)
      (by
        rw [← LinearMap.orthogonal_range, LinearMap.range_eq_top.mpr hsurj,
          Submodule.top_orthogonal_eq_bot]))
  have hcomp : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id := by ext; simp
  rw [hcomp, LinearMap.normDet_id] at hinv
  rw [heC, hC] at hmul
  have hcancel : L.adjoint.normDet = e.toLinearMap.normDet * B.normDet := by
    apply mul_left_cancel₀ hpos.ne'
    nlinarith [hmul]
  have hresult : L.adjoint.normDet * e.symm.toLinearMap.normDet = B.normDet := by
    rw [hcancel]
    calc
      e.toLinearMap.normDet * B.normDet * e.symm.toLinearMap.normDet =
          (e.symm.toLinearMap.normDet * e.toLinearMap.normDet) * B.normDet := by ring
      _ = B.normDet := by rw [← hinv, one_mul]
  exact hresult

end ContinuousLinearEquiv

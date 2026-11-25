/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearDistortion.HilbertSchmidt
public import TauCeti.Analysis.InnerProductSpace.SingularValues.Planar
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.Trace.Free
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Examples of linear distortion

Two examples of the outer, inner and Hilbert–Schmidt distortions `q_O`, `q_I`, `q_S` of a linear
map (`Orientation.outerDistortion`, `Orientation.innerDistortion`,
`Orientation.hilbertSchmidtDistortion`), from the examples of Layer 1 of the QuasiregularMaps
roadmap:

* a positive multiple `c U` of an orientation-preserving isometric isomorphism (for instance a
  rotation) has `q_O = q_I = q_S = 1`
  (`TauCeti.LinearDistortionExamples.outerDistortion_smul_linearIsometryEquiv` and its two
  companions);
* the shear `[[1, 1], [0, 1]]` of an oriented inner product plane has squared singular values
  `(3 ± √5) / 2` (`TauCeti.LinearDistortionExamples.sq_singularValues_shear`), so
  `q_O = q_I = (3 + √5) / 2` (`TauCeti.LinearDistortionExamples.distortion_shear`).
-/

public section

noncomputable section

open Module Matrix LinearMap
open scoped ENNReal

namespace TauCeti.LinearDistortionExamples

section Isometry

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {n : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = n)]
  (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))

omit [FiniteDimensional ℝ W] in
/-- A positive multiple `c U` of an orientation-preserving isometric isomorphism has outer
distortion `1`. -/
theorem outerDistortion_smul_linearIsometryEquiv {c : ℝ} (hc : 0 < c) (U : V ≃ₗᵢ[ℝ] W)
    (hU : oV.orientedJacobian oW (U : V →ₗ[ℝ] W) = 1) :
    oV.outerDistortion oW (c • (U : V →ₗ[ℝ] W)) = 1 := by
  rw [oV.outerDistortion_smul oW (pow_pos hc n), oV.outerDistortion_linearIsometryEquiv oW U hU]

/-- A positive multiple `c U` of an orientation-preserving isometric isomorphism has inner
distortion `1`. -/
theorem innerDistortion_smul_linearIsometryEquiv {c : ℝ} (hc : 0 < c) (U : V ≃ₗᵢ[ℝ] W)
    (hU : oV.orientedJacobian oW (U : V →ₗ[ℝ] W) = 1) :
    oV.innerDistortion oW (c • (U : V →ₗ[ℝ] W)) = 1 := by
  rw [oV.innerDistortion_smul oW (pow_pos hc n), oV.innerDistortion_linearIsometryEquiv oW U hU]

/-- A positive multiple `c U` of an orientation-preserving isometric isomorphism has
Hilbert–Schmidt distortion `1`, since `1 ≤ q_S ≤ q_O = 1`. -/
theorem hilbertSchmidtDistortion_smul_linearIsometryEquiv {c : ℝ} (hc : 0 < c)
    (U : V ≃ₗᵢ[ℝ] W) (hU : oV.orientedJacobian oW (U : V →ₗ[ℝ] W) = 1) :
    oV.hilbertSchmidtDistortion oW (c • (U : V →ₗ[ℝ] W)) = 1 := by
  rw [oV.hilbertSchmidtDistortion_smul oW (pow_pos hc n)]
  refine le_antisymm ?_ (oV.one_le_hilbertSchmidtDistortion oW (by rw [hU]; exact one_pos))
  exact (oV.hilbertSchmidtDistortion_le_outerDistortion oW _).trans_eq
    (oV.outerDistortion_linearIsometryEquiv oW U hU)

end Isometry

section Shear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (finrank ℝ E = 2)] (e : OrthonormalBasis (Fin 2) ℝ E)

/-- The shear `[[1, 1], [0, 1]]` in an orthonormal basis of a plane has squared singular values
`σ₀² = (3 + √5) / 2` and `σ₁² = (3 - √5) / 2`: its Gram operator has trace `3` and
determinant `1`. -/
theorem sq_singularValues_shear :
    (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1]).singularValues 0 ^ 2 = (3 + √5) / 2 ∧
      (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1]).singularValues 1 ^ 2 = (3 - √5) / 2 := by
  set A := toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1]
  have hE : finrank ℝ E = 2 := Fact.out
  have hA0 : A (e 0) = e 0 := by
    rw [← e.coe_toBasis, toLin_self]
    simp [Fin.sum_univ_two]
  have hA1 : A (e 1) = e 0 + e 1 := by
    rw [← e.coe_toBasis, toLin_self]
    simp [Fin.sum_univ_two]
  have htr : RCLike.re (trace ℝ E (adjoint A ∘ₗ A)) = 3 := by
    rw [A.trace_adjoint_comp_self_eq_sum_norm_apply_sq e, Fin.sum_univ_two, hA0, hA1,
      norm_add_sq_real, e.orthonormal.1 0, e.orthonormal.1 1,
      e.orthonormal.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)]
    norm_num
  have hdet : RCLike.re (adjoint A ∘ₗ A).det = 1 := by
    rw [det_comp, det_adjoint, det_toLin, det_fin_two_of]
    norm_num
  have h5 : (3 : ℝ) ^ 2 - 4 * 1 = 5 := by norm_num
  refine ⟨?_, ?_⟩
  · rw [A.sq_singularValues_zero_of_finrank_eq_two hE, htr, hdet, h5]
  · rw [A.sq_singularValues_one_of_finrank_eq_two hE, htr, hdet, h5]

/-- **The shear `[[1, 1], [0, 1]]`** of an oriented inner product plane has
`q_O = q_I = (3 + √5) / 2`. -/
theorem distortion_shear :
    e.toBasis.orientation.outerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1]) = ENNReal.ofReal ((3 + √5) / 2) ∧
      e.toBasis.orientation.innerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1]) = (3 + √5) / 2 := by
  have hJ : e.toBasis.orientation.orientedJacobian e.toBasis.orientation
      (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1]) = 1 := by
    rw [Orientation.orientedJacobian_self, det_toLin, det_fin_two_of]
    norm_num
  obtain ⟨h0, h1⟩ := sq_singularValues_shear e
  refine ⟨?_, ?_⟩
  · rw [Orientation.outerDistortion_of_pos _ _ (by rw [hJ]; exact one_pos), hJ,
      norm_toContinuousLinearMap_eq_singularValues_zero, h0, div_one]
  · have h5 : √5 < 3 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hsq : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    rw [Orientation.innerDistortion_of_pos _ _ (by rw [hJ]; exact one_pos), hJ,
      minimalStretch_def, finrank_eq_card_basis e.toBasis, Fintype.card_fin,
      show 2 - 1 = 1 from rfl, h1,
      div_eq_div_iff (by linarith : (0 : ℝ) < (3 - √5) / 2).ne' two_ne_zero]
    nlinarith

end Shear

end TauCeti.LinearDistortionExamples

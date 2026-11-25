/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearDistortion
import TauCeti.Analysis.InnerProductSpace.SingularValues.Planar
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Examples of linear distortion

Worked examples of the outer and inner distortions `q_O`, `q_I` of a linear map
(`Orientation.outerDistortion`, `Orientation.innerDistortion`). The shear `[[1, 1], [0, 1]]` of an
oriented inner product plane has squared singular values `(3 ± √5) / 2`
(`Matrix.sq_singularValues_toLin_shear_fin_two`) and oriented Jacobian `1`
(`TauCeti.LinearDistortionExamples.orientedJacobian_shear`), so `q_O = q_I = (3 + √5) / 2`
(`TauCeti.LinearDistortionExamples.outerDistortion_shear`,
`TauCeti.LinearDistortionExamples.innerDistortion_shear`).

A positive multiple `c U` of an orientation-preserving isometric isomorphism has
`q_O = q_I = q_S = 1`: this is `Orientation.outerDistortion_smul_linearIsometry`,
`Orientation.innerDistortion_smul_linearIsometryEquiv` and
`Orientation.hilbertSchmidtDistortion_smul_linearIsometry`.
-/

public section

noncomputable section

open Module Matrix LinearMap
open scoped ENNReal

namespace TauCeti.LinearDistortionExamples

section Shear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (e : OrthonormalBasis (Fin 2) ℝ E)

omit [FiniteDimensional ℝ E] in
/-- The shear `[[1, 1], [0, 1]]` of an oriented inner product plane has oriented Jacobian `1`. -/
theorem orientedJacobian_shear [Fact (finrank ℝ E = 2)] :
    e.toBasis.orientation.orientedJacobian e.toBasis.orientation
      (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1]) = 1 := by
  rw [Orientation.orientedJacobian_self, det_toLin, det_fin_two_of]
  norm_num

/-- **The shear `[[1, 1], [0, 1]]`** of an oriented inner product plane has
`q_O = (3 + √5) / 2`. -/
theorem outerDistortion_shear [Fact (finrank ℝ E = 2)] :
    e.toBasis.orientation.outerDistortion e.toBasis.orientation
      (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1]) = ENNReal.ofReal ((3 + √5) / 2) := by
  have hJ := orientedJacobian_shear e
  rw [Orientation.outerDistortion_of_pos _ _ (by rw [hJ]; exact one_pos), hJ,
    norm_toContinuousLinearMap_eq_singularValues_zero,
    (sq_singularValues_toLin_shear_fin_two e).1, div_one]

/-- **The shear `[[1, 1], [0, 1]]`** of an oriented inner product plane has
`q_I = 2 / (3 - √5) = (3 + √5) / 2`. -/
theorem innerDistortion_shear [Fact (finrank ℝ E = 2)] :
    e.toBasis.orientation.innerDistortion e.toBasis.orientation
      (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1]) = (3 + √5) / 2 := by
  have hJ := orientedJacobian_shear e
  have h5 : √5 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hsq : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hE : finrank ℝ E = 2 := Fact.out
  rw [Orientation.innerDistortion_of_pos _ _ (by rw [hJ]; exact one_pos), hJ]
  simp only [minimalStretch_def, hE, Nat.reduceSub]
  rw [(sq_singularValues_toLin_shear_fin_two e).2,
    div_eq_div_iff (by linarith : (0 : ℝ) < (3 - √5) / 2).ne' two_ne_zero]
  nlinarith

end Shear

end TauCeti.LinearDistortionExamples

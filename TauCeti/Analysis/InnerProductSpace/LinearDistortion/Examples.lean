/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearDistortion
import TauCeti.Analysis.InnerProductSpace.LinearDistortion.Comparison
import TauCeti.Analysis.InnerProductSpace.SingularValues.Planar
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Examples of linear distortion

Worked examples of the outer and inner distortions `q_O`, `q_I` of a linear map
(`Orientation.outerDistortion`, `Orientation.innerDistortion`). The shear `[[1, t], [0, 1]]`, in an
orthonormal basis of an inner product plane with any orientation, has squared singular values
`(2 + t² ± |t| √(t² + 4)) / 2`
(`Matrix.sq_singularValues_toLin_shear_fin_two`) and oriented Jacobian `1`
(`TauCeti.LinearDistortionExamples.orientedJacobian_shear`), so
`q_O = q_I = (2 + t² + |t| √(t² + 4)) / 2`, which is `(3 + √5) / 2` for `t = 1`
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
  (o : Orientation ℝ E (Fin 2)) (e : OrthonormalBasis (Fin 2) ℝ E)

omit [FiniteDimensional ℝ E] in
/-- The shear `[[1, t], [0, 1]]` (in an orthonormal basis) of an inner product plane has oriented
Jacobian `1` for any orientation of the plane. -/
theorem orientedJacobian_shear [Fact (finrank ℝ E = 2)] (t : ℝ) :
    o.orientedJacobian o (toLin e.toBasis e.toBasis !![1, t; 0, 1]) = 1 := by
  rw [Orientation.orientedJacobian_self, det_toLin, det_fin_two_of]
  norm_num

/-- **The shear `[[1, t], [0, 1]]`** (in an orthonormal basis) of an inner product plane has
`q_O = (2 + t² + |t| √(t² + 4)) / 2` for any orientation of the plane. -/
theorem outerDistortion_shear [Fact (finrank ℝ E = 2)] (t : ℝ) :
    o.outerDistortion o (toLin e.toBasis e.toBasis !![1, t; 0, 1]) =
      ENNReal.ofReal ((2 + t ^ 2 + |t| * √(t ^ 2 + 4)) / 2) := by
  have hJ := orientedJacobian_shear o e t
  rw [Orientation.outerDistortion_of_pos _ _ (by rw [hJ]; exact one_pos), hJ,
    norm_toContinuousLinearMap_eq_singularValues_zero,
    (sq_singularValues_toLin_shear_fin_two e t).1, div_one]

/-- **The shear `[[1, t], [0, 1]]`** (in an orthonormal basis) of an inner product plane has
`q_I = 2 / (2 + t² - |t| √(t² + 4)) = (2 + t² + |t| √(t² + 4)) / 2` for any orientation of the
plane. -/
theorem innerDistortion_shear [Fact (finrank ℝ E = 2)] (t : ℝ) :
    o.innerDistortion o (toLin e.toBasis e.toBasis !![1, t; 0, 1]) =
      (2 + t ^ 2 + |t| * √(t ^ 2 + 4)) / 2 := by
  have h := o.outerDistortion_eq_ofReal_innerDistortion_of_fin_two o
    (by rw [orientedJacobian_shear o e t]; exact one_pos)
  rw [outerDistortion_shear] at h
  exact ((ENNReal.ofReal_eq_ofReal_iff (by positivity)
    (Orientation.innerDistortion_nonneg _ _ _)).mp h).symm

end Shear

end TauCeti.LinearDistortionExamples

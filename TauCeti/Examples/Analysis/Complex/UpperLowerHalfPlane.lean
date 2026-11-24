/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
public import TauCeti.Analysis.Complex.UpperHalfPlane.UpperLowerHalfPlane

/-!
# Checks for the Möbius action on `ℍ^±`

The reflection `diag(1, -1)` separates the raw action on `ℍ^± = ℂ ∖ ℝ` from Mathlib's folded
action `UpperHalfPlane.glAction` on `ℍ`; a translation shows that they agree for positive
determinant; a dilation is checked on a point of the lower half-plane, where folding commutes
with the action. Then the quarter turn fixes `i`, the section `x + i y ↦ !![y, x; 0, 1]` is
computed at `2 + 3i` and at `-i`, and `-i` is not in the orbit of `i` under positive
determinant.
-/

public section

open UpperHalfPlane Matrix TauCeti

open TauCeti.UpperLowerHalfPlane (fold sectionGL sectionGL_smul_I
  coe_fold_of_im_neg fold_smul smul_I_eq_I_iff im_smul_pos_iff)

namespace TauCeti.UpperLowerHalfPlaneExamples

/-- The reflection `diag(1, -1)`. -/
noncomputable def reflectionGL : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, -1] (by norm_num [det_fin_two])

/-- The translation `[[1, 1], [0, 1]]`. -/
noncomputable def translationGL : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by norm_num [det_fin_two])

/-- The dilation `[[2, 0], [0, 1]]`. -/
noncomputable def dilationGL : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![2, 0; 0, 1] (by norm_num [det_fin_two])

/-- The point `-i` of `ℍ^±`. -/
noncomputable def negI : UpperLowerHalfPlane :=
  UpperLowerHalfPlane.mk (-Complex.I) (by rw [Complex.neg_im, Complex.I_im]; norm_num)

-- The raw image of `i` under `diag(1, -1)` is `-i`.
example : ((reflectionGL • UpperLowerHalfPlane.I : UpperLowerHalfPlane) : ℂ) = -Complex.I := by
  simp [UpperLowerHalfPlane.coe_smul, num, denom, reflectionGL, div_neg]

-- The folded image of `i` under `diag(1, -1)` is `i`.
example : reflectionGL • UpperHalfPlane.I = UpperHalfPlane.I := by
  rw [gl_smul_I_eq_I_iff_of_neg (by simp [reflectionGL, det_fin_two])]
  simp [reflectionGL]

-- The raw image of `i` under `[[1, 1], [0, 1]]` is `1 + i` ...
example :
    ((translationGL • UpperLowerHalfPlane.I : UpperLowerHalfPlane) : ℂ) = 1 + Complex.I := by
  simp [UpperLowerHalfPlane.coe_smul, num, denom, translationGL, add_comm]

-- ... and agrees with the folded action.
example : ((translationGL • UpperHalfPlane.I : ℍ) : ℂ) = 1 + Complex.I := by
  rw [coe_smul_of_det_pos (by simp [translationGL, det_fin_two])]
  simp [num, denom, translationGL, add_comm]

-- The raw image of `-i` under `[[2, 0], [0, 1]]` is `-2i` ...
example : ((dilationGL • negI : UpperLowerHalfPlane) : ℂ) = -2 * Complex.I := by
  simp [UpperLowerHalfPlane.coe_smul, num, denom, dilationGL, negI]

-- ... and folding it gives `2i`, the folded action on the folded input `i`.
example : ((fold (dilationGL • negI) : ℍ) : ℂ) = 2 * Complex.I ∧
    ((dilationGL • fold negI : ℍ) : ℂ) = 2 * Complex.I := by
  rw [← fold_smul, and_self, coe_fold_of_im_neg (by
    simp [UpperLowerHalfPlane.coe_smul, num, denom, dilationGL, negI])]
  simp [UpperLowerHalfPlane.coe_smul, num, denom, dilationGL, negI, map_ofNat]

-- The quarter turn `[[0, 1], [-1, 0]]` is the rotation by `π / 2` and fixes `i`.
example : ∃ g : GL (Fin 2) ℝ,
    (g : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; -1, 0] ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) =
        (SpecialLinearGroup.rotation (Real.pi / 2) : Matrix (Fin 2) (Fin 2) ℝ) ∧
      g • UpperLowerHalfPlane.I = UpperLowerHalfPlane.I := by
  refine ⟨GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by norm_num [det_fin_two]),
    rfl, ?_, ?_⟩
  · simp [SpecialLinearGroup.coe_rotation]
  · rw [smul_I_eq_I_iff]
    simp

-- The section at `2 + 3i` is `[[3, 2], [0, 1]]`, of determinant `3`, and sends `i` to `2 + 3i`.
example :
    let z := UpperLowerHalfPlane.mk (2 + 3 * Complex.I)
      (by rw [Complex.add_im, Complex.mul_im]; norm_num)
    (sectionGL z : Matrix (Fin 2) (Fin 2) ℝ) = !![3, 2; 0, 1] ∧ (sectionGL z).det.val = 3 ∧
      sectionGL z • UpperLowerHalfPlane.I = z := by
  intro z
  refine ⟨by simp [z], by simp [z], sectionGL_smul_I z⟩

-- The section at `-i` has determinant `-1` ...
example : (sectionGL negI).det.val = -1 := by
  simp [negI]

-- ... and `-i` is not in the positive-determinant orbit of `i`.
example (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) : g • UpperLowerHalfPlane.I ≠ negI := by
  intro h
  have him := (im_smul_pos_iff g UpperLowerHalfPlane.I).2 (by simpa using hg)
  rw [h] at him
  norm_num [negI] at him

end TauCeti.UpperLowerHalfPlaneExamples

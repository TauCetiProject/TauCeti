/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.Topology.Order.IntermediateValue

/-!
# Rotations about `I` in `SL(2, ℝ)`

The one-parameter family `rotation θ = !![cos θ, sin θ; -sin θ, cos θ]` in `SL(2, ℝ)`, the
rotations about `I`: each fixes `I` (`rotation_smul_I`), and `rotation (π/2)` acts as
`z ↦ -1/z` (`rotation_pi_div_two_smul`). Rotating a point from `θ = 0` to `θ = π/2` therefore
reverses the sign of its real part, so by the intermediate value theorem some rotation moves any
point onto the imaginary axis (`exists_rotation_smul_re_eq_zero`). This is the ingredient that
turns transitivity of `PSL(2, ℝ)` on `ℍ` into two-point transitivity on geodesic lines
(`Geodesic.lean`).

The stabiliser of `I` is not identified with the rotation group here, and no rotation angle is
computed explicitly.

## Main declarations

* `TauCeti.UpperHalfPlane.rotation θ` — the matrix `!![cos θ, sin θ; -sin θ, cos θ]` in
  `SL(2, ℝ)`; `coe_rotation` exposes it, and `rotation_zero`, `rotation_add`, `rotation_neg` make
  the family a one-parameter subgroup.
* `TauCeti.UpperHalfPlane.coe_rotation_smul` — its Möbius action, as a complex number.
* `TauCeti.UpperHalfPlane.rotation_smul_I` — every rotation fixes `I`.
* `TauCeti.UpperHalfPlane.rotation_pi_div_two_smul` — `rotation (π/2)` acts as `z ↦ -1/z`.
* `TauCeti.UpperHalfPlane.exists_rotation_smul_re_eq_zero` — some rotation about `I` moves any
  point onto the imaginary axis.
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

/-- The rotation `!![cos θ, sin θ; -sin θ, cos θ]`, an element of `SL(2, ℝ)`. -/
def rotation (θ : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ], by
    rw [Matrix.det_fin_two_of]
    linear_combination Real.cos_sq_add_sin_sq θ⟩

/-- The matrix of `rotation θ`. -/
@[simp]
theorem coe_rotation (θ : ℝ) :
    (rotation θ : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] :=
  Matrix.SpecialLinearGroup.coe_mk _ _

/-- The rotation by `0` is the identity. -/
@[simp]
theorem rotation_zero : rotation 0 = 1 :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;> simp

/-- The rotations form a one-parameter subgroup: `rotation (θ + φ) = rotation θ * rotation φ`. -/
@[simp]
theorem rotation_add (θ φ : ℝ) : rotation (θ + φ) = rotation θ * rotation φ :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;>
      simp [Real.cos_add, Real.sin_add, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The inverse of `rotation θ` is `rotation (-θ)`. -/
@[simp]
theorem rotation_neg (θ : ℝ) : rotation (-θ) = (rotation θ)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rotation_add, neg_add_cancel, rotation_zero]

/-- The Möbius action of `rotation θ`, as a complex number:
`(cos θ · z + sin θ) / (-sin θ · z + cos θ)`. -/
theorem coe_rotation_smul (θ : ℝ) (z : ℍ) :
    ((rotation θ • z : ℍ) : ℂ) =
      ((Real.cos θ : ℂ) * z + Real.sin θ) / (-(Real.sin θ : ℂ) * z + Real.cos θ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

/-- The rotations fix `I`. -/
@[simp]
theorem rotation_smul_I (θ : ℝ) : rotation θ • UpperHalfPlane.I = UpperHalfPlane.I := by
  rw [MulAction.compHom_smul_def, gl_smul_I_eq_I_iff_of_pos (by simp)]
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

/-- The rotation by `π/2` acts as `z ↦ -1/z`. -/
theorem rotation_pi_div_two_smul (z : ℍ) :
    ((rotation (Real.pi / 2) • z : ℍ) : ℂ) = (-(z : ℂ))⁻¹ := by
  simp [coe_rotation_smul]

/-- Some rotation about `I` moves any point onto the imaginary axis. -/
theorem exists_rotation_smul_re_eq_zero (w : ℍ) :
    ∃ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), (rotation θ • w).re = 0 := by
  have hcont : Continuous fun θ => (rotation θ • w).re := by
    have : (fun θ => (rotation θ • w).re) = fun θ => (((Real.cos θ : ℂ) * w + Real.sin θ) /
        (-(Real.sin θ : ℂ) * w + Real.cos θ)).re := by
      funext θ
      rw [← coe_re, coe_rotation_smul]
    rw [this]
    refine Complex.continuous_re.comp (Continuous.div (by fun_prop) (by fun_prop) ?_)
    intro θ
    simpa [denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix] using
      denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ (rotation θ)) w
  have h0 : (rotation 0 • w).re = w.re := by
    rw [rotation_zero, one_smul]
  have hpi : (rotation (Real.pi / 2) • w).re = -(w.re / Complex.normSq w) := by
    rw [← coe_re, rotation_pi_div_two_smul]
    simp [Complex.inv_re, coe_re]
  have hpos : 0 < Complex.normSq w := Complex.normSq_pos.2 (ne_zero w)
  have hab : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rcases le_or_gt 0 w.re with hre | hre
  · have hpi' : (rotation (Real.pi / 2) • w).re ≤ 0 := by
      rw [hpi]
      exact neg_nonpos.2 (div_nonneg hre hpos.le)
    obtain ⟨θ, hθ, hθ0⟩ := intermediate_value_Icc' hab hcont.continuousOn ⟨hpi', h0 ▸ hre⟩
    exact ⟨θ, hθ, hθ0⟩
  · have hpi' : 0 ≤ (rotation (Real.pi / 2) • w).re := by
      rw [hpi]
      exact neg_nonneg.2 (div_nonpos_of_nonpos_of_nonneg hre.le hpos.le)
    obtain ⟨θ, hθ, hθ0⟩ := intermediate_value_Icc hab hcont.continuousOn ⟨h0 ▸ hre.le, hpi'⟩
    exact ⟨θ, hθ, hθ0⟩

end TauCeti.UpperHalfPlane

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Topology.Algebra.Group.Matrix
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.MatrixFinTwo
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action

/-!
# Rotations about `I` in `SL(2, ℝ)`

The one-parameter family `Matrix.SpecialLinearGroup.rotation θ = !![cos θ, sin θ; -sin θ, cos θ]`
in `SL(2, ℝ)` consists of the rotations about `I`: each fixes `I` (`rotation_smul_I`), and
`rotation (π/2)` is, in `PSL(2, ℝ)`, the involution `pslS` acting as `z ↦ -1/z`
(`coe_rotation_pi_div_two`). Rotating a point from `θ = 0` to `θ = π/2` therefore reverses the
sign of its real part, so by the intermediate value theorem some rotation moves any point onto the
imaginary axis (`exists_rotation_smul_re_eq_zero`). This is the ingredient that turns transitivity
of `PSL(2, ℝ)` on `ℍ` into two-point transitivity on geodesic lines (`Geodesic.lean`).

The stabiliser of `I` is not identified with the rotation group here, and no rotation angle is
computed explicitly.

## Main declarations

* `Matrix.SpecialLinearGroup.continuous_rotation` — `θ ↦ rotation θ` is continuous.
* `TauCeti.UpperHalfPlane.rotation_smul_I` — every rotation fixes `I`.
* `TauCeti.UpperHalfPlane.coe_rotation_pi_div_two` — the class of `rotation (π/2)` in
  `PSL(2, ℝ)` is `pslS`.
* `TauCeti.UpperHalfPlane.exists_rotation_smul_re_eq_zero` — some rotation about `I` moves any
  point onto the imaginary axis.
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

/-- The rotations `θ ↦ rotation θ` form a continuous family in `SL(2, ℝ)`. -/
@[fun_prop]
theorem continuous_rotation : Continuous rotation :=
  Continuous.subtype_mk (continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, coe_rotation, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      fun_prop) _

end Matrix.SpecialLinearGroup

namespace TauCeti.UpperHalfPlane

open Matrix.SpecialLinearGroup (rotation rotation_zero)

/-- The rotations fix `I`. -/
@[simp]
theorem rotation_smul_I (θ : ℝ) : rotation θ • UpperHalfPlane.I = UpperHalfPlane.I := by
  rw [MulAction.compHom_smul_def, gl_smul_I_eq_I_iff_of_pos (by simp)]
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

/-- The class of `rotation (π/2) = !![0, 1; -1, 0]` in `PSL(2, ℝ)` is `pslS`, the image of
`ModularGroup.S = !![0, -1; 1, 0]`: the two matrices differ by a sign. -/
theorem coe_rotation_pi_div_two : (↑(rotation (Real.pi / 2)) : PSL(2, ℝ)) = pslS := by
  have h : rotation (Real.pi / 2) =
      -(Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) _root_.ModularGroup.S) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.map_apply_coe, _root_.ModularGroup.coe_S]
  rw [h, Matrix.ProjectiveSpecialLinearGroup.mk_neg, pslS_def, psl2zToPSL2R_mk,
    sl2zToPSL2R_apply]

/-- Some rotation about `I` moves any point onto the imaginary axis. -/
theorem exists_rotation_smul_re_eq_zero (w : ℍ) :
    ∃ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), (rotation θ • w).re = 0 := by
  have hcont : Continuous fun θ => (rotation θ • w).re :=
    UpperHalfPlane.continuous_re.comp
      (Matrix.SpecialLinearGroup.continuous_rotation.smul continuous_const)
  have h0 : (rotation 0 • w).re = w.re := by
    rw [rotation_zero, one_smul]
  have hpi : (rotation (Real.pi / 2) • w).re = -w.re / Complex.normSq w := by
    rw [← pslMk_smul, coe_rotation_pi_div_two, re_pslS_smul]
  have hpos : 0 < Complex.normSq w := Complex.normSq_pos.2 (ne_zero w)
  have hab : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rcases le_or_gt 0 w.re with hre | hre
  · have hpi' : (rotation (Real.pi / 2) • w).re ≤ 0 := by
      rw [hpi]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hre) hpos.le
    obtain ⟨θ, hθ, hθ0⟩ := intermediate_value_Icc' hab hcont.continuousOn ⟨hpi', h0 ▸ hre⟩
    exact ⟨θ, hθ, hθ0⟩
  · have hpi' : 0 ≤ (rotation (Real.pi / 2) • w).re := by
      rw [hpi]
      exact div_nonneg (neg_nonneg.2 hre.le) hpos.le
    obtain ⟨θ, hθ, hθ0⟩ := intermediate_value_Icc hab hcont.continuousOn ⟨h0 ▸ hre.le, hpi'⟩
    exact ⟨θ, hθ, hθ0⟩

end TauCeti.UpperHalfPlane

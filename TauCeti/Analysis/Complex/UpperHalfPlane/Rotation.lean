/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
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
(`Matrix.SpecialLinearGroup.pslMk_rotation_pi_div_two`). Rotating a point from `θ = 0` to
`θ = π/2` therefore reverses the sign of its real part, so by the intermediate value theorem some
rotation moves any point onto the imaginary axis (`exists_rotation_smul_re_eq_zero`). This is the
ingredient that turns transitivity of `PSL(2, ℝ)` on `ℍ` into two-point transitivity on geodesic
lines (`Geodesic.lean`).

The file also describes the stabiliser of `I` in `SL(2, ℝ)` in coordinates: its elements are
exactly the matrices `!![a, b; -b, a]` with `a² + b² = 1` (`smul_I_eq_I_iff` and
`sq_add_sq_eq_one_of_smul_I_eq_I`). Their parametrization by an angle `θ` as `rotation θ` is not
set up here, and no rotation angle is computed explicitly.

## Main declarations

* `TauCeti.UpperHalfPlane.rotation_smul_I` — every rotation fixes `I`.
* `Matrix.SpecialLinearGroup.smul_I_eq_I_iff` — the elements of `SL(2, ℝ)` fixing `I` are the
  matrices `!![a, b; -b, a]`, and `Matrix.SpecialLinearGroup.sq_add_sq_eq_one_of_smul_I_eq_I`
  — these have `a² + b² = 1`.
* `TauCeti.UpperHalfPlane.exists_rotation_smul_re_eq_zero` — some rotation about `I` moves any
  point onto the imaginary axis.
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

open Matrix.SpecialLinearGroup (rotation rotation_zero pslMk_rotation_pi_div_two)

/-- The rotations fix `I`. -/
@[simp]
theorem rotation_smul_I (θ : ℝ) : rotation θ • UpperHalfPlane.I = UpperHalfPlane.I := by
  rw [MulAction.compHom_smul_def, gl_smul_I_eq_I_iff_of_pos (by simp)]
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

/-- An element of `SL(2, ℝ)` fixes `I` exactly when it has the form `!![a, b; -b, a]`. This is the
`SL(2, ℝ)` form of Mathlib's `UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos`. -/
theorem _root_.Matrix.SpecialLinearGroup.smul_I_eq_I_iff (k : SL(2, ℝ)) :
    k • UpperHalfPlane.I = UpperHalfPlane.I ↔ k 1 1 = k 0 0 ∧ k 1 0 = -k 0 1 := by
  rw [MulAction.compHom_smul_def, gl_smul_I_eq_I_iff_of_pos (by simp)]
  simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.algebraMap_self_apply]
  constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨h₀.symm, by linear_combination h₁⟩
  · rintro ⟨h₀, h₁⟩
    exact ⟨h₀.symm, by linear_combination h₁⟩

/-- The first row `(a, b)` of an element `!![a, b; -b, a]` of `SL(2, ℝ)` fixing `I` is a unit
vector: `a² + b² = 1`. -/
theorem _root_.Matrix.SpecialLinearGroup.sq_add_sq_eq_one_of_smul_I_eq_I {k : SL(2, ℝ)}
    (hk : k • UpperHalfPlane.I = UpperHalfPlane.I) : k 0 0 ^ 2 + k 0 1 ^ 2 = 1 := by
  obtain ⟨h₁₁, h₁₀⟩ := (Matrix.SpecialLinearGroup.smul_I_eq_I_iff k).1 hk
  have hdet := k.det_coe
  rw [Matrix.det_fin_two, h₁₁, h₁₀] at hdet
  linear_combination hdet

/-- Some rotation about `I` moves any point onto the imaginary axis. -/
theorem exists_rotation_smul_re_eq_zero (w : ℍ) :
    ∃ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), (rotation θ • w).re = 0 := by
  have hcont : Continuous fun θ => (rotation θ • w).re :=
    UpperHalfPlane.continuous_re.comp
      (Matrix.SpecialLinearGroup.continuous_rotation.smul continuous_const)
  have h0 : (rotation 0 • w).re = w.re := by
    rw [rotation_zero, one_smul]
  have hpi : (rotation (Real.pi / 2) • w).re = -w.re / Complex.normSq w := by
    rw [← pslMk_smul, pslMk_rotation_pi_div_two, re_pslS_smul]
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

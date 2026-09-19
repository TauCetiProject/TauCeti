/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Datum
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import Mathlib.Analysis.Complex.Periodic

/-!
# Coordinates of normalized cusp data

The exponential coordinate of a normalized cusp datum is invariant under the full cusp
stabilizer. In scaling coordinates, the selected generator translates by the cusp width.
These formulas provide the datum-level interface for comparing cusp coordinates.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Springer, 2005, §2.4.
-/

public section

open Matrix.ProjectiveSpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti

variable {Γ : Subgroup PSL(2, ℝ)}

namespace Subgroup.CuspDatum

/-- The exponential coordinate of a normalized cusp datum on the upper half-plane. -/
noncomputable def coordinate (D : Γ.CuspDatum) (z : ℍ) : ℂ :=
  Function.Periodic.qParam D.width (↑(D.scaling • z) : ℂ)

/-- The cusp coordinate is the q-parameter of the scaled point, with the datum's width. -/
theorem coordinate_apply (D : Γ.CuspDatum) (z : ℍ) :
    coordinate D z = Function.Periodic.qParam D.width (↑(D.scaling • z) : ℂ) := (rfl)

/-- The exponential cusp coordinate never vanishes on the upper half-plane. -/
@[simp]
theorem coordinate_ne_zero (D : Γ.CuspDatum) (z : ℍ) : coordinate D z ≠ 0 := by
  rw [coordinate_apply]
  exact Function.Periodic.qParam_ne_zero _

/-- The exponential cusp coordinate lies in the open unit disc. -/
theorem norm_coordinate_lt_one (D : Γ.CuspDatum) (z : ℍ) : ‖coordinate D z‖ < 1 := by
  rw [coordinate_apply]
  exact Function.Periodic.norm_qParam_lt_one D.width_pos (D.scaling • z).im_pos

/-- In scaling coordinates, the selected generator acts by translation through the width. -/
theorem coe_scaling_smul_generator (D : Γ.CuspDatum) (z : ℍ) :
    (↑(D.scaling • (D.generator : PSL(2, ℝ)) • z) : ℂ) =
      (↑(D.scaling • z) : ℂ) + D.width := by
  have heq : D.scaling • (D.generator : PSL(2, ℝ)) • z =
      upperRightHom D.width • (D.scaling • z) := by
    rw [← D.scaling_mul_generator_mul_inv, mul_smul, mul_smul, inv_smul_smul]
  rw [heq, upperRightHom_apply, UpperHalfPlane.pslMk_smul, coe_specialLinearGroup_apply]
  simp [Matrix.SpecialLinearGroup.transvection_coe]

/-- The exponential cusp coordinate is invariant under the full cusp stabilizer. -/
@[simp]
theorem coordinate_smul (D : Γ.CuspDatum) {g : Γ}
    (hg : g ∈ MulAction.stabilizer Γ D.cusp) (z : ℍ) :
    coordinate D (g • z) = coordinate D z := by
  obtain ⟨n, hn⟩ := D.mem_stabilizer_iff_conj.mp hg
  have heq : D.scaling • (g • z) = upperRightHom (n * D.width) • (D.scaling • z) := by
    rw [← hn, mul_smul, mul_smul, inv_smul_smul, Subgroup.smul_def]
  have hcoe : (↑(D.scaling • (g • z)) : ℂ) =
      (↑(D.scaling • z) : ℂ) + (n : ℝ) * D.width := by
    rw [heq, upperRightHom_apply, UpperHalfPlane.pslMk_smul, coe_specialLinearGroup_apply]
    simp [Matrix.SpecialLinearGroup.transvection_coe]
  rw [coordinate_apply, coordinate_apply, hcoe]
  simp only [Function.Periodic.qParam]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨n, ?_⟩
  push_cast
  field_simp [D.width_pos.ne']

end Subgroup.CuspDatum

end TauCeti

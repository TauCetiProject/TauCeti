/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Residue.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Sphere
import TauCeti.Analysis.Contour.Residue.SimplePole

/-!
# Residues of `dz / z` on the Riemann sphere

The `1`-form `dz / z` on the Riemann sphere `OnePoint ℂ` has residue `1` at `0`
(`TauCeti.RiemannSurface.OneForm.residue_inv_smul_sphereCoordinateDifferential_zero`) and `-1` at
`∞` (`TauCeti.RiemannSurface.OneForm.residue_inv_smul_sphereCoordinateDifferential_infty`), the
residue at `∞` being read in the inverted chart `w = 1/z`, where `dz / z = -dw / w`. The two
residues add up to zero, as the residue theorem on a compact Riemann surface
(`TauCeti.RiemannSurface.OneForm.sum_residue_eq_zero`) requires.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §10 (the residue theorem).
-/

public noncomputable section

open Complex Function OnePoint

open scoped Manifold

namespace TauCeti.RiemannSurface.OneForm

/-! ### Check: the form `dz / z` on the sphere -/

/-- The `1`-form `dz / z` on the sphere, in the affine and inverted charts. -/
private theorem coeff_inv_smul_sphereCoordinateDifferential_invChart {w : ℂ} (hw : w ≠ 0) :
    (((affineChart : OnePoint ℂ → ℂ))⁻¹ • sphereCoordinateDifferential).coeff invChart w =
      -w⁻¹ := by
  rw [coeff_smul, Pi.mul_apply, coeff_invChart_eq_neg_inv_sq_mul _ hw,
    coeff_sphereCoordinateDifferential_affineChart, comp_apply, Pi.inv_apply,
    invChart_symm_of_ne_zero hw, affineChart_coe, inv_inv]
  field_simp

/-- The form `dz / z` has residue `1` at `0`. -/
theorem residue_inv_smul_sphereCoordinateDifferential_zero :
    (((affineChart : OnePoint ℂ → ℂ))⁻¹ • sphereCoordinateDifferential).residue
      ((0 : ℂ) : OnePoint ℂ) = 1 := by
  rw [residue_def, chartAt_coe, affineChart_coe, coeff_smul,
    coeff_sphereCoordinateDifferential_affineChart]
  have : (((affineChart : OnePoint ℂ → ℂ))⁻¹ ∘ affineChart.symm) * (fun _ ↦ (1 : ℂ)) =
      fun z ↦ (z - 0)⁻¹ := by
    funext z
    simp
  rw [this, Contour.residue_sub_inv]

/-- The form `dz / z` has residue `-1` at `∞`. -/
theorem residue_inv_smul_sphereCoordinateDifferential_infty :
    (((affineChart : OnePoint ℂ → ℂ))⁻¹ • sphereCoordinateDifferential).residue ∞ = -1 := by
  rw [residue_def, chartAt_infty, invChart_infty,
    Contour.residue_congr_nhdsNE (g := (-1 : ℂ) • fun w ↦ (w - 0)⁻¹)
      (eventually_nhdsWithin_of_forall fun w hw ↦ by
        rw [coeff_inv_smul_sphereCoordinateDifferential_invChart hw]
        simp),
    Contour.residue_const_smul, Contour.residue_sub_inv, smul_eq_mul, mul_one]

end TauCeti.RiemannSurface.OneForm

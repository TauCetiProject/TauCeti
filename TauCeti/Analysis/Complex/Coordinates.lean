/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import TauCeti.LinearAlgebra.Complex.Determinant

/-!
# Real coordinates of the complex plane

The real linear coordinate interchange is an involution with determinant `-1`, recording
the reversal of orientation. Any `v` has real coordinates in the real basis `u`, `r * u * I`,
`u ≠ 0`, `r ≠ 0`, of radial and angular directions at the point `r * u`
(`Complex.eq_re_mul_add_im_div_mul`). The real frame `(1, 0)`, `(i, 0)`, `(0, 1)` of `ℂ × ℝ` is
linearly independent. A point `c + t * I` of a vertical line with `c ≠ 0` is nonzero.
-/

public section

namespace Complex

/-- The real continuous linear equivalence interchanging real and imaginary coordinates. -/
noncomputable def coordinateSwapCLE : ℂ ≃L[ℝ] ℂ :=
  (equivRealProdCLM.trans (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)).trans
    equivRealProdCLM.symm

/-- Coordinate swap sends `(x,y)` to `(y,x)`. -/
@[simp]
theorem coordinateSwapCLE_apply (z : ℂ) : coordinateSwapCLE z = ⟨z.im, z.re⟩ := (rfl)

/-- Coordinate interchange is its own inverse. -/
@[simp]
theorem coordinateSwapCLE_symm : coordinateSwapCLE.symm = coordinateSwapCLE := by
  ext z
  rfl

/-- Interchanging the coordinates twice returns the original point. -/
theorem coordinateSwapCLE_coordinateSwapCLE (z : ℂ) :
    coordinateSwapCLE (coordinateSwapCLE z) = z := (rfl)

/-- Interchanging the coordinates has real determinant `-1`. -/
@[simp]
theorem det_coordinateSwapCLE : coordinateSwapCLE.toLinearEquiv.toLinearMap.det = -1 := by
  rw [LinearMap.det_complex]
  simp

/-- The determinant unit of coordinate interchange is `-1`. -/
@[simp]
theorem linearEquiv_det_coordinateSwapCLE : coordinateSwapCLE.toLinearEquiv.det = -1 := by
  simp [← Units.val_inj]

/-- A vector `v` in polar coordinates at a point `r * u` with `u ≠ 0`, `r ≠ 0`: its components
along the radial direction `u` and the angular direction `r * u * I`. -/
theorem eq_re_mul_add_im_div_mul {u : ℂ} (hu : u ≠ 0) {r : ℝ} (hr : r ≠ 0) (v : ℂ) :
    v = ((v / u).re : ℂ) * u + (((v / u).im / r : ℝ) : ℂ) * (r * u * I) := by
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr
  conv_lhs => rw [← div_mul_cancel₀ v hu, ← re_add_im (v / u)]
  push_cast
  field_simp

/-- The real frame `(1, 0)`, `(i, 0)`, `(0, 1)` of `ℂ × ℝ` is linearly independent. -/
theorem linearIndependent_one_zero_I_zero_zero_one :
    LinearIndependent ℝ ![((1 : ℂ), (0 : ℝ)), (I, 0), (0, 1)] := by
  refine Fintype.linearIndependent_iff.2 fun g hg i ↦ ?_
  rw [Fin.sum_univ_three] at hg
  fin_cases i
  · simpa using congrArg (fun x : ℂ × ℝ ↦ x.1.re) hg
  · simpa using congrArg (fun x : ℂ × ℝ ↦ x.1.im) hg
  · simpa using congrArg Prod.snd hg

/-- A point `c + t * I` of the vertical line `Re z = c` is nonzero as soon as `c` is.  Mathlib's
`Complex.ne_zero_of_re_pos` covers only the positive-real-part case. -/
theorem ofReal_add_mul_I_ne_zero {c : ℝ} (hc : c ≠ 0) (t : ℝ) : (c : ℂ) + t * I ≠ 0 :=
  fun h ↦ hc (by simpa using congrArg Complex.re h)

end Complex

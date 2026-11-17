/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import TauCeti.LinearAlgebra.Complex.Determinant
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Real coordinates of the complex plane

The real linear coordinate interchange is an involution with determinant `-1`, recording
the reversal of orientation. Any `v` has real coordinates in the real basis `u`, `r * u * I`,
`u ≠ 0`, `r ≠ 0`, of radial and angular directions at the point `r * u`
(`Complex.eq_re_mul_add_im_div_mul`). The real frame `(1, 0)`, `(i, 0)`, `(0, 1)` of `ℂ × ℝ` is
linearly independent. A point `c + t * I` of a vertical line with `c ≠ 0` is nonzero.

In the frame of a nonzero direction `v`, the point `v (s ± h i)` on either side of the line through
`v s` with direction `v` has imaginary coordinate `±h`
(`TauCeti.mul_add_mul_I_sub_mul_div_im`) and lies at distance `‖v‖ * |h|` from `v s`
(`Complex.dist_mul_add_mul_I`).

A rank-one map `L.smulRight w` built from a real functional `L` on `ℂ` splits along the real
basis `1, I` as `L 1 • re ⊗ w + L I • im ⊗ w`
(`ContinuousLinearMap.smulRight_eq_re_add_im`). A real-linear map `D` on `ℂ`
precomposed with multiplication by `c = a + b i`, tested in the Cauchy–Riemann combination with an
operator `A`, is `D (c * 1) + A D (c * I) = a (D 1 + A D i) + b (D i - A D 1)`
(`ContinuousLinearMap.apply_mul_one_add_apply_mul_I`).
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

/-- Coordinate interchange sends `1` to `I`. -/
theorem coordinateSwapCLE_one : coordinateSwapCLE 1 = I :=
  Complex.ext (by simp) (by simp)

/-- Coordinate interchange sends `I` to `1`. -/
theorem coordinateSwapCLE_I : coordinateSwapCLE I = 1 :=
  Complex.ext (by simp) (by simp)

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

/-- The point `h` units off the line `s ↦ v * s` in the direction `v * I` is at distance
`‖v‖ * |h|` from the line point. -/
@[simp]
theorem dist_mul_add_mul_I (v : ℂ) (s h : ℝ) : dist (v * (s + h * I)) (v * s) = ‖v‖ * |h| := by
  rw [dist_eq_norm]
  have : v * (s + h * I) - v * s = v * (h * I) := by ring
  rw [this, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The point `h` units off the line `s ↦ v * s` in the direction `-(v * I)` is at distance
`‖v‖ * |h|` from the line point. -/
@[simp]
theorem dist_mul_sub_mul_I (v : ℂ) (s h : ℝ) : dist (v * (s - h * I)) (v * s) = ‖v‖ * |h| := by
  have := dist_mul_add_mul_I v s (-h)
  rwa [ofReal_neg, neg_mul, ← sub_eq_add_neg, abs_neg] at this

end Complex

namespace TauCeti

section LineThrough

open Complex

variable {v : ℂ} {s : ℝ}

/-- The imaginary part of the coordinate, in the frame of `v`, of the point `v * (s + h * I)`
relative to the line point `v * s` is `h`. -/
@[simp]
theorem mul_add_mul_I_sub_mul_div_im (hv : v ≠ 0) (h : ℝ) :
    ((v * (s + h * I) - v * s) / v).im = h := by
  have : (v * (s + h * I) - v * s) / v = h * I := by
    field_simp
    ring
  rw [this]
  simp only [mul_im, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, add_zero]

/-- The imaginary part of the coordinate, in the frame of `v`, of the point `v * (s - h * I)`
relative to the line point `v * s` is `-h`. -/
@[simp]
theorem mul_sub_mul_I_sub_mul_div_im (hv : v ≠ 0) (h : ℝ) :
    ((v * (s - h * I) - v * s) / v).im = -h := by
  have := mul_add_mul_I_sub_mul_div_im (v := v) (s := s) hv (-h)
  rwa [ofReal_neg, neg_mul, ← sub_eq_add_neg] at this

end LineThrough

end TauCeti

namespace ContinuousLinearMap

/-- The rank-one map `L.smulRight w` determined by a real functional `L` on `ℂ` splits along the
real basis `1, I` of `ℂ`. -/
theorem smulRight_eq_re_add_im {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] (L : ℂ →L[ℝ] ℝ) (w : F) :
    L.smulRight w =
      L 1 • Complex.reCLM.smulRight w + L Complex.I • Complex.imCLM.smulRight w := by
  ext v
  have hv := (L : ℂ →ₗ[ℝ] ℝ).apply_eq_re_smul_one_add_im_smul_I v
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at hv
  simp [hv, add_smul, smul_smul, mul_comm]

/-- A real-linear map `D` on `ℂ`, precomposed with multiplication by `c = a + b i`, tested in the
Cauchy–Riemann combination: `D (c·1) + A D (c·i) = a (D 1 + A D i) + b (D i - A D 1)`. -/
theorem apply_mul_one_add_apply_mul_I {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] (D : ℂ →L[ℝ] F) (A : F →L[ℝ] F) (c : ℂ) :
    D (c * 1) + A (D (c * Complex.I)) =
      c.re • (D 1 + A (D Complex.I)) + c.im • (D Complex.I - A (D 1)) := by
  have h1 : c * 1 = c.re • (1 : ℂ) + c.im • Complex.I := by apply Complex.ext <;> simp
  have h2 : c * Complex.I = c.re • Complex.I - c.im • (1 : ℂ) := by apply Complex.ext <;> simp
  rw [h1, h2]
  simp only [map_add, map_sub, map_smul, smul_add, smul_sub]
  abel

end ContinuousLinearMap

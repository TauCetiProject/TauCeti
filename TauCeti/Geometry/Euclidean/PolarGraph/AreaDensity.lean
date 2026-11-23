/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.PolarGraph.Slope
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# First fundamental form and area density of a polar graph

The polar parametrization of a height `h(r, θ)` takes values in the Euclidean product of the
complex plane and the real line. Its coordinate Gram determinant is
`r² (1 + hᵣ²) + hθ²`, including at radius zero and at negative radii. Where the height is given by a
Cartesian germ, the area density is the absolute radius times the Cartesian graph area factor.
-/

public noncomputable section

namespace TauCeti.PolarGraph

open Filter
open scoped Gradient InnerProductSpace Topology

/-- The graph parametrized by radius and angle in the Euclidean product `ℂ × ℝ`. -/
@[expose] def polarHeightGraph (h : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : WithLp 2 (ℂ × ℝ) :=
  WithLp.toLp 2 (Complex.polarCoord.symm q, h q)

/-- The differential of the graph pairs the polar-coordinate differential with that of
the height. -/
theorem fderiv_polarHeightGraph {h : ℝ × ℝ → ℝ} {q : ℝ × ℝ} (hh : DifferentiableAt ℝ h q)
    (v : ℝ × ℝ) : fderiv ℝ (polarHeightGraph h) q v =
      WithLp.toLp 2 (Complex.equivRealProdCLM.symm (fderivPolarCoordSymm q v), fderiv ℝ h q v) := by
  have hπ : HasFDerivAt Complex.polarCoord.symm
      (Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp (fderivPolarCoordSymm q)) q := by
    simpa only [zero_add] using hasFDerivAt_add_polarCoord_symm q 0
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] WithLp 2 (ℂ × ℝ) ↦ L v)
    (((WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℝ).symm.hasFDerivAt.comp q
      (hπ.prodMk hh.hasFDerivAt)).fderiv : fderiv ℝ (polarHeightGraph h) q = _)

/-- The Gram matrix of the actual graph differential on the radial and angular coordinate
vectors, in that order. -/
@[expose] def polarHeightGram (h : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.gram ℝ (fun i ↦ fderiv ℝ (polarHeightGraph h) q (![(1, 0), (0, 1)] i))

/-- The first fundamental form in the radius and angle coordinates. The mixed entry is the
product of the height derivatives since the planar radial and angular velocities are orthogonal. -/
theorem polarHeightGram_eq {h : ℝ × ℝ → ℝ} {q : ℝ × ℝ} (hh : DifferentiableAt ℝ h q) :
    polarHeightGram h q =
      !![1 + (fderiv ℝ h q (1, 0)) ^ 2, fderiv ℝ h q (1, 0) * fderiv ℝ h q (0, 1);
         fderiv ℝ h q (1, 0) * fderiv ℝ h q (0, 1), q.1 ^ 2 + (fderiv ℝ h q (0, 1)) ^ 2] := by
  have horth : ⟪Complex.exp (q.2 * Complex.I), circleMap 0 q.1 q.2 * Complex.I⟫_ℝ = 0 := by
    simp [Complex.inner, circleMap_zero, Complex.mul_re, Complex.mul_im]
    ring
  have horth' := (real_inner_comm (Complex.exp (q.2 * Complex.I)) _).trans horth
  ext i j
  simp only [polarHeightGram, Matrix.gram_apply, fderiv_polarHeightGraph hh,
    WithLp.prod_inner_apply, Real.inner_apply]
  fin_cases i <;> fin_cases j <;>
    simp [equivRealProd_symm_fderivPolarCoordSymm_apply_one_zero,
      equivRealProd_symm_fderivPolarCoordSymm_apply_zero_one, horth, horth'] <;> ring

/-- The Gram determinant of a polar graph at a point of differentiability of the height. -/
theorem det_polarHeightGram {h : ℝ × ℝ → ℝ} {q : ℝ × ℝ} (hh : DifferentiableAt ℝ h q) :
    (polarHeightGram h q).det =
      q.1 ^ 2 * (1 + (fderiv ℝ h q (1, 0)) ^ 2) + (fderiv ℝ h q (0, 1)) ^ 2 := by
  rw [polarHeightGram_eq hh, Matrix.det_fin_two_of]
  ring

/-- Away from the axis the area density factors into the polar Jacobian and the graph factor
in the unit radial and angular directions. -/
theorem sqrt_det_polarHeightGram {h : ℝ × ℝ → ℝ} {q : ℝ × ℝ} (hh : DifferentiableAt ℝ h q)
    (hr : q.1 ≠ 0) :
    √(polarHeightGram h q).det =
      |q.1| * √(1 + (fderiv ℝ h q (1, 0)) ^ 2 + (fderiv ℝ h q (0, 1) / q.1) ^ 2) := by
  rw [det_polarHeightGram hh, ← Real.sqrt_sq_eq_abs q.1, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  field_simp

/-- For a Cartesian height germ in a translated polar chart, the area density is the absolute
polar Jacobian times the Cartesian graph area factor, including on the axis. -/
theorem sqrt_det_polarHeightGram_eq_cartesian {f : ℂ → ℝ} {h : ℝ × ℝ → ℝ} (z₀ : ℂ)
    (q : ℝ × ℝ) (hf : DifferentiableAt ℝ f (z₀ + Complex.polarCoord.symm q))
    (he : h =ᶠ[𝓝 q] fun t ↦ f (z₀ + Complex.polarCoord.symm t)) :
    √(polarHeightGram h q).det = |q.1| * √(1 + ‖∇ f (z₀ + Complex.polarCoord.symm q)‖ ^ 2) := by
  have hd := hf.comp q (hasFDerivAt_add_polarCoord_symm q z₀).differentiableAt
  have hh := hd.congr_of_eventuallyEq he
  rw [det_polarHeightGram hh, ← Real.sqrt_sq_eq_abs q.1, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  linear_combination -sq_radius_mul_norm_gradient_sq z₀ q hf he

end TauCeti.PolarGraph

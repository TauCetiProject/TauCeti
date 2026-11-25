/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.PolarGraph.Basic
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

/-- The graph parametrized on all radius-angle pairs, allowing signed and zero radius, in the
Euclidean product `ℂ × ℝ`. On positive radii this is `PolarGraph.graph` with the codomain
transported to `WithLp 2 (ℂ × ℝ)` and the height restricted to `PolarPoint`. -/
def graphOfProd (h : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : WithLp 2 (ℂ × ℝ) :=
  WithLp.toLp 2 (Complex.polarCoord.symm q, h q)

/-- Evaluation of the graph on a radius-angle pair. -/
@[simp] theorem graphOfProd_apply (h : ℝ × ℝ → ℝ) (q : ℝ × ℝ) :
    graphOfProd h q = WithLp.toLp 2 (Complex.polarCoord.symm q, h q) := (rfl)

/-- On positive radii, forgetting the Euclidean product norm recovers the graph on the cover. -/
-- Rewrite before graphOfProd_apply expands the inner graph into Cartesian coordinates.
@[simp↓] theorem ofLp_graphOfProd_val (h : ℝ × ℝ → ℝ) (p : PolarPoint) :
    WithLp.ofLp (graphOfProd h p.val) = graph (h ∘ Subtype.val) p := by
  simp [graphOfProd_apply, graph_def, projection_def, Complex.polarCoord_symm_apply,
    Circle.coe_exp, Complex.exp_mul_I, radius_def, angle_def]

/-- The graph is the pair of the polar projection and height, transported to the Euclidean
product by its continuous linear equivalence. -/
theorem graphOfProd_eq_comp (h : ℝ × ℝ → ℝ) :
    graphOfProd h = (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℝ).symm ∘
      (fun q ↦ (Complex.polarCoord.symm q, h q)) := by
  funext q
  simp

/-- The differential of the graph pairs the polar-coordinate differential with that of
the height. -/
theorem fderiv_graphOfProd {h : ℝ × ℝ → ℝ} {q : ℝ × ℝ} (hh : DifferentiableAt ℝ h q)
    (v : ℝ × ℝ) : fderiv ℝ (graphOfProd h) q v =
      WithLp.toLp 2 (Complex.equivRealProdCLM.symm (fderivPolarCoordSymm q v), fderiv ℝ h q v) := by
  have hπ : HasFDerivAt Complex.polarCoord.symm
      (Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp (fderivPolarCoordSymm q)) q := by
    simpa only [zero_add] using hasFDerivAt_add_polarCoord_symm q 0
  rw [graphOfProd_eq_comp]
  have hD := (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℝ).symm.hasFDerivAt.comp q
    (hπ.prodMk hh.hasFDerivAt)
  simp only [Function.comp_def] at hD ⊢
  rw [hD.fderiv]
  simp

/-- The Gram matrix of the actual graph differential on the radial and angular coordinate
vectors, in that order. -/
def gram (h : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.gram ℝ (fun i ↦ fderiv ℝ (graphOfProd h) q (![(1, 0), (0, 1)] i))

/-- Each Gram entry is the inner product of the graph differential on the corresponding
radial or angular coordinate vectors, without a differentiability assumption. -/
@[simp] theorem gram_apply (h : ℝ × ℝ → ℝ) (q : ℝ × ℝ) (i j : Fin 2) :
    gram h q i j =
      ⟪fderiv ℝ (graphOfProd h) q (![(1, 0), (0, 1)] i),
        fderiv ℝ (graphOfProd h) q (![(1, 0), (0, 1)] j)⟫_ℝ := (rfl)

/-- The first fundamental form in the radius and angle coordinates. The mixed entry is the
product of the height derivatives since the planar radial and angular velocities are orthogonal. -/
theorem gram_eq {h : ℝ × ℝ → ℝ} {q : ℝ × ℝ} (hh : DifferentiableAt ℝ h q) :
    gram h q =
      !![1 + (fderiv ℝ h q (1, 0)) ^ 2, fderiv ℝ h q (1, 0) * fderiv ℝ h q (0, 1);
         fderiv ℝ h q (1, 0) * fderiv ℝ h q (0, 1), q.1 ^ 2 + (fderiv ℝ h q (0, 1)) ^ 2] := by
  have horth : ⟪Complex.exp (q.2 * Complex.I), circleMap 0 q.1 q.2 * Complex.I⟫_ℝ = 0 := by
    rw [circleMap_zero, mul_assoc,
      ← Complex.real_smul (x := q.1), real_inner_smul_right]
    simpa only [smul_eq_mul, RCLike.I_to_complex, mul_comm, mul_zero] using
      congrArg (q.1 * ·) (real_inner_I_smul_self ℂ (Complex.exp (q.2 * Complex.I)))
  ext i j
  simp only [gram_apply, fderiv_graphOfProd hh,
    WithLp.prod_inner_apply, Real.inner_apply]
  fin_cases i <;> fin_cases j <;>
    simp [equivRealProd_symm_fderivPolarCoordSymm_apply_one_zero,
      equivRealProd_symm_fderivPolarCoordSymm_apply_zero_one, horth, real_inner_comm] <;> ring

/-- The Gram determinant of a polar graph at a point of differentiability of the height. -/
theorem det_gram {h : ℝ × ℝ → ℝ} {q : ℝ × ℝ} (hh : DifferentiableAt ℝ h q) :
    (gram h q).det =
      q.1 ^ 2 * (1 + (fderiv ℝ h q (1, 0)) ^ 2) + (fderiv ℝ h q (0, 1)) ^ 2 := by
  rw [gram_eq hh, Matrix.det_fin_two_of]
  ring

/-- Away from the axis the area density factors into the polar Jacobian and the graph factor
in the unit radial and angular directions. -/
theorem sqrt_det_gram {h : ℝ × ℝ → ℝ} {q : ℝ × ℝ} (hh : DifferentiableAt ℝ h q)
    (hr : q.1 ≠ 0) :
    √(gram h q).det =
      |q.1| * √(1 + (fderiv ℝ h q (1, 0)) ^ 2 + (fderiv ℝ h q (0, 1) / q.1) ^ 2) := by
  rw [det_gram hh, ← Real.sqrt_sq_eq_abs q.1, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  field_simp

/-- For a Cartesian height germ in a translated polar chart, the area density is the absolute
polar Jacobian times the Cartesian graph area factor, including on the axis. -/
theorem sqrt_det_gram_eq_cartesian {f : ℂ → ℝ} {h : ℝ × ℝ → ℝ} (z₀ : ℂ)
    (q : ℝ × ℝ) (hf : DifferentiableAt ℝ f (z₀ + Complex.polarCoord.symm q))
    (he : h =ᶠ[𝓝 q] fun t ↦ f (z₀ + Complex.polarCoord.symm t)) :
    √(gram h q).det = |q.1| * √(1 + ‖∇ f (z₀ + Complex.polarCoord.symm q)‖ ^ 2) := by
  have hd := hf.comp q (hasFDerivAt_add_polarCoord_symm q z₀).differentiableAt
  have hh := hd.congr_of_eventuallyEq he
  rw [det_gram hh, ← Real.sqrt_sq_eq_abs q.1, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  linear_combination -sq_radius_mul_norm_gradient_sq z₀ q hf he

end TauCeti.PolarGraph

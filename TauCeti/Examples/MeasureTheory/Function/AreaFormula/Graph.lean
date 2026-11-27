/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AreaFormula.Graph
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Checks for the area of graphs in every codimension

* *The diagonal plane in `ℝ⁴`.* The graph of the identity of `ℝ²` is the plane `{(x, x)}` in
  `ℝ² × ℝ² = ℝ⁴`. The map `x ↦ (x, x)` has `√det(I + I* I) = √det(2 I) = 2`, so it doubles areas:
  the graph over a measurable `s` has `H²` measure `2 |s|`
  (`euclideanHausdorffMeasure_graph_id_image`). The codimension-one factor `√(1 + ‖A‖²)` with the
  operator norm `‖I‖ = 1` would give `√2` instead (`sqrt_one_add_norm_id_sq`).
* *Lipschitz graphs over an interval.* For a Lipschitz `φ : ℝ → ℝ`, the graph `x ↦ (x, φ x)` over
  `[a, b]` has `H¹` measure `∫_{[a, b]} √(1 + φ'(x)²) dx`, the integral over the set `[a, b]`
  (`euclideanHausdorffMeasure_graph_image_Icc`), since on `ℝ` the integrand `√det(1 + A* A)`,
  the Jacobian of `t ↦ (t, A t)`, is the norm `√(1 + (A 1)²)` of the image of `1`.
-/

public section

noncomputable section

namespace TauCeti.Examples.AreaFormulaGraph

open MeasureTheory Module Set

open scoped ENNReal NNReal

/-- **The diagonal plane `{(x, x)}` in `ℝ⁴` doubles areas**: for measurable `s ⊆ ℝ²`, the graph
of the identity over `s` has two-dimensional Hausdorff measure `2 |s|`. -/
theorem euclideanHausdorffMeasure_graph_id_image {s : Set (EuclideanSpace ℝ (Fin 2))}
    (hs : MeasurableSet s) :
    μHE[2] ((fun x ↦ WithLp.toLp 2 (x, x)) '' s) = 2 * volume s := by
  have h := LipschitzWith.id.euclideanHausdorffMeasure_graph_image (φ := id) hs
  rw [finrank_euclideanSpace_fin] at h
  refine h.trans ?_
  rw [show (2 : ℝ≥0∞) * volume s = ∫⁻ _ in s, 2 by simp]
  refine setLIntegral_congr_fun hs fun x _ => ?_
  rw [fderiv_id, ← ContinuousLinearMap.normDet_graphL,
    ContinuousLinearMap.normDet_graphL_id_of_finrank_eq_two finrank_euclideanSpace_fin]
  simp

/-- The codimension-one factor `√(1 + ‖A‖²)` with the operator norm gives `√2` for the identity of
`ℝ²`, not the area factor `2`. -/
theorem sqrt_one_add_norm_id_sq :
    Real.sqrt (1 + ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))‖ ^ 2) = Real.sqrt 2 := by
  rw [ContinuousLinearMap.norm_id]
  norm_num

/-- **The length of a Lipschitz graph over an interval**: for a Lipschitz `φ : ℝ → ℝ`, the graph
`x ↦ (x, φ x)` over `[a, b]` has one-dimensional Hausdorff measure `∫_{[a, b]} √(1 + φ'(x)²) dx`,
the integral over the set `[a, b]` (both sides vanish when `b < a`). -/
theorem euclideanHausdorffMeasure_graph_image_Icc {K : ℝ≥0} {φ : ℝ → ℝ} (hφ : LipschitzWith K φ)
    (a b : ℝ) :
    μHE[1] ((fun x ↦ WithLp.toLp 2 (x, φ x)) '' Icc a b) =
      ∫⁻ x in Icc a b, ENNReal.ofReal (Real.sqrt (1 + deriv φ x ^ 2)) := by
  have h := hφ.euclideanHausdorffMeasure_graph_image (measurableSet_Icc (a := a) (b := b))
  rw [finrank_self] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  rw [← ContinuousLinearMap.normDet_graphL, LinearMap.normDet_eq_norm_apply_one,
    WithLp.prod_norm_eq_of_L2]
  simp

end TauCeti.Examples.AreaFormulaGraph

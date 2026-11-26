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
  `[a, b]` has `H¹` measure `∫_a^b √(1 + φ'(x)²) dx` (`euclideanHausdorffMeasure_graph_image_Icc`),
  since on `ℝ` the integrand `√det(1 + A* A)` is `√(1 + (A 1)²)`
  (`det_one_add_adjoint_comp_self_real`).
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
  simp only [finrank_euclideanSpace_fin, id_eq] at h
  rw [h]
  have hdet : ∀ x : EuclideanSpace ℝ (Fin 2), Real.sqrt (LinearMap.det
      (1 + LinearMap.adjoint (fderiv ℝ (id : EuclideanSpace ℝ (Fin 2) → _) x :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) ∘ₗ
        (fderiv ℝ (id : EuclideanSpace ℝ (Fin 2) → _) x :
          EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)))) = 2 := by
    intro x
    have h2 : (1 + LinearMap.id : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) =
        (2 : ℝ) • 1 := by
      rw [two_smul]
      rfl
    simp only [fderiv_id, ContinuousLinearMap.coe_id, LinearMap.adjoint_id, LinearMap.id_comp, h2,
      LinearMap.det_smul, map_one, finrank_euclideanSpace_fin, mul_one]
    exact Real.sqrt_sq zero_le_two
  simp only [hdet, setLIntegral_const, ENNReal.ofReal_ofNat]

/-- The codimension-one factor `√(1 + ‖A‖²)` with the operator norm gives `√2` for the identity of
`ℝ²`, not the area factor `2`. -/
theorem sqrt_one_add_norm_id_sq :
    Real.sqrt (1 + ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))‖ ^ 2) = Real.sqrt 2 := by
  rw [ContinuousLinearMap.norm_id]
  norm_num

/-- On `ℝ`, `det (1 + A* A) = 1 + (A 1) ^ 2`. -/
theorem det_one_add_adjoint_comp_self_real (A : ℝ →ₗ[ℝ] ℝ) :
    LinearMap.det (1 + LinearMap.adjoint A ∘ₗ A) = 1 + A 1 ^ 2 := by
  have hA : LinearMap.adjoint A (A 1) = A 1 ^ 2 := by
    have := LinearMap.adjoint_inner_left A (A 1) 1
    simp only [RCLike.inner_apply, conj_trivial] at this
    have hlin : ∀ (f : ℝ →ₗ[ℝ] ℝ) (y : ℝ), f y = y * f 1 := fun f y => by
      rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    rw [hlin (LinearMap.adjoint A), this, mul_one, hlin A (A 1), sq]
  rw [LinearMap.det_ring]
  simp [hA]

/-- **The length of a Lipschitz graph over an interval**: for a Lipschitz `φ : ℝ → ℝ`, the graph
`x ↦ (x, φ x)` over `[a, b]` has one-dimensional Hausdorff measure `∫_a^b √(1 + φ'(x)²) dx`. -/
theorem euclideanHausdorffMeasure_graph_image_Icc {K : ℝ≥0} {φ : ℝ → ℝ} (hφ : LipschitzWith K φ)
    (a b : ℝ) :
    μHE[1] ((fun x ↦ WithLp.toLp 2 (x, φ x)) '' Icc a b) =
      ∫⁻ x in Icc a b, ENNReal.ofReal (Real.sqrt (1 + deriv φ x ^ 2)) := by
  have h := hφ.euclideanHausdorffMeasure_graph_image (measurableSet_Icc (a := a) (b := b))
  rw [finrank_self] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  rw [det_one_add_adjoint_comp_self_real]
  simp

end TauCeti.Examples.AreaFormulaGraph

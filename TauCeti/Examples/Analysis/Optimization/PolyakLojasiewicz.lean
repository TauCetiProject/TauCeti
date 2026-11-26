/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.InnerProductSpace.SingularValues.Planar
import TauCeti.Analysis.Optimization.PolyakLojasiewicz.LeastSquares

/-!
# Examples of the Polyak–Łojasiewicz condition

The half square and a rank-one least-squares problem both have sharp modulus one.
The exponential has infimum zero but fails gradient domination for every positive modulus.
-/

open TauCeti Matrix Set
open scoped Gradient

/-- The normalization gives the half square sharp modulus one. -/
example {μ : ℝ} : PolyakLojasiewicz μ (fun x : ℝ ↦ x ^ 2 / 2) ↔ μ ≤ 1 := by
  have h := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).polyakLojasiewicz_leastSquares_iff 0 (μ := μ)
  rw [LinearMap.singularValues_eq_single_of_finrank_eq_one _ (by simp) (x := (1 : ℝ))
    (by simp)] at h
  simpa [Real.norm_eq_abs, sq_abs, Finsupp.single_apply, apply_ite] using h

/-- For the projection with matrix `diag(1,0)` and data equal to the second basis vector,
the least-squares modulus one remains sharp despite the nonzero residual at the minimum. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (e : OrthonormalBasis (Fin 2) ℝ E) {μ : ℝ} :
    PolyakLojasiewicz μ
      (fun x ↦ ‖toLin e.toBasis e.toBasis (diagonal ![1, 0]) x - e 1‖ ^ 2 / 2) ↔ μ ≤ 1 := by
  rw [LinearMap.polyakLojasiewicz_leastSquares_iff,
    singularValues_toLin_diagonal_fin_two e (by norm_num)]
  simp [Finsupp.single_apply, apply_ite]

/-- The exponential at `log μ` rules out gradient domination with positive modulus `μ`. -/
example {μ : ℝ} (hμ : 0 < μ) : ¬ PolyakLojasiewicz μ Real.exp := by
  intro h
  have hgap := h.le (Real.log μ)
  rw [gradient_eq_deriv', Real.deriv_exp, iInf, Real.range_exp, csInf_Ioi,
    Real.exp_log hμ, Real.norm_of_nonneg hμ.le] at hgap
  nlinarith [sq_pos_of_pos hμ]

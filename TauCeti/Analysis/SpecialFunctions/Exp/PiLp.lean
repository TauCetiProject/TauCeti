/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Coordinatewise exponential and logarithmic Jacobians

On finite real Euclidean spaces, coordinatewise exponentiation has diagonal derivative with
entries `exp (x i)`. Coordinatewise logarithms have diagonal derivative with entries `(x i)⁻¹`
where the coordinates are nonzero. Their determinant formulas provide the Jacobian factors
for transporting densities between Euclidean space and the positive orthant.
Coordinatewise exponentiation is injective with range the positive orthant.
-/

public section

noncomputable section

open scoped ENNReal

namespace PiLp

/-- Coordinatewise real exponentiation is injective. -/
theorem exp_injective (p : ℝ≥0∞) {ι : Type*} :
    Function.Injective (fun x : PiLp p (fun _ : ι ↦ ℝ) ↦
      WithLp.toLp p (fun i ↦ Real.exp (x i))) := by
  intro x y h
  ext i
  exact Real.exp_injective (congrArg (fun z : PiLp p (fun _ : ι ↦ ℝ) ↦ z i) h)

/-- The range of coordinatewise real exponentiation is the positive orthant. -/
@[simp]
theorem range_exp (p : ℝ≥0∞) {ι : Type*} :
    Set.range (fun x : PiLp p (fun _ : ι ↦ ℝ) ↦ WithLp.toLp p (fun i ↦ Real.exp (x i))) =
      {x | ∀ i, 0 < x i} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact fun i ↦ Real.exp_pos (y i)
  · intro hx
    refine ⟨WithLp.toLp p (fun i ↦ Real.log (x i)), ?_⟩
    ext i
    exact Real.exp_log (hx i)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The derivative of coordinatewise exponentiation is the diagonal matrix of exponentials. -/
theorem hasFDerivAt_exp (x : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun y : EuclideanSpace ℝ ι ↦ WithLp.toLp 2 (fun i ↦ Real.exp (y i)))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (fun i ↦ Real.exp (x i)))) x := by
  refine ((hasStrictFDerivAt_piLp (𝕜 := ℝ) 2).mpr ?_).hasFDerivAt
  intro i
  convert (PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 x i).exp using 1
  ext y
  simp [ContinuousLinearMap.comp_apply, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

omit [DecidableEq ι] in
/-- The Jacobian determinant of coordinatewise exponentiation. -/
@[simp]
theorem det_fderiv_exp (x : EuclideanSpace ℝ ι) :
    (fderiv ℝ (fun y : EuclideanSpace ℝ ι ↦ WithLp.toLp 2 (fun i ↦ Real.exp (y i))) x).det =
      ∏ i, Real.exp (x i) := by
  classical
  rw [(hasFDerivAt_exp x).fderiv, Matrix.det_toEuclideanCLM_diagonal]

/-- The derivative of coordinatewise logarithms where every coordinate is nonzero. -/
theorem hasFDerivAt_log (x : EuclideanSpace ℝ ι) (hx : ∀ i, x i ≠ 0) :
    HasFDerivAt (fun y : EuclideanSpace ℝ ι ↦ WithLp.toLp 2 (fun i ↦ Real.log (y i)))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (fun i ↦ (x i)⁻¹))) x := by
  refine ((hasStrictFDerivAt_piLp (𝕜 := ℝ) 2).mpr ?_).hasFDerivAt
  intro i
  convert (PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 x i).log (hx i) using 1
  ext y
  simp [ContinuousLinearMap.comp_apply, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

omit [DecidableEq ι] in
/-- The Jacobian determinant of coordinatewise logarithms is the reciprocal coordinate product. -/
@[simp]
theorem det_fderiv_log (x : EuclideanSpace ℝ ι) (hx : ∀ i, x i ≠ 0) :
    (fderiv ℝ (fun y : EuclideanSpace ℝ ι ↦ WithLp.toLp 2 (fun i ↦ Real.log (y i))) x).det =
      (∏ i, x i)⁻¹ := by
  classical
  rw [(hasFDerivAt_log x hx).fderiv, Matrix.det_toEuclideanCLM_diagonal, Finset.prod_inv_distrib]

end PiLp

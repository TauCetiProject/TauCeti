/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.Calculus.Morse.Linearization
public import TauCeti.Analysis.Distribution.TestFunction.Divergence
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Trace

/-!
# The Euclidean minimal graph operator

For a twice differentiable function on a finite-dimensional Euclidean space, the divergence of
its normalized gradient is a positive multiple of the nondivergence minimal graph operator.
This file establishes the equivalence pointwise. No minimality assertion is used here.

## References

* T. H. Colding and W. Minicozzi II, *A course in minimal surfaces*, Section 1.1.
* O. Chodosh, *Introduction to minimal surfaces*, Section 18.
-/

public noncomputable section

open scoped Gradient Laplacian

namespace TauCeti.MinimalGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The reciprocal area density of a Euclidean graph. -/
def areaWeight (u : E → ℝ) (x : E) : ℝ :=
  (1 + ‖∇ u x‖ ^ 2) ^ (-(1 / 2 : ℝ))

/-- The area weight is the reciprocal of the Euclidean graph area density. -/
theorem areaWeight_eq_inv_sqrt (u : E → ℝ) (x : E) :
    areaWeight u x = (Real.sqrt (1 + ‖∇ u x‖ ^ 2))⁻¹ := by
  rw [areaWeight, Real.sqrt_eq_rpow,
    ← Real.rpow_neg (by positivity : 0 ≤ 1 + ‖∇ u x‖ ^ 2)]

@[simp]
theorem areaWeight_def (u : E → ℝ) (x : E) :
    areaWeight u x = (1 + ‖∇ u x‖ ^ 2) ^ (-(1 / 2 : ℝ)) := (rfl)

/-- The graph area weight is strictly positive. -/
theorem areaWeight_pos (u : E → ℝ) (x : E) : 0 < areaWeight u x := by
  unfold areaWeight
  positivity

/-- The normalized gradient whose divergence is the minimal graph equation. -/
def areaFlux (u : E → ℝ) (x : E) : E := areaWeight u x • ∇ u x

@[simp]
theorem areaFlux_apply (u : E → ℝ) (x : E) :
    areaFlux u x = areaWeight u x • ∇ u x := (rfl)

/-- The divergence of the normalized gradient, as the trace of its Fréchet derivative. -/
def fluxDivergence (u : E → ℝ) (x : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ (areaFlux u) x).toLinearMap

theorem fluxDivergence_def (u : E → ℝ) (x : E) :
    fluxDivergence u x = LinearMap.trace ℝ E (fderiv ℝ (areaFlux u) x).toLinearMap := (rfl)

private theorem areaWeight_deriv {u : E → ℝ} {x : E}
    (hgrad : DifferentiableAt ℝ (∇ u) x) (v : E) :
    fderiv ℝ (areaWeight u) x v =
      -(1 + ‖∇ u x‖ ^ 2) ^ (-(3 / 2 : ℝ)) *
        inner ℝ (∇ u x) (fderiv ℝ (∇ u) x v) := by
  have hs : HasFDerivAt (fun (y : E) ↦ 1 + ‖∇ u y‖ ^ 2)
      (2 • (innerSL ℝ (∇ u x)) ∘SL fderiv ℝ (∇ u) x) x := by
    exact (hgrad.hasFDerivAt.norm_sq).const_add 1
  have hpos : 0 < 1 + ‖∇ u x‖ ^ 2 := by positivity
  have hw := hs.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hpos.ne')
  have heq := congrArg (fun (L : E →L[ℝ] ℝ) ↦ L v) hw.fderiv
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    innerSL_apply_apply, mul_assoc] at heq
  rw [funext (areaWeight_def u)]
  rw [heq]
  norm_num only
  ring

private theorem differentiableAt_areaWeight {u : E → ℝ} {x : E}
    (hgrad : DifferentiableAt ℝ (∇ u) x) : DifferentiableAt ℝ (areaWeight u) x := by
  have hs : DifferentiableAt ℝ (fun y : E ↦ 1 + ‖∇ u y‖ ^ 2) x :=
    (hgrad.hasFDerivAt.norm_sq).differentiableAt.const_add 1
  have hpos : 0 < 1 + ‖∇ u x‖ ^ 2 := by positivity
  exact hs.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hpos.ne')

/-- The nondivergence minimal graph operator in basis-free form. -/
def nondivergenceOperator (u : E → ℝ) (x : E) : ℝ :=
  (1 + ‖∇ u x‖ ^ 2) *
      LinearMap.trace ℝ E (fderiv ℝ (∇ u) x).toLinearMap -
    inner ℝ (∇ u x) (fderiv ℝ (∇ u) x (∇ u x))

/-- The trace formula defining the nondivergence minimal graph operator. -/
theorem nondivergenceOperator_def (u : E → ℝ) (x : E) :
    nondivergenceOperator u x = (1 + ‖∇ u x‖ ^ 2) *
      LinearMap.trace ℝ E (fderiv ℝ (∇ u) x).toLinearMap -
        inner ℝ (∇ u x) (fderiv ℝ (∇ u) x (∇ u x)) := (rfl)

/-- The divergence form is a positive multiple of the nondivergence form. -/
theorem fluxDivergence_eq_rpow_mul_nondivergenceOperator {u : E → ℝ} {x : E}
    (hgrad : DifferentiableAt ℝ (∇ u) x) :
    fluxDivergence u x =
      (1 + ‖∇ u x‖ ^ 2) ^ (-(3 / 2 : ℝ)) * nondivergenceOperator u x := by
  let s : ℝ := 1 + ‖∇ u x‖ ^ 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hpow : s ^ (-(1 / 2 : ℝ)) = s * s ^ (-(3 / 2 : ℝ)) := by
    calc
      _ = s ^ (1 + -(3 / 2 : ℝ)) := by congr 1; ring
      _ = s ^ 1 * s ^ (-(3 / 2 : ℝ)) := Real.rpow_add hs 1 _
      _ = _ := by simp
  rw [fluxDivergence_def, funext (areaFlux_apply u)]
  rw [TauCeti.trace_fderiv_smul (differentiableAt_areaWeight hgrad) hgrad,
    areaWeight_deriv hgrad]
  rw [areaWeight, nondivergenceOperator]
  dsimp only [s] at hpow
  rw [hpow]
  ring

/-- The two Euclidean minimal graph equations have the same solutions at a point. -/
theorem fluxDivergence_eq_zero_iff {u : E → ℝ} {x : E}
    (hgrad : DifferentiableAt ℝ (∇ u) x) :
    fluxDivergence u x = 0 ↔ nondivergenceOperator u x = 0 := by
  have hfactor : (1 + ‖∇ u x‖ ^ 2) ^ (-(3 / 2 : ℝ)) ≠ 0 := by positivity
  rw [fluxDivergence_eq_rpow_mul_nondivergenceOperator hgrad]
  simp only [mul_eq_zero, hfactor, false_or]

/-- The nondivergence equation is `(1+|Du|²) Δu - D²u(Du,Du)`. -/
theorem nondivergenceOperator_eq (u : E → ℝ) (x : E) :
    nondivergenceOperator u x = (1 + ‖∇ u x‖ ^ 2) * Δ u x -
      fderiv ℝ (fderiv ℝ u) x (∇ u x) (∇ u x) := by
  rw [nondivergenceOperator, TauCeti.laplacian_eq_trace_iteratedGradientChain_one,
    TauCeti.iteratedGradientChain_succ, TauCeti.iteratedGradientChain_zero]
  congr 1
  rw [TauCeti.fderiv_gradient, real_inner_comm]
  exact TauCeti.inner_hessianOperator_left u x (∇ u x) (∇ u x)

end TauCeti.MinimalGraph

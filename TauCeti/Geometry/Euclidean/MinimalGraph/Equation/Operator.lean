/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.Calculus.Gradient
public import Mathlib.LinearAlgebra.Trace
import TauCeti.Analysis.Calculus.Morse.Linearization
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.Analysis.InnerProductSpace.Laplacian.Trace

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

open scoped Gradient Laplacian Topology

namespace TauCeti.MinimalGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Hilbert

variable [CompleteSpace E]

/-- The reciprocal area density of a Euclidean graph. -/
def areaWeight (u : E → ℝ) (x : E) : ℝ :=
  (1 + ‖∇ u x‖ ^ 2) ^ (-(1 / 2 : ℝ))

/-- The area weight is the reciprocal of the Euclidean graph area density. -/
theorem areaWeight_eq_inv_sqrt (u : E → ℝ) (x : E) :
    areaWeight u x = (Real.sqrt (1 + ‖∇ u x‖ ^ 2))⁻¹ := by
  rw [areaWeight, Real.sqrt_eq_rpow,
    ← Real.rpow_neg (by positivity : 0 ≤ 1 + ‖∇ u x‖ ^ 2)]

theorem areaWeight_def (u : E → ℝ) (x : E) :
    areaWeight u x = (1 + ‖∇ u x‖ ^ 2) ^ (-(1 / 2 : ℝ)) := (rfl)

/-- The graph area weight is strictly positive. -/
theorem areaWeight_pos (u : E → ℝ) (x : E) : 0 < areaWeight u x := by
  unfold areaWeight
  positivity

/-- The normalized gradient whose divergence is the minimal graph equation. -/
def areaFlux (u : E → ℝ) (x : E) : E := areaWeight u x • ∇ u x

theorem areaFlux_apply (u : E → ℝ) (x : E) :
    areaFlux u x = areaWeight u x • ∇ u x := (rfl)

/-- The derivative of reciprocal graph area density in terms of the differentiated gradient. -/
theorem hasFDerivAt_areaWeight {u : E → ℝ} {x : E}
    (hgrad : DifferentiableAt ℝ (∇ u) x) :
    HasFDerivAt (areaWeight u)
      ((-(1 + ‖∇ u x‖ ^ 2) ^ (-(3 / 2 : ℝ)) • innerSL ℝ (∇ u x)).comp
        (fderiv ℝ (∇ u) x)) x := by
  have h := (TauCeti.hasStrictFDerivAt_one_add_norm_sq_rpow (-(1 / 2 : ℝ))
    (∇ u x)).hasFDerivAt.comp x hgrad.hasFDerivAt
  norm_num only at h
  rw [funext (areaWeight_def u)]
  simpa [Function.comp_def, neg_smul, smul_smul] using h

/-- The area weight is differentiable wherever the gradient is differentiable. -/
theorem differentiableAt_areaWeight {u : E → ℝ} {x : E}
    (hgrad : DifferentiableAt ℝ (∇ u) x) : DifferentiableAt ℝ (areaWeight u) x :=
  (hasFDerivAt_areaWeight hgrad).differentiableAt

/-- The derivative of the normalized gradient is given by the scalar product rule. -/
theorem hasFDerivAt_areaFlux {u : E → ℝ} {x : E}
    (hgrad : DifferentiableAt ℝ (∇ u) x) :
    HasFDerivAt (areaFlux u)
      (areaWeight u x • fderiv ℝ (∇ u) x +
        (((-(1 + ‖∇ u x‖ ^ 2) ^ (-(3 / 2 : ℝ)) • innerSL ℝ (∇ u x)).comp
          (fderiv ℝ (∇ u) x)).smulRight (∇ u x))) x :=
  (hasFDerivAt_areaWeight hgrad).smul hgrad.hasFDerivAt

/-- The normalized gradient is differentiable wherever the gradient is differentiable. -/
theorem differentiableAt_areaFlux {u : E → ℝ} {x : E}
    (hgrad : DifferentiableAt ℝ (∇ u) x) : DifferentiableAt ℝ (areaFlux u) x :=
  (hasFDerivAt_areaFlux hgrad).differentiableAt

/-- The reciprocal graph area density is at most one. -/
theorem areaWeight_le_one (u : E → ℝ) (x : E) : areaWeight u x ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (sq_nonneg _)) (by norm_num)

/-- The normalized graph flux has norm strictly less than one. -/
theorem norm_areaFlux_lt_one (u : E → ℝ) (x : E) : ‖areaFlux u x‖ < 1 := by
  rw [areaFlux_apply, norm_smul, Real.norm_of_nonneg (areaWeight_pos u x).le,
    areaWeight_eq_inv_sqrt, inv_mul_eq_div, div_lt_one (by positivity)]
  exact (Real.lt_sqrt (norm_nonneg _)).2 (by linarith)

/-- The area weight depends only on the germ of the height. -/
theorem areaWeight_congr_of_eventuallyEq {u v : E → ℝ} {x : E} (h : u =ᶠ[𝓝 x] v) :
    areaWeight u x = areaWeight v x := by
  rw [areaWeight_def, areaWeight_def, h.gradient_eq]

/-- The graph flux depends only on the germ of the height. -/
theorem areaFlux_congr_of_eventuallyEq {u v : E → ℝ} {x : E} (h : u =ᶠ[𝓝 x] v) :
    areaFlux u x = areaFlux v x := by
  rw [areaFlux_apply, areaFlux_apply, areaWeight_congr_of_eventuallyEq h, h.gradient_eq]

/-- A constant height has unit reciprocal area density. -/
@[simp] theorem areaWeight_const (c : ℝ) (x : E) : areaWeight (fun _ ↦ c) x = 1 := by
  simp [areaWeight_def, gradient_fun_const]

/-- A constant height has zero normalized gradient. -/
@[simp] theorem areaFlux_const (c : ℝ) (x : E) : areaFlux (fun _ ↦ c) x = 0 := by
  simp [areaFlux_apply, gradient_fun_const]

/-- Vertical translation preserves reciprocal area density. -/
@[simp] theorem areaWeight_add_const (u : E → ℝ) (c : ℝ) (x : E) :
    areaWeight (fun y ↦ u y + c) x = areaWeight u x := by
  simp [areaWeight_def, gradient, fderiv_add_const]

/-- Vertical translation preserves normalized gradient. -/
@[simp] theorem areaFlux_add_const (u : E → ℝ) (c : ℝ) (x : E) :
    areaFlux (fun y ↦ u y + c) x = areaFlux u x := by
  simp [areaFlux_apply, gradient, fderiv_add_const]

/-- Negating the height preserves reciprocal area density. -/
@[simp] theorem areaWeight_neg (u : E → ℝ) (x : E) : areaWeight (-u) x = areaWeight u x := by
  simp [areaWeight_def, TauCeti.gradient_neg]

/-- Negating the height negates normalized gradient. -/
@[simp] theorem areaFlux_neg (u : E → ℝ) (x : E) : areaFlux (-u) x = -areaFlux u x := by
  simp [areaFlux_apply, TauCeti.gradient_neg]

end Hilbert

variable [FiniteDimensional ℝ E]

/-- The divergence of the normalized gradient, as the trace of its Fréchet derivative. -/
def fluxDivergence (u : E → ℝ) (x : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ (areaFlux u) x).toLinearMap

theorem fluxDivergence_def (u : E → ℝ) (x : E) :
    fluxDivergence u x = LinearMap.trace ℝ E (fderiv ℝ (areaFlux u) x).toLinearMap := (rfl)

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

/-- Flux divergence depends only on the germ of the height. -/
theorem fluxDivergence_congr_of_eventuallyEq {u v : E → ℝ} {x : E}
    (h : u =ᶠ[𝓝 x] v) : fluxDivergence u x = fluxDivergence v x := by
  have hf : areaFlux u =ᶠ[𝓝 x] areaFlux v :=
    h.eventuallyEq_nhds.mono fun _ hy ↦ areaFlux_congr_of_eventuallyEq hy
  rw [fluxDivergence_def, fluxDivergence_def, hf.fderiv_eq]

/-- The nondivergence operator depends only on the germ of the height. -/
theorem nondivergenceOperator_congr_of_eventuallyEq {u v : E → ℝ} {x : E}
    (h : u =ᶠ[𝓝 x] v) : nondivergenceOperator u x = nondivergenceOperator v x := by
  rw [nondivergenceOperator_def, nondivergenceOperator_def, h.gradient_eq, h.gradient.fderiv_eq]

/-- Constant graphs solve the divergence equation. -/
@[simp] theorem fluxDivergence_const (c : ℝ) (x : E) : fluxDivergence (fun _ ↦ c) x = 0 := by
  simp [fluxDivergence_def, funext (areaFlux_const c)]

/-- Constant graphs solve the nondivergence equation. -/
@[simp] theorem nondivergenceOperator_const (c : ℝ) (x : E) :
    nondivergenceOperator (fun _ ↦ c) x = 0 := by
  simp [nondivergenceOperator_def, gradient_fun_const']

/-- Vertical translation preserves flux divergence. -/
@[simp] theorem fluxDivergence_add_const (u : E → ℝ) (c : ℝ) (x : E) :
    fluxDivergence (fun y ↦ u y + c) x = fluxDivergence u x := by
  simp only [fluxDivergence_def, funext (areaFlux_add_const u c)]

/-- Vertical translation preserves the nondivergence graph operator. -/
@[simp] theorem nondivergenceOperator_add_const (u : E → ℝ) (c : ℝ) (x : E) :
    nondivergenceOperator (fun y ↦ u y + c) x = nondivergenceOperator u x := by
  have hg : ∇ (fun y ↦ u y + c) = ∇ u := by
    funext y
    simp [gradient, fderiv_add_const]
  simp only [nondivergenceOperator_def, hg]

/-- Negating the height negates flux divergence. -/
@[simp] theorem fluxDivergence_neg (u : E → ℝ) (x : E) :
    fluxDivergence (-u) x = -fluxDivergence u x := by
  simp [fluxDivergence_def, funext (areaFlux_neg u), fderiv_fun_neg]

/-- Negating the height negates the nondivergence graph operator. -/
@[simp] theorem nondivergenceOperator_neg (u : E → ℝ) (x : E) :
    nondivergenceOperator (-u) x = -nondivergenceOperator u x := by
  have hg : ∇ (-u) = -∇ u := funext fun y ↦ TauCeti.gradient_neg
  rw [nondivergenceOperator_def, hg, fderiv_neg]
  simp [nondivergenceOperator_def, sub_eq_add_neg, add_comm]

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
    (hasFDerivAt_areaWeight hgrad).fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
    neg_mul]
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

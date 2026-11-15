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

/-- The graph area weight is strictly positive. -/
theorem areaWeight_pos (u : E → ℝ) (x : E) : 0 < areaWeight u x := by
  unfold areaWeight
  positivity

/-- The normalized gradient whose divergence is the minimal graph equation. -/
def areaFlux (u : E → ℝ) (x : E) : E := areaWeight u x • ∇ u x

/-- The divergence of the normalized gradient, as the trace of its Fréchet derivative. -/
def fluxDivergence (u : E → ℝ) (x : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ (areaFlux u) x).toLinearMap

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
  change (fderiv ℝ (fun y : E ↦ (1 + ‖∇ u y‖ ^ 2) ^ (-(1 / 2 : ℝ))) x) v = _
  rw [heq]
  norm_num
  ring

private theorem differentiableAt_areaWeight {u : E → ℝ} {x : E}
    (hgrad : DifferentiableAt ℝ (∇ u) x) : DifferentiableAt ℝ (areaWeight u) x := by
  have hs : DifferentiableAt ℝ (fun y : E ↦ 1 + ‖∇ u y‖ ^ 2) x :=
    (hgrad.hasFDerivAt.norm_sq).differentiableAt.const_add 1
  have hpos : 0 < 1 + ‖∇ u x‖ ^ 2 := by positivity
  exact hs.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hpos.ne')

private theorem fluxDivergence_eq {u : E → ℝ} {x : E}
    (hgrad : DifferentiableAt ℝ (∇ u) x) :
    fluxDivergence u x = areaWeight u x *
        LinearMap.trace ℝ E (fderiv ℝ (∇ u) x).toLinearMap +
      fderiv ℝ (areaWeight u) x (∇ u x) := by
  have hw := differentiableAt_areaWeight hgrad
  change LinearMap.trace ℝ E
    (fderiv ℝ (fun y : E ↦ areaWeight u y • ∇ u y) x).toLinearMap = _
  rw [fderiv_fun_smul hw hgrad]
  simp [LinearMap.trace_smulRight]

/-- The nondivergence minimal graph operator in basis-free form. -/
def nondivergenceOperator (u : E → ℝ) (x : E) : ℝ :=
  (1 + ‖∇ u x‖ ^ 2) *
      LinearMap.trace ℝ E (fderiv ℝ (∇ u) x).toLinearMap -
    inner ℝ (∇ u x) (fderiv ℝ (∇ u) x (∇ u x))

/-- The divergence form is a positive multiple of the nondivergence form. -/
theorem fluxDivergence_eq_nondivergence {u : E → ℝ} {x : E}
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
  rw [fluxDivergence_eq hgrad, areaWeight_deriv hgrad]
  rw [areaWeight, nondivergenceOperator]
  change s ^ (-(1 / 2 : ℝ)) * _ + -(s ^ (-(3 / 2 : ℝ))) * _ =
    s ^ (-(3 / 2 : ℝ)) * (s * _ - _)
  rw [hpow]
  ring

/-- The two Euclidean minimal graph equations have the same solutions at a point. -/
theorem fluxDivergence_eq_zero_iff {u : E → ℝ} {x : E}
    (hgrad : DifferentiableAt ℝ (∇ u) x) :
    fluxDivergence u x = 0 ↔ nondivergenceOperator u x = 0 := by
  have hfactor : (1 + ‖∇ u x‖ ^ 2) ^ (-(3 / 2 : ℝ)) ≠ 0 := by positivity
  rw [fluxDivergence_eq_nondivergence hgrad]
  simp only [mul_eq_zero, hfactor, false_or]

/-- The trace of the derivative of the Euclidean gradient is the flat Laplacian. -/
theorem trace_fderiv_gradient_eq_laplacian (u : E → ℝ) (x : E) :
    LinearMap.trace ℝ E (fderiv ℝ (∇ u) x).toLinearMap = Δ u x := by
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner _ b,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm, TauCeti.fderiv_gradient]
  change inner ℝ (TauCeti.hessianOperator u x (b i)) (b i) = _
  rw [TauCeti.inner_hessianOperator_left]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The nondivergence equation is `(1+|Du|²) Δu - D²u(Du,Du)`. -/
theorem nondivergenceOperator_eq (u : E → ℝ) (x : E) :
    nondivergenceOperator u x = (1 + ‖∇ u x‖ ^ 2) * Δ u x -
      fderiv ℝ (fderiv ℝ u) x (∇ u x) (∇ u x) := by
  rw [nondivergenceOperator, trace_fderiv_gradient_eq_laplacian,
    TauCeti.fderiv_gradient]
  congr 1
  rw [real_inner_comm]
  change inner ℝ (TauCeti.hessianOperator u x (∇ u x)) (∇ u x) = _
  exact TauCeti.inner_hessianOperator_left u x (∇ u x) (∇ u x)

end TauCeti.MinimalGraph

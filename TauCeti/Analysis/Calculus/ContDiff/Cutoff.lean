/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.Algebra.Support

/-!
# Cutting off a map that is smooth on an open set

Multiplying a map `u` that is `C^n` on an open set `W` by a scalar cutoff `g` that is `C^n` near
every point of a set `U` and vanishes near every point of `U` outside `W` gives a map that is
`C^n` on all of `U` (`TauCeti.contDiffOn_smul_of_eventuallyEq_zero`). This is how a map defined
on a punctured domain is extended across a puncture by a cutoff vanishing near it.

The cutoff perturbation `x ↦ x + χ x • (f x - x)` is `C^n` when `f` is `C^n` near
`tsupport χ`. Its derivative error is controlled by the value and derivative errors of `f`.

## References

* [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Filter
open scoped Topology

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞}

/-- Multiplying a map that is `C^n` on an open set `W` by a cutoff that is `C^n` at every point of
a set `U` and vanishes near every point of `U` outside `W` gives a map that is `C^n` on `U`. -/
theorem contDiffOn_smul_of_eventuallyEq_zero {U W : Set E} (hW : IsOpen W) {g : E → 𝕜}
    {u : E → F} (hg : ∀ z ∈ U, ContDiffAt 𝕜 n g z) (hu : ContDiffOn 𝕜 n u W)
    (h : ∀ z ∈ U, z ∉ W → g =ᶠ[𝓝 z] fun _ ↦ 0) :
    ContDiffOn 𝕜 n (fun z ↦ g z • u z) U := by
  intro z hz
  by_cases hzW : z ∈ W
  · exact ((hg z hz).smul (hu.contDiffAt (hW.mem_nhds hzW))).contDiffWithinAt
  · refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_ |>.contDiffWithinAt
    filter_upwards [h z hz hzW] with z' hz'
    rw [hz', zero_smul]

section Perturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A `C^n` scalar cutoff turns a map that is `C^n` near its closed support into a globally
`C^n` perturbation of the identity. -/
theorem _root_.ContDiff.contDiff_cutoff_perturbation_of_contDiffAt
    {χ : E → ℝ} (hχ : ContDiff ℝ n χ) {f : E → E}
    (hf : ∀ x ∈ tsupport χ, ContDiffAt ℝ n f x) :
    ContDiff ℝ n (fun x ↦ x + χ x • (f x - x)) := by
  refine contDiff_id.add (contDiff_iff_contDiffAt.mpr fun x ↦ ?_)
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul ((hf x hx).sub contDiffAt_id)
  · refine (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [hy, zero_smul]

/-- Outside the closed support of the cutoff, the derivative of its perturbation is the identity. -/
theorem fderiv_cutoff_perturbation_eq_id_of_notMem_tsupport
    {χ : E → ℝ} {f : E → E} {x : E} (hx : x ∉ tsupport χ) :
    fderiv ℝ (fun y ↦ y + χ y • (f y - y)) x = ContinuousLinearMap.id ℝ E := by
  have heq : (fun y ↦ y + χ y • (f y - y)) =ᶠ[𝓝 x] id := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [hy, zero_smul, add_zero, id_eq]
  rw [heq.fderiv_eq, fderiv_id]

/-- Product-rule bound for the derivative error of a cutoff perturbation, in terms of the value and
derivative errors of the local map. -/
theorem norm_fderiv_cutoff_perturbation_sub_id_le
    {χ : E → ℝ} {f : E → E} {x : E}
    (hχ : DifferentiableAt ℝ χ x) (hf : DifferentiableAt ℝ f x) :
    ‖fderiv ℝ (fun y ↦ y + χ y • (f y - y)) x - ContinuousLinearMap.id ℝ E‖ ≤
      ‖χ x‖ * ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ +
        ‖fderiv ℝ χ x‖ * ‖f x - x‖ := by
  have hd := (hasFDerivAt_id x).add
    (hχ.hasFDerivAt.smul (hf.hasFDerivAt.sub (hasFDerivAt_id x)))
  -- Pointwise addition and subtraction identify the function with the product-rule expression.
  change HasFDerivAt (fun y ↦ y + χ y • (f y - y))
    (ContinuousLinearMap.id ℝ E +
      (χ x • (fderiv ℝ f x - ContinuousLinearMap.id ℝ E) +
        (fderiv ℝ χ x).smulRight (f x - x))) x at hd
  rw [hd.fderiv, add_sub_cancel_left]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply])

/-- Cutoff derivative error from bounds for the cutoff and the two local errors. -/
theorem norm_fderiv_cutoff_perturbation_sub_id_le_of_bounds
    {χ : E → ℝ} {f : E → E} {x : E} {B₀ B₁ ε : ℝ}
    (hχ : DifferentiableAt ℝ χ x) (hf : DifferentiableAt ℝ f x)
    (h₀ : ‖χ x‖ ≤ B₀) (h₁ : ‖fderiv ℝ χ x‖ ≤ B₁)
    (hf₀ : ‖f x - x‖ ≤ ε) (hf₁ : ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ ε) :
    ‖fderiv ℝ (fun y ↦ y + χ y • (f y - y)) x - ContinuousLinearMap.id ℝ E‖ ≤
      (B₀ + B₁) * ε := by
  calc
    _ ≤ ‖χ x‖ * ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ +
        ‖fderiv ℝ χ x‖ * ‖f x - x‖ :=
      norm_fderiv_cutoff_perturbation_sub_id_le hχ hf
    _ ≤ B₀ * ε + B₁ * ε := add_le_add
      (mul_le_mul h₀ hf₁ (norm_nonneg _) ((norm_nonneg _).trans h₀))
      (mul_le_mul h₁ hf₀ (norm_nonneg _) ((norm_nonneg _).trans h₁))
    _ = _ := (add_mul _ _ _).symm

end Perturbation

end TauCeti

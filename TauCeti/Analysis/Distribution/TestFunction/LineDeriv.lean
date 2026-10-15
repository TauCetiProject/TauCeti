/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Directional derivatives of test functions

Mathlib equips the test functions `𝓓(Ω, F)` with the directional derivative `∂_{v}`. This file
evaluates it pointwise as the classical directional derivative, and shows that two directional
derivatives of a test function commute, `∂_{v} (∂_{w} φ) = ∂_{w} (∂_{v} φ)`, because the second
derivative of a smooth function is symmetric. Moving derivatives between the two sides of an
integration-by-parts identity uses exactly this, for instance to show that weak derivatives
commute. Summing over an orthonormal basis, the Laplacian of a test function commutes with every
directional derivative.

## Main declarations

* `TestFunction.lineDerivOp_apply`: `∂_{v} φ` is the classical directional derivative of `φ`.
* `TestFunction.lineDerivOp_comm` and `TestFunction.lineDeriv_lineDerivOp_comm`: directional
  derivatives of test functions commute.
* `TestFunction.lineDerivOp_laplacianCLM`: the Laplacian of test functions commutes with
  directional derivatives.
* `TestFunction.laplacianCLM_apply`: the test-function Laplacian agrees pointwise with the
  classical Laplacian.
-/

public section

namespace TestFunction

open LineDeriv TopologicalSpace
open scoped Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- The directional derivative of a test function is its classical directional derivative. -/
@[simp]
theorem lineDerivOp_apply (φ : 𝓓(Ω, F)) (v x : E) : ∂_{v} φ x = lineDeriv ℝ φ x v :=
  lineDerivCLM_apply_of_le le_top

/-- The underlying function of a directional derivative of a test function is its classical
directional derivative. -/
@[simp]
theorem coe_lineDerivCLM (φ : 𝓓(Ω, F)) (v : E) :
    ⇑(lineDerivCLM ℝ v φ : 𝓓(Ω, F)) = fun x ↦ lineDeriv ℝ (φ : E → F) x v :=
  funext fun _ ↦ lineDerivCLM_apply_of_le le_top

/-- Iterated directional derivatives of a test function agree with its iterated Fréchet
derivatives evaluated in those directions. -/
theorem lineDeriv_lineDeriv_eq_fderiv_fderiv (φ : 𝓓(Ω, F)) (v w x : E) :
    lineDeriv ℝ (fun y ↦ lineDeriv ℝ (φ : E → F) y v) x w =
      fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → F) y v) x w := by
  have hφ : ∀ y, lineDeriv ℝ (φ : E → F) y v = fderiv ℝ (φ : E → F) y v := fun y ↦
    (φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv
  simp_rw [hφ]
  exact (((φ.contDiff.fderiv_right (by simp)).clm_apply contDiff_const).differentiable
    one_ne_zero x).lineDeriv_eq_fderiv

/-- **Directional derivatives of test functions commute.** -/
theorem lineDerivOp_comm (φ : 𝓓(Ω, F)) (v w : E) : ∂_{v} (∂_{w} φ) = ∂_{w} (∂_{v} φ) := by
  ext x
  have hd : DifferentiableAt ℝ (fderiv ℝ (φ : E → F)) x :=
    (φ.contDiff.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero x
  rw [lineDerivOp_apply, lineDerivOp_apply]
  simp only [lineDerivOp_eq_lineDerivCLM ℝ]
  rw [coe_lineDerivCLM, coe_lineDerivCLM,
    lineDeriv_lineDeriv_eq_fderiv_fderiv, lineDeriv_lineDeriv_eq_fderiv_fderiv]
  simpa [fderiv_clm_apply hd (differentiableAt_const _)] using
    ((φ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)).eq v w

/-- The classical directional derivative of `∂_{v} φ` in the direction `w` is that of `∂_{w} φ`
in the direction `v`. -/
theorem lineDeriv_lineDerivOp_comm (φ : 𝓓(Ω, F)) (v w x : E) :
    lineDeriv ℝ (∂_{v} φ : 𝓓(Ω, F)) x w = lineDeriv ℝ (∂_{w} φ : 𝓓(Ω, F)) x v := by
  rw [← lineDerivOp_apply, ← lineDerivOp_apply, lineDerivOp_comm]

end TestFunction

namespace TestFunction

open LineDeriv TopologicalSpace
open scoped Distributions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- **The Laplacian of test functions commutes with directional derivatives**:
`∂_{v} (Δφ) = Δ (∂_{v} φ)`. -/
theorem lineDerivOp_laplacianCLM (φ : 𝓓(Ω, F)) (v : E) :
    ∂_{v} (laplacianCLM ℝ E 𝓓(Ω, F) φ) = laplacianCLM ℝ E 𝓓(Ω, F) (∂_{v} φ) := by
  simp only [laplacianCLM_eq_sum (stdOrthonormalBasis ℝ E), lineDerivOp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lineDerivOp_comm, lineDerivOp_comm φ v]

open InnerProductSpace Laplacian in
/-- The test-function Laplacian agrees pointwise with the classical Laplacian. -/
@[simp]
theorem laplacianCLM_apply (φ : 𝓓(Ω, F)) (x : E) :
    (laplacianCLM ℝ E (𝓓(Ω, F)) φ) x = Δ (φ : E → F) x := by
  have hcoe (v : E) : ⇑(lineDerivCLM ℝ v φ : 𝓓(Ω, F)) =
      fun y ↦ fderiv ℝ (φ : E → F) y v := by
    funext y
    rw [lineDerivCLM_eq_fderivCLM, fderivCLM_apply_of_le _ le_top]
  simp only [LineDeriv.laplacianCLM, sum_apply,
    ContinuousLinearMap.comp_apply, lineDerivOpCLM_eq_lineDerivCLM,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [lineDerivCLM_eq_fderivCLM, fderivCLM_apply_of_le _ le_top, hcoe,
    fderiv_clm_apply ((φ.contDiff.fderiv_right (by simp)).differentiable one_ne_zero x)
      (differentiableAt_const _)]
  simp

end TestFunction

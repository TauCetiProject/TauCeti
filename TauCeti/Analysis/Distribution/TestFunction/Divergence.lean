/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Translation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Module.Trace
import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# The divergence of a test vector field

For an open set `Ω` of a finite-dimensional real normed space `E`, a test vector field
`φ ∈ 𝓓(Ω, E)` has divergence `div φ = tr (Dφ)`, which is again a test function on `Ω`. This file
packages the divergence as a continuous linear map `𝓓(Ω, E) →L[ℝ] 𝓓(Ω, ℝ)`, in the style of
Mathlib's `TestFunction.fderivCLM`, and, when `E` is an inner product space, expands it in an
orthonormal basis.

The divergence of test vector fields is the operator dual to the distributional gradient: the
total variation of a function and the perimeter of a set are suprema of the pairings
`∫ u div φ` over test vector fields `φ` with `‖φ‖ ≤ 1`.

## Main declarations

* `TestFunction.divergenceCLM`: the divergence `𝓓(Ω, E) →L[ℝ] 𝓓(Ω, ℝ)`.
* `TestFunction.divergenceCLM_apply`: pointwise, it is the trace of the Fréchet derivative.
* `TestFunction.divergenceCLM_monoCLM`: the divergence commutes with extending a test vector
  field from `Ω'` to a larger open set `Ω`.
* `TestFunction.divergenceCLM_postcompCLM_toSpanSingleton`: the divergence of the vector field
  `φ v` is the directional derivative `∂_v φ`.
* `TestFunction.divergenceCLM_apply_eq_deriv`: on the real line, the divergence of a test
  function is its derivative.
* `TestFunction.divergenceCLM_apply_eq_sum`: in an orthonormal basis `b`, it is the sum of the
  derivatives of the components `⟪b i, φ⟫` in the directions `b i`.
* `TauCeti.divergenceCLM_translateTestFunction`: the divergence of a translated test vector field
  is the translate of its divergence.
* `TauCeti.trace_fderiv_smul` and `TauCeti.trace_fderiv_smul_const`: the Leibniz rule
  `div (χ φ) = χ div φ + Dχ φ` for the divergence `tr (D ·)` of a vector field multiplied by a
  scalar function.
-/

public section

namespace TestFunction

open LineDeriv TopologicalSpace
open scoped ContDiff Distributions InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω Ω' : Opens E}

/-- The **divergence** `div φ = tr (Dφ)` of a test vector field `φ ∈ 𝓓(Ω, E)`, as a continuous
linear map into the scalar test functions `𝓓(Ω, ℝ)`. It is the composite of the Fréchet
derivative `TestFunction.fderivCLM` with the trace `TauCeti.traceCLM`. -/
noncomputable def divergenceCLM : 𝓓(Ω, E) →L[ℝ] 𝓓(Ω, ℝ) :=
  postcompCLM (TauCeti.traceCLM ℝ E) ∘L fderivCLM ℝ ⊤ ⊤

/-- The divergence of a test vector field is pointwise the trace of its Fréchet derivative. -/
@[simp]
theorem divergenceCLM_apply (φ : 𝓓(Ω, E)) (x : E) :
    divergenceCLM φ x = LinearMap.trace ℝ E (fderiv ℝ (φ : E → E) x : E →ₗ[ℝ] E) := by
  simp [divergenceCLM]

/-- The divergence of a test vector field extended from `Ω'` to a larger open set `Ω` is the
divergence of the original field. -/
@[simp]
theorem divergenceCLM_monoCLM (h : Ω' ≤ Ω) (φ : 𝓓(Ω', E)) :
    (divergenceCLM (monoCLM ℝ φ : 𝓓(Ω, E)) : E → ℝ) = divergenceCLM φ := by
  ext x
  simp [monoCLM_apply, h]

/-- The divergence of the test vector field `φ v`, for a scalar test function `φ` and a fixed
vector `v`, is the directional derivative `∂_v φ`. -/
@[simp]
theorem divergenceCLM_postcompCLM_toSpanSingleton (φ : 𝓓(Ω, ℝ)) (v : E) :
    divergenceCLM (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ v) φ) = ∂_{v} φ := by
  ext x
  have hφ : DifferentiableAt ℝ (φ : E → ℝ) x := φ.contDiff.differentiable (by simp) x
  have hcoe : ⇑(postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ v) φ) = fun y => φ y • v := by
    ext y
    simp
  rw [divergenceCLM_apply, hcoe, fderiv_smul_const hφ, lineDerivOp_eq_lineDerivCLM ℝ,
    lineDerivCLM_apply_of_le le_top, hφ.lineDeriv_eq_fderiv]
  exact LinearMap.trace_smulRight _ _

/-- On the real line, a test function is a test vector field whose divergence is its
derivative. -/
theorem divergenceCLM_apply_eq_deriv {Ω : Opens ℝ} (φ : 𝓓(Ω, ℝ)) (x : ℝ) :
    divergenceCLM φ x = deriv φ x := by
  have hφ : postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)) φ = φ := by
    ext; simp
  conv_lhs => rw [← hφ]
  rw [divergenceCLM_postcompCLM_toSpanSingleton, lineDerivOp_one_apply_eq_deriv]

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E}

/-- **The divergence in an orthonormal basis**: `div φ = ∑ i, ∂_{b i} ⟪b i, φ⟫`. -/
theorem divergenceCLM_apply_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (φ : 𝓓(Ω, E)) (x : E) :
    divergenceCLM φ x = ∑ i, lineDeriv ℝ (fun y => ⟪b i, φ y⟫_ℝ) x (b i) := by
  have hφ : DifferentiableAt ℝ (φ : E → E) x := φ.contDiff.differentiable (by simp) x
  rw [divergenceCLM_apply, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : HasFDerivAt (fun y => ⟪b i, φ y⟫_ℝ) ((innerSL ℝ (b i)).comp (fderiv ℝ φ x)) x :=
    (innerSL ℝ (b i)).hasFDerivAt.comp x hφ.hasFDerivAt
  rw [hd.hasLineDerivAt (b i) |>.lineDeriv]
  simp

end InnerProductSpace

end TestFunction

namespace TauCeti

open Set TestFunction TopologicalSpace
open scoped Distributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω V : Opens E} {h : E}

/-- The divergence of a translated test vector field is the translate of its divergence. -/
@[simp]
theorem divergenceCLM_translateTestFunction (hVO : MapsTo (· + h) V Ω) (φ : 𝓓(V, E)) :
    divergenceCLM (translateTestFunction hVO φ) =
      translateTestFunction hVO (divergenceCLM φ) := by
  ext y
  simp only [divergenceCLM_apply, fderiv_translateTestFunction, translateTestFunction_apply]

/-- **Leibniz rule for the divergence**: `div (χ φ) = χ div φ + Dχ φ`, where the divergence of a
vector field is the trace of its Fréchet derivative. -/
theorem trace_fderiv_smul {χ : E → ℝ} {φ : E → E} {x : E} (hχ : DifferentiableAt ℝ χ x)
    (hφ : DifferentiableAt ℝ φ x) :
    LinearMap.trace ℝ E (fderiv ℝ (fun y => χ y • φ y) x : E →ₗ[ℝ] E) =
      χ x * LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) + fderiv ℝ χ x (φ x) := by
  simp [fderiv_fun_smul hχ hφ, LinearMap.trace_smulRight]

/-- **Divergence of a scalar function times a constant vector**: `div (χ v) = Dχ v`. -/
theorem trace_fderiv_smul_const {χ : E → ℝ} {x : E} (hχ : DifferentiableAt ℝ χ x) (v : E) :
    LinearMap.trace ℝ E (fderiv ℝ (fun y => χ y • v) x : E →ₗ[ℝ] E) = fderiv ℝ χ x v := by
  simpa using trace_fderiv_smul hχ (differentiableAt_const v)

end TauCeti

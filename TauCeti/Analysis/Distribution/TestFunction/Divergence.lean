/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Translation
public import TauCeti.Topology.Algebra.Module.Trace
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# The divergence of a test vector field

For an open set `Ω` of a finite-dimensional real normed space `E`, a test vector field
`φ ∈ 𝓓(Ω, E)` has divergence `div φ = tr (Dφ)`, which is again a test function on `Ω`. This file
packages the divergence as a continuous linear map `𝓓(Ω, E) →L[ℝ] 𝓓(Ω, ℝ)`, in the style of
Mathlib's `TestFunction.fderivCLM`, and expands it in the coordinates of any finite basis.

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
* `TestFunction.divergenceCLM_apply_eq_sum`: in a basis `b`, it is the sum of the derivatives of
  the coordinate functions `b.repr (φ ·) i` in the directions `b i`.
* `TauCeti.divergenceCLM_translateTestFunction`: the divergence of a translated test vector field
  is the translate of its divergence.
* `TauCeti.integral_divergenceCLM_mul_congr_ae`: the pairing `∫ u div φ` only depends on `u`
  almost everywhere on `Ω`.
* `TauCeti.trace_fderiv_smul` and `TauCeti.trace_fderiv_smul_const`: the Leibniz rule
  `div (χ φ) = χ div φ + Dχ φ` for the divergence `tr (D ·)` of a vector field multiplied by a
  scalar function.
* `TauCeti.exists_testFunction_sum_smul_comp_add`: weighting translates of a test vector field
  `φ` by nonnegative smooth functions `ζ k` compactly supported in `Ω` with sum at most one gives
  a test vector field `∑ k, ζ k φ(· + τ k)` on `Ω`, of norm at most one when `‖φ‖ ≤ 1`, whose
  divergence is given by the Leibniz rule.
-/

public section

namespace TestFunction

open LineDeriv TopologicalSpace
open scoped ContDiff Distributions

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

/-- **The divergence in a basis**: `div φ = ∑ i, ∂_{b i} (b.repr (φ ·) i)`. -/
theorem divergenceCLM_apply_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (φ : 𝓓(Ω, E)) (x : E) :
    divergenceCLM φ x = ∑ i, lineDeriv ℝ (fun y => b.repr (φ y) i) x (b i) := by
  classical
  rw [divergenceCLM_apply, LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : HasFDerivAt (fun y => b.repr (φ y) i)
      ((LinearMap.toContinuousLinearMap (b.coord i)).comp (fderiv ℝ (φ : E → E) x)) x :=
    (LinearMap.toContinuousLinearMap (b.coord i)).hasFDerivAt.comp x
      (φ.contDiff.differentiable (by simp) x).hasFDerivAt
  rw [(hd.hasLineDerivAt (b i)).lineDeriv]
  simp [LinearMap.toMatrix_apply]

end TestFunction

namespace TauCeti

open Set TestFunction TopologicalSpace
open scoped ContDiff Distributions

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

/-- Let `ζ k`, for `k ∈ s`, be nonnegative smooth functions compactly supported in `Ω` whose sum
is at most one, and `φ` a test vector field on `Ω` with `‖φ‖ ≤ 1`. For any vectors `τ k`, the
field `∑ k ∈ s, ζ k φ(· + τ k)` is a test vector field on `Ω` of norm at most one, whose
divergence is given by the Leibniz rule `div (ζ φ) = ζ div φ + Dζ φ`. The translates
`φ(· + τ k)` need not be supported in `Ω`: the weights `ζ k` cut them off. -/
theorem exists_testFunction_sum_smul_comp_add {ι : Type*} {s : Finset ι} {ζ : ι → E → ℝ}
    (hζ : ∀ k ∈ s, ContDiff ℝ ∞ (ζ k) ∧ HasCompactSupport (ζ k) ∧ tsupport (ζ k) ⊆ Ω)
    (hζ0 : ∀ k ∈ s, ∀ x, 0 ≤ ζ k x) (hζ1 : ∀ x, ∑ k ∈ s, ζ k x ≤ 1)
    (φ : 𝓓(Ω, E)) (hφ : ∀ x, ‖φ x‖ ≤ 1) (τ : ι → E) :
    ∃ Φ : 𝓓(Ω, E), (∀ y, Φ y = ∑ k ∈ s, ζ k y • φ (y + τ k)) ∧ (∀ y, ‖Φ y‖ ≤ 1) ∧
      ∀ y, divergenceCLM Φ y =
        ∑ k ∈ s, (ζ k y * divergenceCLM φ (y + τ k) + fderiv ℝ (ζ k) y (φ (y + τ k))) := by
  have hφτ (k : ι) : ContDiff ℝ ∞ (fun y => φ (y + τ k)) :=
    φ.contDiff.comp (contDiff_id.add contDiff_const)
  set L : Set E := ⋃ k ∈ s, tsupport (ζ k)
  have hL : IsCompact L := s.isCompact_biUnion fun k hk => (hζ k hk).2.1
  have hLΩ : L ⊆ Ω := iUnion₂_subset fun k hk => (hζ k hk).2.2
  have hΦL : Function.support (fun y => ∑ k ∈ s, ζ k y • φ (y + τ k)) ⊆ L := fun y hy => by
    by_contra hyL
    refine hy (Finset.sum_eq_zero fun k hk => ?_)
    rw [image_eq_zero_of_notMem_tsupport fun h => hyL (mem_iUnion₂.2 ⟨k, hk, h⟩), zero_smul]
  have hΦt : tsupport (fun y => ∑ k ∈ s, ζ k y • φ (y + τ k)) ⊆ L :=
    closure_minimal hΦL hL.isClosed
  refine ⟨⟨fun y => ∑ k ∈ s, ζ k y • φ (y + τ k),
    ContDiff.sum fun k hk => (hζ k hk).1.smul (hφτ k),
    .of_support_subset_isCompact hL hΦL, hΦt.trans hLΩ⟩, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · simp only [TestFunction.coe_mk]
  · simp only [TestFunction.coe_mk]
    calc ‖∑ k ∈ s, ζ k y • φ (y + τ k)‖
        ≤ ∑ k ∈ s, ‖ζ k y • φ (y + τ k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ s, ζ k y := Finset.sum_le_sum fun k hk => by
          rw [norm_smul, Real.norm_of_nonneg (hζ0 k hk y)]
          exact mul_le_of_le_one_right (hζ0 k hk y) (hφ _)
      _ ≤ 1 := hζ1 y
  · have hζd (k : ι) (hk : k ∈ s) : DifferentiableAt ℝ (ζ k) y :=
      (hζ k hk).1.differentiable (by simp) y
    have hd (k : ι) : DifferentiableAt ℝ (fun y => φ (y + τ k)) y :=
      (hφτ k).differentiable (by simp) y
    rw [divergenceCLM_apply]
    simp only [TestFunction.coe_mk]
    rw [fderiv_fun_sum (A := fun k y => ζ k y • φ (y + τ k)) fun k hk => (hζd k hk).smul (hd k),
      ContinuousLinearMap.toLinearMap_sum, map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [trace_fderiv_smul (hζd k hk) (hd k), fderiv_comp_add_right, divergenceCLM_apply]

/-- The pairing `∫ u div φ` of `u` with a test vector field `φ` on `Ω` only depends on `u` almost
everywhere on `Ω`, since `div φ` vanishes off `Ω`. -/
theorem integral_divergenceCLM_mul_congr_ae [MeasurableSpace E] {μ : MeasureTheory.Measure E}
    {u v : E → ℝ} (huv : u =ᵐ[μ.restrict Ω] v) (φ : 𝓓(Ω, E)) :
    ∫ x, divergenceCLM φ x * u x ∂μ = ∫ x, divergenceCLM φ x * v x ∂μ := by
  have hΩ (w : E → ℝ) :
      ∫ x in (Ω : Set E), divergenceCLM φ x * w x ∂μ = ∫ x, divergenceCLM φ x * w x ∂μ :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun hmem =>
        hx ((divergenceCLM φ).tsupport_subset hmem), zero_mul]
  rw [← hΩ, ← hΩ]
  exact MeasureTheory.integral_congr_ae (huv.mono fun x hx => by simp only [hx])

end TauCeti

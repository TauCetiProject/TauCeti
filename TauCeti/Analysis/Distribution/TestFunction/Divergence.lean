/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Translation
public import TauCeti.Topology.Algebra.Module.Trace
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts

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
* `TestFunction.tsupport_divergenceCLM_subset`: the divergence of a test vector field is supported
  in the support of the field.
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
* `TauCeti.smulTestField`: a scalar test function times a vector field smooth on `Ω`.
* `TauCeti.divergenceCLM_smulTestField`: the divergence product rule for this test field.
* `TauCeti.trace_fderiv_smul` and `TauCeti.trace_fderiv_smul_const`: the Leibniz rule
  `div (χ φ) = χ div φ + Dχ φ` for the divergence `tr (D ·)` of a vector field multiplied by a
  scalar function.
* `TauCeti.trace_fderiv_exp_neg_smul`: the weighted divergence
  `div (e^{−W} φ) = (div φ − DW φ) e^{−W}`.
* `TauCeti.exists_testFunction_sum_smul_comp_add`: weighting translates of a test vector field
  `φ` by nonnegative smooth functions `ζ k` compactly supported in `Ω` with sum at most one gives
  a test vector field `∑ k, ζ k φ(· + τ k)` on `Ω`, of norm at most one when `‖φ‖ ≤ 1`, whose
  divergence is given by the Leibniz rule.
* `TauCeti.trace_fderiv_orthogonalLine_eq` and `TauCeti.divergenceCLM_orthogonalLine_eq`:
  decompose the divergence in orthogonal line coordinates along a unit vector `e` into the
  hyperplane divergence of the orthogonal projection onto `(ℝ ∙ e)ᗮ` plus the longitudinal
  derivative along `e`.
* `TauCeti.trace_fderiv_smul_comp_mul`, `TauCeti.continuous_trace_fderiv_comp_mul`,
  `TauCeti.trace_fderiv_comp_mul_eq_zero_of_notMem`, and
  `TauCeti.integral_mul_trace_fderiv_comp_mul_eq_neg`: pointwise chain rule, continuity,
  off-support vanishing, and compact-support integral identity for a rescaled field
  `z ↦ a z • A z (a z * u)`.
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

/-- The divergence of a test vector field is supported in the support of the field. -/
theorem tsupport_divergenceCLM_subset (φ : 𝓓(Ω, E)) :
    tsupport (divergenceCLM φ) ⊆ tsupport φ := by
  have h : ⇑(divergenceCLM φ) = TauCeti.traceCLM ℝ E ∘ fderiv ℝ (φ : E → E) :=
    funext fun x => by rw [divergenceCLM_apply, Function.comp_apply, TauCeti.traceCLM_apply]
  rw [h]
  exact (tsupport_comp_subset (map_zero _) _).trans (tsupport_fderiv_subset ℝ)

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

omit [FiniteDimensional ℝ E] in
/-- The test vector field `φ b`, for a test function `φ` and a vector field `b` smooth on `Ω`. -/
noncomputable def smulTestField {b : E → E} (hb : ContDiffOn ℝ ∞ b Ω) (φ : 𝓓(Ω, ℝ)) :
    𝓓(Ω, E) :=
  ⟨fun x ↦ φ x • b x, hb.contDiff_smul_of_tsupport_subset Ω.isOpen φ.contDiff.contDiffOn
    φ.tsupport_subset, φ.hasCompactSupport.smul_right,
    (tsupport_smul_subset_left _ _).trans φ.tsupport_subset⟩

omit [FiniteDimensional ℝ E] in
/-- The test field `φ b` evaluated at a point. -/
@[simp]
theorem smulTestField_apply {b : E → E} (hb : ContDiffOn ℝ ∞ b Ω) (φ : 𝓓(Ω, ℝ))
    (x : E) : smulTestField hb φ x = φ x • b x :=
  (rfl)

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

open scoped Gradient InnerProductSpace in
/-- On `Ω`, the divergence of `φ b` is `φ div b + ⟪∇φ, b⟫`. -/
theorem divergenceCLM_smulTestField {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {Ω : Opens F} {b : F → F}
    (hb : ContDiffOn ℝ ∞ b Ω) (φ : 𝓓(Ω, ℝ))
    {x : F} (hx : x ∈ Ω) :
    TestFunction.divergenceCLM (smulTestField hb φ) x =
      φ x * LinearMap.trace ℝ F (fderiv ℝ b x : F →ₗ[ℝ] F) +
        ⟪∇ (φ : F → ℝ) x, b x⟫_ℝ := by
  have hcoe : (smulTestField hb φ : F → F) = fun y ↦ φ y • b y := by
    funext y
    exact smulTestField_apply hb φ y
  rw [TestFunction.divergenceCLM_apply, hcoe, trace_fderiv_smul
      (φ.contDiff.differentiable (by simp) x)
      ((hb.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)), gradient,
    InnerProductSpace.toDual_symm_apply]

/-- **The weighted divergence.** For a differentiable weight `W` and vector field `X`,
`div (e^{−W} X) = (div X − DW X) e^{−W}`, where `div = tr ∘ D`. -/
theorem trace_fderiv_exp_neg_smul {W : E → ℝ} {X : E → E} {x : E}
    (hW : DifferentiableAt ℝ W x) (hX : DifferentiableAt ℝ X x) :
    LinearMap.trace ℝ E (fderiv ℝ (fun y => Real.exp (-W y) • X y) x : E →ₗ[ℝ] E) =
      (LinearMap.trace ℝ E (fderiv ℝ X x : E →ₗ[ℝ] E) - fderiv ℝ W x (X x)) *
        Real.exp (-W x) := by
  have hW' : DifferentiableAt ℝ (fun y => -W y) x := hW.neg
  rw [trace_fderiv_smul hW'.exp hX, fderiv_exp hW', fderiv_fun_neg]
  simp only [_root_.smul_apply, _root_.neg_apply, smul_eq_mul]
  ring

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

section OrthogonalLine

open scoped RealInnerProductSpace

/-- Decompose the divergence `tr (Df)` in orthogonal line coordinates along a unit vector `e` into
the hyperplane divergence of the transverse projection `(ℝ ∙ e)ᗮ.orthogonalProjectionOnto ∘ f`
plus the longitudinal derivative `d/ds ⟪e, f (y + s • e)⟫` along `e`. -/
theorem trace_fderiv_orthogonalLine_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (e : F) (he : ‖e‖ = 1)
    {f : F → F} {y : (ℝ ∙ e)ᗮ} {t : ℝ} (hf : DifferentiableAt ℝ f ((y : F) + t • e)) :
    LinearMap.trace ℝ F (fderiv ℝ f ((y : F) + t • e) : F →ₗ[ℝ] F) =
      LinearMap.trace ℝ (ℝ ∙ e)ᗮ
          (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ =>
            (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (f ((z : F) + t • e))) y :
            (ℝ ∙ e)ᗮ →ₗ[ℝ] (ℝ ∙ e)ᗮ) +
        deriv (fun s : ℝ => ⟪e, f ((y : F) + s • e)⟫) t := by
  set P : F →L[ℝ] (ℝ ∙ e)ᗮ := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  have hproj (x : F) : (P x : F) + ⟪e, x⟫ • e = x := by
    have hmem : x - ⟪e, x⟫ • e ∈ (ℝ ∙ e)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      simp [inner_sub_right, inner_smul_right, he]
    have hP : P x = ⟨x - ⟪e, x⟫ • e, hmem⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_orthogonalProjectionOnto_apply]
      exact Submodule.eq_starProjection_of_mem_orthogonal' hmem
        (Submodule.le_orthogonal_orthogonal _
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)))
        (sub_add_cancel x (⟪e, x⟫ • e)).symm
    rw [hP, Submodule.coe_mk, sub_add_cancel]
  set g : F → (ℝ ∙ e)ᗮ := fun x => P (f x)
  have hdecomp : f = fun x => (ℝ ∙ e)ᗮ.subtypeL (g x) + ⟪e, f x⟫ • e := by
    ext x
    exact (hproj (f x)).symm
  set x₀ : F := (y : F) + t • e
  have hgd : DifferentiableAt ℝ g x₀ := P.differentiableAt.comp x₀ hf
  have h1d : DifferentiableAt ℝ (fun x => (ℝ ∙ e)ᗮ.subtypeL (g x)) x₀ :=
    (ℝ ∙ e)ᗮ.subtypeL.differentiableAt.comp x₀ hgd
  have hinner : DifferentiableAt ℝ (fun x => ⟪e, f x⟫) x₀ :=
    (innerSL ℝ e).differentiableAt.comp x₀ hf
  conv_lhs =>
    rw [hdecomp, fderiv_fun_add h1d (hinner.smul_const e), ContinuousLinearMap.toLinearMap_add,
      map_add, trace_fderiv_smul_const hinner e]
  congr 1
  · have hf1 : fderiv ℝ (fun x => (ℝ ∙ e)ᗮ.subtypeL (g x)) x₀ =
        (ℝ ∙ e)ᗮ.subtypeL.comp (fderiv ℝ g x₀) :=
      ((ℝ ∙ e)ᗮ.subtypeL.hasFDerivAt.comp x₀ hgd.hasFDerivAt).fderiv
    have haff : HasFDerivAt (fun z : (ℝ ∙ e)ᗮ => (z : F) + t • e) (ℝ ∙ e)ᗮ.subtypeL y :=
      ((ℝ ∙ e)ᗮ.subtypeL.hasFDerivAt (x := y)).add_const (t • e)
    have hf2 : fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => P (f ((z : F) + t • e))) y =
        (fderiv ℝ g x₀).comp (ℝ ∙ e)ᗮ.subtypeL :=
      (HasFDerivAt.comp (f := fun z : (ℝ ∙ e)ᗮ => (z : F) + t • e) y
        hgd.hasFDerivAt haff).fderiv
    rw [hf1, hf2, ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp]
    exact LinearMap.trace_comp_comm' _ _
  · have hl : HasDerivAt (fun s : ℝ => (y : F) + s • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add (y : F)
    exact (hinner.hasFDerivAt.comp_hasDerivAt t hl).deriv.symm

/-- Decompose `divergenceCLM φ` in orthogonal line coordinates along a unit vector `e` into the
hyperplane divergence of its transverse projection `(ℝ ∙ e)ᗮ.orthogonalProjectionOnto ∘ φ` plus
the longitudinal derivative along `e`. -/
theorem divergenceCLM_orthogonalLine_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {Ω : Opens F} (e : F) (he : ‖e‖ = 1)
    (φ : 𝓓(Ω, F)) (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    divergenceCLM φ ((y : F) + t • e) =
      LinearMap.trace ℝ (ℝ ∙ e)ᗮ
          (fderiv ℝ (fun z : (ℝ ∙ e)ᗮ =>
            (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (φ ((z : F) + t • e))) y :
            (ℝ ∙ e)ᗮ →ₗ[ℝ] (ℝ ∙ e)ᗮ) +
        deriv (fun s : ℝ => ⟪e, φ ((y : F) + s • e)⟫) t := by
  rw [divergenceCLM_apply]
  exact trace_fderiv_orthogonalLine_eq e he (φ.contDiff.differentiable (by simp) _)

end OrthogonalLine

section RescaledField

/-- Pointwise Leibniz-and-chain-rule identity for the divergence of a field rescaled along a
scalar function `a`: `z ↦ a z • A z (a z * u)`. -/
theorem trace_fderiv_smul_comp_mul {A : E → ℝ → E} {a : E → ℝ} {u : ℝ} {y : E}
    (hA : DifferentiableAt ℝ (Function.uncurry A) (y, a y * u))
    (ha : DifferentiableAt ℝ a y) :
    LinearMap.trace ℝ E (fderiv ℝ (fun z : E => a z • A z (a z * u)) y : E →ₗ[ℝ] E) =
      a y * LinearMap.trace ℝ E (fderiv ℝ (fun z : E => A z (a y * u)) y : E →ₗ[ℝ] E) +
        deriv (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s))) u := by
  have hmul : HasFDerivAt (fun z : E => a z * u) (u • fderiv ℝ a y) y := by
    simpa only [mul_comm] using (ha.hasFDerivAt.const_mul u).congr_of_eventuallyEq
      (.of_forall fun z => mul_comm (a z) u)
  have hAd : DifferentiableAt ℝ (A y) (a y * u) :=
    hA.comp (a y * u) (differentiableAt_const y |>.prodMk differentiableAt_id)
  have hcomp_diff : DifferentiableAt ℝ (fun z : E => A z (a z * u)) y :=
    hA.fun_comp' y (differentiableAt_id.prodMk hmul.differentiableAt)
  have hcomp_eq : fderiv ℝ (fun z : E => A z (a z * u)) y =
      fderiv ℝ (fun z : E => A z (a y * u)) y +
        (u • fderiv ℝ a y).smulRight (deriv (A y) (a y * u)) := by
    ext v
    have hg := fderiv_comp_graph_apply (f := Function.uncurry A) hmul.differentiableAt hA v
    have hleft := congrArg (fun L => L v) (fderiv_slice_left hA)
    simp only [Function.uncurry, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
      at hg hleft
    rw [hg, ← hleft, hmul.fderiv, hAd.hasDerivAt.hasFDerivAt.fderiv]
    simp [ContinuousLinearMap.smulRight_apply]
  have hlin : HasDerivAt (fun s : ℝ => a y * s) (a y) u := by
    simpa using (hasDerivAt_id u).const_mul (a y)
  have hsm := (hasDerivAt_id u).smul (hAd.hasDerivAt.scomp u hlin)
  have hΦd : HasDerivAt (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s)))
      (fderiv ℝ a y (u • (a y • deriv (A y) (a y * u)) + (1 : ℝ) • A y (a y * u))) u :=
    (fderiv ℝ a y).hasFDerivAt.comp_hasDerivAt u hsm
  rw [trace_fderiv_smul ha hcomp_diff, hcomp_eq, ContinuousLinearMap.toLinearMap_add, map_add,
    hΦd.deriv]
  simp only [ContinuousLinearMap.coe_smulRight, LinearMap.trace_smulRight,
    ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    smul_eq_mul, map_add, map_smul, one_smul]
  ring

/-- Continuity on `ℝ × E` of the two pieces in `TauCeti.trace_fderiv_smul_comp_mul`. -/
theorem continuous_trace_fderiv_comp_mul {A : E → ℝ → E}
    (hA : ContDiff ℝ 1 (Function.uncurry A)) {a : E → ℝ} (ha : ContDiff ℝ 1 a) :
    Continuous (fun q : ℝ × E =>
        a q.2 * LinearMap.trace ℝ E
          (fderiv ℝ (fun z : E => A z (a q.2 * q.1)) q.2 : E →ₗ[ℝ] E)) ∧
      Continuous (fun q : ℝ × E =>
        deriv (fun s : ℝ => fderiv ℝ a q.2 (s • A q.2 (a q.2 * s))) q.1) := by
  have hFA : (fun p : E × ℝ => fderiv ℝ (fun z : E => A z p.2) p.1) =
      fun p => (fderiv ℝ (Function.uncurry A) p).comp (.inl ℝ E ℝ) :=
    funext fun p => fderiv_slice_left (hA.differentiable one_ne_zero (p.1, p.2))
  have hFA_cont : Continuous (fun p : E × ℝ => fderiv ℝ (fun z : E => A z p.2) p.1) := by
    rw [hFA]
    exact (((ContinuousLinearMap.compL ℝ E (E × ℝ) E).flip (.inl ℝ E ℝ)).continuous.comp
      (hA.continuous_fderiv one_ne_zero))
  have hP1 : Continuous (fun q : ℝ × E =>
      a q.2 * LinearMap.trace ℝ E
        (fderiv ℝ (fun z : E => A z (a q.2 * q.1)) q.2 : E →ₗ[ℝ] E)) := by
    simp_rw [← traceCLM_apply]
    exact (ha.continuous.comp continuous_snd).mul <|
      (traceCLM ℝ E).continuous.comp <| hFA_cont.comp
        (continuous_snd.prodMk ((ha.continuous.comp continuous_snd).mul continuous_fst))
  have hWu : ContDiff ℝ 1 (fun q : ℝ × E => a q.2 • A q.2 (a q.2 * q.1)) :=
    (ha.comp contDiff_snd).smul
      (hA.comp (contDiff_snd.prodMk ((ha.comp contDiff_snd).mul contDiff_fst)))
  have hdiv_eq : (fun q : ℝ × E => LinearMap.trace ℝ E
        (fderiv ℝ (fun z : E => a z • A z (a z * q.1)) q.2 : E →ₗ[ℝ] E)) =
      fun q => traceCLM ℝ E
        ((fderiv ℝ (fun p : ℝ × E => a p.2 • A p.2 (a p.2 * p.1)) q).comp (.inr ℝ ℝ E)) :=
    funext fun q => by
      rw [← traceCLM_apply]
      exact congrArg (traceCLM ℝ E)
        (fderiv_slice_right (f := fun p : ℝ × E => a p.2 • A p.2 (a p.2 * p.1))
          (hWu.differentiable one_ne_zero (q.1, q.2)))
  have hdiv : Continuous (fun q : ℝ × E => LinearMap.trace ℝ E
      (fderiv ℝ (fun z : E => a z • A z (a z * q.1)) q.2 : E →ₗ[ℝ] E)) := by
    rw [hdiv_eq]
    exact (traceCLM ℝ E).continuous.comp
      (((ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip (.inr ℝ ℝ E)).continuous.comp
        (hWu.continuous_fderiv one_ne_zero))
  refine ⟨hP1, ?_⟩
  convert hdiv.sub hP1 using 1
  ext ⟨u, y⟩
  simp only [Pi.sub_apply]
  linarith [trace_fderiv_smul_comp_mul
    (hA.differentiable one_ne_zero (y, a y * u)) (ha.differentiable one_ne_zero y)]

omit [FiniteDimensional ℝ E] in
/-- Off a closed set `K` outside which `A` vanishes, both pieces in
`TauCeti.trace_fderiv_smul_comp_mul` vanish. -/
theorem trace_fderiv_comp_mul_eq_zero_of_notMem {K : Set E} (hK : IsClosed K)
    {A : E → ℝ → E} (hA0 : ∀ {y : E}, y ∉ K → ∀ t, A y t = 0) (a : E → ℝ) (u : ℝ)
    {y : E} (hy : y ∉ K) :
    a y * LinearMap.trace ℝ E (fderiv ℝ (fun z : E => A z (a y * u)) y : E →ₗ[ℝ] E) = 0 ∧
      deriv (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s))) u = 0 := by
  refine ⟨?_, ?_⟩
  · have hloc : (fun z : E => A z (a y * u)) =ᶠ[nhds y] 0 :=
      Filter.eventually_of_mem (hK.isOpen_compl.mem_nhds hy) fun z hz => hA0 hz _
    simp [hloc.fderiv_eq]
  · have hloc : (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s))) = 0 :=
      funext fun s => by simp [hA0 hy]
    rw [hloc]
    simp

/-- For any fixed parameter `u : ℝ`, when `A` is `C¹` and vanishes outside a compact set `K`, and
`a` is `C¹`, integrating the rescaled divergence piece `a y * div_y (A · (a y * u))` against an
additive Haar measure equals minus the integral of the `u`-derivative term, since their sum is the
divergence of the compactly supported `C¹` field `y ↦ a y • A y (a y * u)`. -/
theorem integral_mul_trace_fderiv_comp_mul_eq_neg [MeasurableSpace E] [BorelSpace E]
    {μ : MeasureTheory.Measure E} [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) {A : E → ℝ → E} (hA : ContDiff ℝ 1 (Function.uncurry A))
    (hA0 : ∀ {y : E}, y ∉ K → ∀ t, A y t = 0) {a : E → ℝ} (ha : ContDiff ℝ 1 a) (u : ℝ) :
    (∫ y : E, a y * LinearMap.trace ℝ E
        (fderiv ℝ (fun z : E => A z (a y * u)) y : E →ₗ[ℝ] E) ∂μ) =
      -∫ y : E, deriv (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s))) u ∂μ := by
  let W : E → E := fun y => a y • A y (a y * u)
  have hW : ContDiff ℝ 1 W :=
    ha.smul (hA.comp (contDiff_id.prodMk (ha.mul contDiff_const)))
  have hWc : HasCompactSupport W := .of_support_subset_isCompact hK fun y hy => by
    by_contra hyK
    exact hy (by simp [W, hA0 hyK])
  have hW_int : MeasureTheory.Integrable (fderiv ℝ W) μ :=
    (hW.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (hWc.fderiv (𝕜 := ℝ))
  have hW0 : ∫ y : E, LinearMap.trace ℝ E (fderiv ℝ W y : E →ₗ[ℝ] E) ∂μ = 0 := by
    simp_rw [← traceCLM_apply]
    rw [(traceCLM ℝ E).integral_comp_comm hW_int,
      integral_fderiv_eq_zero_of_hasCompactSupport hW hWc, map_zero]
  obtain ⟨hP1c, hP2c⟩ := continuous_trace_fderiv_comp_mul hA ha
  have hi1 : MeasureTheory.Integrable (fun y : E => a y * LinearMap.trace ℝ E
      (fderiv ℝ (fun z : E => A z (a y * u)) y : E →ₗ[ℝ] E)) μ :=
    (hP1c.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (.of_support_subset_isCompact hK fun y hy => by
        by_contra hyK
        exact hy (trace_fderiv_comp_mul_eq_zero_of_notMem hK.isClosed hA0 a u hyK).1)
  have hi2 : MeasureTheory.Integrable (fun y : E =>
      deriv (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s))) u) μ :=
    (hP2c.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (.of_support_subset_isCompact hK fun y hy => by
        by_contra hyK
        exact hy (trace_fderiv_comp_mul_eq_zero_of_notMem hK.isClosed hA0 a u hyK).2)
  have hsum : (∫ y : E, a y * LinearMap.trace ℝ E
        (fderiv ℝ (fun z : E => A z (a y * u)) y : E →ₗ[ℝ] E) ∂μ) +
      (∫ y : E, deriv (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s))) u ∂μ) =
      ∫ y : E, LinearMap.trace ℝ E (fderiv ℝ W y : E →ₗ[ℝ] E) ∂μ := by
    rw [← MeasureTheory.integral_add hi1 hi2]
    exact MeasureTheory.integral_congr_ae (.of_forall fun y =>
      (trace_fderiv_smul_comp_mul (hA.differentiable one_ne_zero (y, a y * u))
        (ha.differentiable one_ne_zero y)).symm)
  linarith

end RescaledField

end TauCeti

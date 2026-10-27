/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Topology.Compactness.Normed

/-!
# Analytic parameter dependence of integrals over compact families

Let `f : V × Y → E` be a family of functions of a complex parameter `p ∈ V` and a variable
`y ∈ Y`, and let `φ : α → Y` be a continuous map whose values lie in a compact set `K`. If `f` is
jointly complex analytic at every point of `{p₀} × K`, then for every integrable weight
`g : α → ℂ` the integral

`p ↦ ∫ a, g a • f (p, φ a) ∂μ`

may be differentiated under the integral sign at `p₀`, and is complex analytic at `p₀` when `V` is
finite-dimensional. Only analyticity near the compact set `{p₀} × K` is needed, so the integrand
may be singular elsewhere.

This is the measure-theoretic form of `TauCeti.analyticAt_circleIntegral`: the integration
variable ranges over an arbitrary second-countable space with an arbitrary measure, and only its
image under `φ` must lie in a compact subset of a complex normed space. A typical use integrates a
kernel `k (z, w)`, holomorphic in both variables near a set of real points `(x, y)`, over a
compact real surface: complexifying the real variables, the integral of `k (z, y)` is then
holomorphic, and its restriction to real `z` is real analytic.

## Main declarations

* `TauCeti.hasFDerivAt_integral_smul_of_analyticAt`: differentiation under the integral sign.
* `TauCeti.analyticAt_integral_smul`: analytic dependence of the integral on the parameter.
-/

public section

open Filter MeasureTheory Set Topology

namespace TauCeti

variable {E V Y α : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α]
  {μ : Measure α} {f : V × Y → E} {φ : α → Y} {g : α → ℂ} {K : Set Y}

/-- **Differentiation under the integral sign for a jointly analytic integrand.** If `f` is
jointly analytic at every point of `{p} × K`, with `K` compact, and `φ` is a continuous map with
values in `K`, then for every integrable weight `g` the integral `q ↦ ∫ a, g a • f (q, φ a) ∂μ`
has derivative at `p` the integral of the partial derivatives of `f` in the parameter. -/
theorem hasFDerivAt_integral_smul_of_analyticAt {p : V} (hK : IsCompact K) (hφ : Continuous φ)
    (hφK : ∀ a, φ a ∈ K) (hf : ∀ y ∈ K, AnalyticAt ℂ f (p, y)) (hg : Integrable g μ) :
    HasFDerivAt (fun q ↦ ∫ a, g a • f (q, φ a) ∂μ)
      (∫ a, g a • (fderiv ℂ f (p, φ a)).comp (ContinuousLinearMap.inl ℂ V Y) ∂μ) p := by
  -- The partial derivative of `f` in the parameter, continuous where `f` is analytic.
  set G : V × Y → V →L[ℂ] E := fun x ↦ (fderiv ℂ f x).comp (ContinuousLinearMap.inl ℂ V Y)
  -- Near `p`, `f` is analytic on `{q} × K` and `G` is bounded there uniformly in `q`.
  obtain ⟨C, hC⟩ := hK.exists_eventually_norm_le (F := G) (x₀ := p) (isOpen_analyticAt ℂ f)
    (fun y hy ↦ (hf y hy).fderiv.continuousAt.clm_comp continuousAt_const) hf
  set s := {q : V | ∀ y ∈ K, AnalyticAt ℂ f (q, y) ∧ ‖G (q, y)‖ ≤ C}
  have hs : s ∈ 𝓝 p := hC
  have hcont : ∀ q ∈ s, Continuous fun a ↦ f (q, φ a) := fun q hq ↦
    continuous_iff_continuousAt.2 fun a ↦
      (hq _ (hφK a)).1.continuousAt.comp_of_eq (f := fun a ↦ (q, φ a))
        (continuous_const.prodMk hφ).continuousAt rfl
  have hGcont : Continuous fun a ↦ G (p, φ a) := continuous_iff_continuousAt.2 fun a ↦
    ((hf _ (hφK a)).fderiv.continuousAt.clm_comp continuousAt_const).comp_of_eq
      (f := fun a ↦ (p, φ a)) (continuous_const.prodMk hφ).continuousAt rfl
  -- The integrand at `p` is bounded by a multiple of `‖g‖`, hence integrable.
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun y ↦ f (p, y)) fun y hy ↦
    ((hf y hy).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt
      ).continuousWithinAt
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun q a ↦ g a • G (q, φ a))
    (bound := fun a ↦ ‖g a‖ * C) hs
    (eventually_of_mem hs fun q hq ↦
      hg.aestronglyMeasurable.smul (hcont q hq).aestronglyMeasurable) ?_
    (hg.aestronglyMeasurable.smul hGcont.aestronglyMeasurable) ?_ (hg.norm.mul_const C) ?_
  · refine (hg.norm.mul_const B).mono'
      (hg.aestronglyMeasurable.smul (hcont p (mem_of_mem_nhds hs)).aestronglyMeasurable)
      (ae_of_all _ fun a ↦ ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hB _ (hφK a)) (norm_nonneg _)
  · refine ae_of_all _ fun a q hq ↦ ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hq _ (hφK a)).2 (norm_nonneg _)
  · refine ae_of_all _ fun a q hq ↦ ?_
    exact (((hq _ (hφK a)).1.differentiableAt.hasFDerivAt).comp q
      (hasFDerivAt_prodMk_left q (φ a))).const_smul (g a)

/-- **Analytic dependence of an integral on a parameter.** If `f` is jointly analytic at every
point of `{p} × K`, with `K` compact, and `φ` is a continuous map with values in `K`, then for
every integrable weight `g` the integral `q ↦ ∫ a, g a • f (q, φ a) ∂μ` is analytic at `p`. -/
theorem analyticAt_integral_smul [FiniteDimensional ℂ V] {p : V} (hK : IsCompact K)
    (hφ : Continuous φ) (hφK : ∀ a, φ a ∈ K) (hf : ∀ y ∈ K, AnalyticAt ℂ f (p, y))
    (hg : Integrable g μ) :
    AnalyticAt ℂ (fun q ↦ ∫ a, g a • f (q, φ a) ∂μ) p := by
  -- Analyticity of `f` on `{p} × K` persists on `{q} × K` for `q` near `p`, and the integral is
  -- differentiable at each such `q`.
  have h : ∀ᶠ q in 𝓝 p, ∀ y ∈ K, AnalyticAt ℂ f (q, y) :=
    hK.eventually_forall_of_forall_eventually fun y hy ↦ (hf y hy).eventually_analyticAt
  exact DifferentiableOn.analyticAt_of_finiteDimensional (fun q hq ↦
    (hasFDerivAt_integral_smul_of_analyticAt hK hφ hφK hq hg).differentiableAt
      |>.differentiableWithinAt) h

end TauCeti

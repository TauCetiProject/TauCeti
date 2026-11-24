/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.Distribution.TestFunction.Divergence
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Trace
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Topology.Algebra.Support

/-!
# The weak divergence of a weakly differentiable vector field

Let `g : E → E` be a vector field on an open set `Ω` of a finite-dimensional real inner product
space, with weak derivative `G : E → E →L[ℝ] E`. Its divergence is the trace of its derivative,
and this holds in the weak sense: for every test function `φ` on `Ω`,

`∫ ⟪∇φ, g⟫ = -∫ φ • tr G`.

Applied to the weak gradient `g` of a scalar function `u`, together with
`TauCeti.HasWeakFDerivOn.integral_laplacian_smul_eq_neg_integral_inner`, this gives the pairing
`∫ Δφ • u = ∫ φ • tr G`. For an additive Haar measure, it says that the distributional Laplacian
of a twice weakly differentiable function is the trace of its weak Hessian. This identity is what
makes the weak formulation `∫ Δφ • u = ∫ φ • f` of Poisson's equation `Δu = f` agree with the
strong one, `tr G = f` almost everywhere, for twice weakly differentiable `u`.

Dually, a weakly differentiable function `u : E → F` with weak derivative `U` pairs with the
divergence of a test vector field `φ` as `∫ div φ • u = -∫ U φ`. This identity only needs a
finite-dimensional real normed domain and a real normed codomain. For scalar `u`, it is the
identity behind total variation, a supremum of the left-hand side over `‖φ‖ ≤ 1`. Against an
additive Haar measure, taking `u = 1` gives `∫ div φ = 0`.

Applied to the test vector field `φ ∇χ` for a smooth cutoff `χ` compactly supported in `Ω`, whose
divergence is `⟪∇φ, ∇χ⟫ + φ Δχ`, the pairing localizes Poisson's equation: if `v` has weak
gradient `g` and solves `Δv = f` on `Ω`, then `Δ(χ v) = χ f + 2 ⟪∇χ, g⟫ + v Δχ` against every
smooth function on the whole space.

No boundedness or boundary regularity of `Ω` is used. Except for `∫ div φ = 0`, which needs an
additive Haar measure, the measure need not be a Haar measure: the trace identity, the Laplacian
identity and the pairing `∫ div φ • u = -∫ U φ` all come from the defining integration-by-parts
identities of weak derivatives. For a general measure these are adjoint identities relative to
`μ`; their usual distributional interpretation requires an additive Haar measure.

## Main declarations

* `TauCeti.HasWeakFDerivOn.integral_inner_gradient_eq_neg_integral_smul_trace`: the weak
  divergence of a weakly differentiable vector field is the trace of its weak derivative.
* `TauCeti.HasWeakFDerivOn.integral_laplacian_smul_eq_integral_smul_trace`: the Laplacian
  pairing of a twice weakly differentiable function is given by the trace of its weak Hessian.
* `TauCeti.HasWeakFDerivOn.integral_divergenceCLM_smul_eq_neg_integral`: a weakly differentiable
  function pairs with the divergence of a test vector field through its weak derivative.
* `TestFunction.integral_divergenceCLM_eq_zero`: the divergence of a test vector field has
  integral zero against an additive Haar measure.
* `TauCeti.HasWeakFDerivOn.integral_inner_gradient_add_mul_laplacian_mul_eq`: integration by
  parts against the divergence `⟪∇φ, ∇χ⟫ + φ Δχ` of a cutoff gradient field `φ ∇χ`.
* `TauCeti.HasWeakFDerivOn.integral_laplacian_mul_cutoff_mul_eq`: the weak Leibniz rule
  `Δ(χ v) = χ f + 2 ⟪∇χ, g⟫ + v Δχ` for a cutoff `χ` of a weak solution `v` of `Δv = f`.
* `TauCeti.dist_integral_trace_fderiv_mul_le`: the pairing `∫ div φ * u` of `C¹` vector fields
  supported in a fixed set `K` with a function integrable on `K` depends continuously on
  `Dφ` in the uniform norm.
* `TauCeti.continuousOn_trace_fderiv`, `TauCeti.integrable_mul_trace_fderiv`: the divergence
  `tr (DV)` of a `C¹` vector field is continuous, and integrable against a compactly supported
  continuous weight.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.1 and §6.3.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Gradient InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {μ : Measure E} {Ω : Opens E}

section InnerProductSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The weak divergence is the trace of the weak derivative.** If the vector field `g` has weak
derivative `G` on `Ω`, then for every test function `φ` on `Ω`,
`∫ ⟪∇φ, g⟫ ∂μ = -∫ φ • tr G ∂μ`. -/
theorem HasWeakFDerivOn.integral_inner_gradient_eq_neg_integral_smul_trace
    [OpensMeasurableSpace E] {g : E → E} {G : E → E →L[ℝ] E} (h : HasWeakFDerivOn μ Ω g G)
    (φ : 𝓓(Ω, ℝ)) :
    ∫ x, ⟪∇ (φ : E → ℝ) x, g x⟫_ℝ ∂μ =
      -∫ x, (φ : E → ℝ) x • LinearMap.trace ℝ E (G x) ∂μ := by
  set b := stdOrthonormalBasis ℝ E
  -- The component `⟪bᵢ, g⟫` has weak derivative `⟪bᵢ, G bᵢ⟫` in the direction `bᵢ`.
  have hdir : ∀ i, HasWeakLineDerivOn μ Ω (fun x => ⟪b i, g x⟫_ℝ)
      (fun x => ⟪b i, G x (b i)⟫_ℝ) (b i) := fun i => by
    simpa only [innerSL_apply_apply] using
      (h.hasWeakLineDerivOn (b i)).clm_comp (innerSL ℝ (b i))
  have hline : ∀ x v, lineDeriv ℝ (φ : E → ℝ) x v = fderiv ℝ (φ : E → ℝ) x v := fun x v =>
    (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv
  calc ∫ x, ⟪∇ (φ : E → ℝ) x, g x⟫_ℝ ∂μ
      = ∑ i, ∫ x, lineDeriv ℝ (φ : E → ℝ) x (b i) • ⟪b i, g x⟫_ℝ ∂μ := by
        rw [← integral_finsetSum _ fun i _ =>
          integrable_lineDeriv_smul_of_locallyIntegrableOn (hdir i).locallyIntegrableOn φ (b i)]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hline, smul_eq_mul, ← toDual_gradient, toDual_apply_apply]
        exact (b.sum_inner_mul_inner _ _).symm
    _ = ∑ i, -∫ x, (φ : E → ℝ) x • ⟪b i, G x (b i)⟫_ℝ ∂μ :=
        Finset.sum_congr rfl fun i _ => (hdir i).integral_lineDeriv_smul_eq_neg_integral_smul φ
    _ = -∫ x, (φ : E → ℝ) x • LinearMap.trace ℝ E (G x) ∂μ := by
        rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ =>
          φ.integrable_smul (hdir i).locallyIntegrableOn_deriv]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp [LinearMap.trace_eq_sum_inner _ b, Finset.mul_sum]

/-- **The Laplacian pairing is given by the trace of the weak Hessian.** If `u` has weak
gradient `g` on `Ω` and `g` has weak derivative `G` there, then for every test function `φ` on
`Ω`, `∫ Δφ • u ∂μ = ∫ φ • tr G ∂μ`. For an additive Haar measure, this identifies the
distributional Laplacian of `u` with the trace of its weak Hessian. -/
theorem HasWeakFDerivOn.integral_laplacian_smul_eq_integral_smul_trace [OpensMeasurableSpace E]
    {u : E → ℝ} {g : E → E} {G : E → E →L[ℝ] E}
    (hu : HasWeakFDerivOn μ Ω u fun x => innerSL ℝ (g x)) (hg : HasWeakFDerivOn μ Ω g G)
    (φ : 𝓓(Ω, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • u x ∂μ = ∫ x, (φ : E → ℝ) x • LinearMap.trace ℝ E (G x) ∂μ := by
  rw [hu.integral_laplacian_smul_eq_neg_integral_inner φ,
    hg.integral_inner_gradient_eq_neg_integral_smul_trace φ, neg_neg]

end InnerProductSpace

section NormedSpace

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Integration by parts against a divergence.** If `u : E → F` has weak derivative `U` on
`Ω`, then for every test vector field `φ` on `Ω`, `∫ div φ • u ∂μ = -∫ U φ ∂μ`. -/
theorem HasWeakFDerivOn.integral_divergenceCLM_smul_eq_neg_integral [OpensMeasurableSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U) (φ : 𝓓(Ω, E)) :
    ∫ x, TestFunction.divergenceCLM φ x • u x ∂μ = -∫ x, U x (φ x) ∂μ := by
  have := h.completeSpace
  let b := Module.finBasis ℝ E
  -- Coordinate functions replace inner products, so no inner product on `E` is needed.
  let ψ : Fin (Module.finrank ℝ E) → 𝓓(Ω, ℝ) := fun i =>
    TestFunction.postcompCLM (LinearMap.toContinuousLinearMap (b.coord i)) φ
  have hψ (i) : (ψ i : E → ℝ) = fun y => b.repr (φ y) i := by
    ext y
    simp [ψ]
  calc ∫ x, TestFunction.divergenceCLM φ x • u x ∂μ
      = ∑ i, ∫ x, lineDeriv ℝ (ψ i : E → ℝ) x (b i) • u x ∂μ := by
        simp_rw [TestFunction.divergenceCLM_apply_eq_sum b, ← hψ, Finset.sum_smul]
        exact integral_finsetSum _ fun i _ =>
          integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn (ψ i) (b i)
    _ = ∑ i, -∫ x, (ψ i : E → ℝ) x • U x (b i) ∂μ := Finset.sum_congr rfl fun i _ =>
        (h.hasWeakLineDerivOn (b i)).integral_lineDeriv_smul_eq_neg_integral_smul (ψ i)
    _ = -∫ x, U x (φ x) ∂μ := by
        rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ =>
          TestFunction.integrable_smul (ψ i) (h.hasWeakLineDerivOn (b i)).locallyIntegrableOn_deriv]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hψ]
        simpa only [map_sum, map_smul] using congrArg (U x) (b.sum_repr (φ x))

/-- The divergence of a test vector field has integral zero against an additive Haar measure:
`∫ div φ ∂μ = 0`. -/
theorem _root_.TestFunction.integral_divergenceCLM_eq_zero [BorelSpace E] [μ.IsAddHaarMeasure]
    (φ : 𝓓(Ω, E)) : ∫ x, TestFunction.divergenceCLM φ x ∂μ = 0 := by
  have h : HasWeakFDerivOn μ Ω (fun _ => (1 : ℝ)) 0 := hasWeakFDerivOn_iff.mpr fun v => by
    simpa using hasWeakLineDerivOn_const (μ := μ) (Ω := Ω) (v := v) (1 : ℝ)
  simpa using h.integral_divergenceCLM_smul_eq_neg_integral φ

omit [MeasurableSpace E] in
/-- The trace of the derivative of a vector field `V` is continuous on a set where `V` is `C¹`. -/
theorem continuousOn_trace_fderiv {V : E → E} {s : Set E} (hV : ∀ x ∈ s, ContDiffAt ℝ 1 V x) :
    ContinuousOn (fun x => LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E)) s := fun x hx => by
  simpa only [Function.comp_def, traceCLM_apply] using ((traceCLM ℝ E).continuous.continuousAt.comp
    ((hV x hx).fderiv_right (m := 0) le_rfl).continuousAt).continuousWithinAt

/-- If `χ` is continuous with compact support inside an open set `U` on which the vector field `V`
is `C¹`, then `χ tr (DV)` is integrable. This is the integrability of the right-hand side of the
weak divergence identity for a classical derivative. -/
theorem integrable_mul_trace_fderiv [OpensMeasurableSpace E] [IsFiniteMeasureOnCompacts μ]
    {U : Set E} (hU : IsOpen U) {χ : E → ℝ} {V : E → E} (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) (hV : ∀ x ∈ U, ContDiffAt ℝ 1 V x) :
    Integrable (fun x => χ x * LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E)) μ :=
  ((hχ.continuousOn.mul (continuousOn_trace_fderiv hV)).continuous_of_tsupport_subset hU
    (tsupport_mul_subset_left.trans hχU)).integrable_of_hasCompactSupport hχc.mul_right

/-- Vector fields supported in a fixed set `K` whose derivatives are uniformly close have
close divergence pairings `∫ div φ * u dμ` with a function `u` integrable on `K`. The constant is
the norm of the trace times `∫_K |u| dμ`. (If the two pairings are not integrable, both are `0`.) -/
theorem dist_integral_trace_fderiv_mul_le [OpensMeasurableSpace E] {u : E → ℝ} {K : Set E}
    (hu : IntegrableOn u K μ) {f g : E → E} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hfK : tsupport f ⊆ K) (hgK : tsupport g ⊆ K) {ε : ℝ}
    (hε : ∀ x, dist (fderiv ℝ f x) (fderiv ℝ g x) ≤ ε) :
    dist (∫ x, LinearMap.trace ℝ E (fderiv ℝ f x : E →ₗ[ℝ] E) * u x ∂μ)
      (∫ x, LinearMap.trace ℝ E (fderiv ℝ g x : E →ₗ[ℝ] E) * u x ∂μ) ≤
      ‖traceCLM ℝ E‖ * ε * ∫ x in K, ‖u x‖ ∂μ := by
  have hdiv {h : E → E} (hh : ContDiff ℝ 1 h) :
      Continuous fun x => LinearMap.trace ℝ E (fderiv ℝ h x : E →ₗ[ℝ] E) :=
    continuousOn_univ.mp (continuousOn_trace_fderiv fun x _ => hh.contDiffAt)
  -- Both integrands vanish off `K`, where `u` is integrable.
  have hvan {h : E → E} (hhK : tsupport h ⊆ K) (x : E) (hx : x ∉ K) :
      LinearMap.trace ℝ E (fderiv ℝ h x : E →ₗ[ℝ] E) * u x = 0 := by
    simp [image_eq_zero_of_notMem_tsupport fun h' => hx (hhK (tsupport_fderiv_subset ℝ h'))]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (hvan hfK),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (hvan hgK), dist_eq_norm]
  -- The difference of the two integrands is dominated by a multiple of `‖u‖`.
  have hbound : ∀ x, ‖(LinearMap.trace ℝ E (fderiv ℝ f x : E →ₗ[ℝ] E) -
      LinearMap.trace ℝ E (fderiv ℝ g x : E →ₗ[ℝ] E)) * u x‖ ≤ ‖traceCLM ℝ E‖ * ε * ‖u x‖ := by
    intro x
    have htr : LinearMap.trace ℝ E (fderiv ℝ f x : E →ₗ[ℝ] E) -
        LinearMap.trace ℝ E (fderiv ℝ g x : E →ₗ[ℝ] E) =
          traceCLM ℝ E (fderiv ℝ f x - fderiv ℝ g x) := by
      simp [map_sub]
    rw [htr, norm_mul]
    gcongr
    exact ((traceCLM ℝ E).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hε x) (norm_nonneg _))
  have hH : IntegrableOn (fun x => (LinearMap.trace ℝ E (fderiv ℝ f x : E →ₗ[ℝ] E) -
      LinearMap.trace ℝ E (fderiv ℝ g x : E →ₗ[ℝ] E)) * u x) K μ :=
    Integrable.mono' (hu.norm.const_mul _)
      (((hdiv hf).sub (hdiv hg)).aestronglyMeasurable.mul hu.aestronglyMeasurable)
      (Filter.Eventually.of_forall hbound)
  by_cases hF : IntegrableOn (fun x => LinearMap.trace ℝ E (fderiv ℝ f x : E →ₗ[ℝ] E) * u x) K μ
  · have hG : IntegrableOn (fun x => LinearMap.trace ℝ E (fderiv ℝ g x : E →ₗ[ℝ] E) * u x) K μ := by
      convert hF.sub hH using 2 with x
      simp only [Pi.sub_apply]
      ring
    rw [← integral_sub hF hG, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hu.norm.const_mul _)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [← sub_mul]
    exact hbound x
  · have hG : ¬ IntegrableOn
        (fun x => LinearMap.trace ℝ E (fderiv ℝ g x : E →ₗ[ℝ] E) * u x) K μ := fun hG => hF (by
      convert hG.add hH using 2 with x
      simp only [Pi.add_apply]
      ring)
    rw [integral_undef hF, integral_undef hG, sub_zero, norm_zero]
    have hε0 : 0 ≤ ε := (dist_nonneg).trans (hε 0)
    positivity

end NormedSpace

section Cutoff

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [OpensMeasurableSpace E]

/-- **Integration by parts against a cutoff gradient.** Let `v` have weak gradient `g` on `Ω` and
let `χ` be smooth with compact support in `Ω`. Then for every smooth `φ`,
`∫ (⟪∇φ, ∇χ⟫ + φ Δχ) v ∂μ = -∫ φ ⟪∇χ, g⟫ ∂μ`: the left side pairs `v` with `div (φ ∇χ)`, and
`φ ∇χ` is a test vector field on `Ω`. -/
theorem HasWeakFDerivOn.integral_inner_gradient_add_mul_laplacian_mul_eq {v : E → ℝ}
    {g : E → E} (hv : HasWeakFDerivOn μ Ω v fun x ↦ innerSL ℝ (g x)) {χ φ : E → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hφ : ContDiff ℝ ∞ φ) :
    ∫ x, (⟪∇ φ x, ∇ χ x⟫_ℝ + φ x * Δ χ x) * v x ∂μ = -∫ x, φ x * ⟪∇ χ x, g x⟫_ℝ ∂μ := by
  have hgχ : ContDiff ℝ ∞ (∇ χ) := hχ.gradient_right (m := ∞) (by simp)
  have hts : tsupport (fun x ↦ φ x • ∇ χ x) ⊆ tsupport χ :=
    (tsupport_smul_subset_right _ _).trans <|
      tsupport_subset_of_forall_notMem_eq_zero (fun _ ↦ gradient_of_notMem_tsupport)
        (isClosed_tsupport χ)
  let Φ : 𝓓(Ω, E) := ⟨fun x ↦ φ x • ∇ χ x, hφ.smul hgχ,
    hχc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hχΩ⟩
  have hΦ : (Φ : E → E) = fun x ↦ φ x • ∇ χ x := TestFunction.coe_mk
  -- The divergence of the test vector field `φ ∇χ` is `⟪∇φ, ∇χ⟫ + φ Δχ`.
  have hdiv : ∀ x, TestFunction.divergenceCLM Φ x = ⟪∇ φ x, ∇ χ x⟫_ℝ + φ x * Δ χ x := fun x ↦ by
    rw [TestFunction.divergenceCLM_apply, hΦ,
      trace_fderiv_smul (hφ.differentiable (by simp) x) (hgχ.differentiable (by simp) x),
      laplacian_eq_trace_iteratedGradientChain_one, iteratedGradientChain_succ,
      iteratedGradientChain_zero, inner_gradient_left, add_comm]
  simpa only [hdiv, hΦ, smul_eq_mul, innerSL_apply_apply, real_inner_smul_right,
    real_inner_comm (g _)] using hv.integral_divergenceCLM_smul_eq_neg_integral Φ

/-- **The Laplacian of a cutoff of a solution.** Let `v` have weak gradient `g` on `Ω` and solve
`Δv = f` against the test functions on `Ω`, and let `χ` be smooth with compact support in `Ω`.
Then `Δ(χ v) = χ f + 2 ⟪∇χ, g⟫ + v Δχ` against every smooth function on the whole space; no
support condition is needed on it, since `χ` has compact support. -/
theorem HasWeakFDerivOn.integral_laplacian_mul_cutoff_mul_eq {v f : E → ℝ} {g : E → E}
    (hv : HasWeakFDerivOn μ Ω v fun x ↦ innerSL ℝ (g x)) (hf : LocallyIntegrableOn f Ω μ)
    (h : ∀ φ : 𝓓(Ω, ℝ), ∫ x, Δ (φ : E → ℝ) x • v x ∂μ = ∫ x, (φ : E → ℝ) x • f x ∂μ)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∫ x, Δ φ x * (χ x * v x) ∂μ =
      ∫ x, φ x * (χ x * f x + 2 * ⟪∇ χ x, g x⟫_ℝ + Δ χ x * v x) ∂μ := by
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by simp)
  have hcgχ : Continuous (∇ χ) := (hχ.gradient_right (m := 0) (by simp)).continuous
  -- Integrability of the five terms, each a continuous coefficient vanishing off `tsupport χ`.
  have hint : ∀ {c q : E → ℝ}, Continuous c → (∀ x ∉ tsupport χ, c x = 0) →
      LocallyIntegrableOn q Ω μ → Integrable (fun x ↦ c x * q x) μ := fun {c _} hc hc0 hq ↦ by
    simpa only [smul_eq_mul] using hq.integrable_smul_left_of_hasCompactSupport hc.continuousOn
      (.intro hχc hc0)
      ((tsupport_subset_of_forall_notMem_eq_zero hc0 (isClosed_tsupport χ)).trans hχΩ)
  have I₁ : Integrable (fun x ↦ Δ (fun y ↦ χ y * φ y) x * v x) μ :=
    hint ((hχ.mul hφ).of_le (m := 2) (by simp)).continuous_laplacian (fun _ hx ↦
      laplacian_of_notMem_tsupport fun h ↦ hx (tsupport_mul_subset_left h)) hv.locallyIntegrableOn
  have I₂ : Integrable (fun x ↦ (⟪∇ φ x, ∇ χ x⟫_ℝ + φ x * Δ χ x) * v x) μ :=
    hint (((hφ.gradient_right (m := 0) (by simp)).continuous.inner hcgχ).add
      (hφ.continuous.mul hχ2.continuous_laplacian))
      (fun x hx ↦ by simp [gradient_of_notMem_tsupport hx, laplacian_of_notMem_tsupport hx])
      hv.locallyIntegrableOn
  have I₃ : Integrable (fun x ↦ φ x * Δ χ x * v x) μ := hint (hφ.continuous.mul
    hχ2.continuous_laplacian) (fun x hx ↦ by simp [laplacian_of_notMem_tsupport hx])
    hv.locallyIntegrableOn
  have I₄ : Integrable (fun x ↦ χ x * φ x * f x) μ := hint (hχ.continuous.mul hφ.continuous)
    (fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]) hf
  have I₅ : Integrable (fun x ↦ φ x * ⟪∇ χ x, g x⟫_ℝ) μ := by
    have h0 : ∀ x ∉ tsupport χ, φ x • ∇ χ x = 0 := fun x hx ↦ by
      simp [gradient_of_notMem_tsupport hx]
    simpa only [real_inner_smul_left] using
      hv.locallyIntegrableOn_gradient.integrable_inner_left_of_hasCompactSupport (𝕜 := ℝ)
        (g := fun x ↦ φ x • ∇ χ x) (hφ.continuous.smul hcgχ).continuousOn (.intro hχc h0)
        ((tsupport_subset_of_forall_notMem_eq_zero h0 (isClosed_tsupport χ)).trans hχΩ)
  -- Poisson's equation against `χ φ`, then split both sides by linearity.
  have hB : ∫ x, Δ (fun y ↦ χ y * φ y) x * v x ∂μ = ∫ x, χ x * φ x * f x ∂μ := by
    simpa only [TestFunction.coe_mk, smul_eq_mul] using
      h ⟨fun x ↦ χ x * φ x, hχ.mul hφ, hχc.mul_right, tsupport_mul_subset_left.trans hχΩ⟩
  have e₁ : ∫ x, Δ φ x * (χ x * v x) ∂μ = (∫ x, Δ (fun y ↦ χ y * φ y) x * v x ∂μ) -
      2 * (∫ x, (⟪∇ φ x, ∇ χ x⟫_ℝ + φ x * Δ χ x) * v x ∂μ) + ∫ x, φ x * Δ χ x * v x ∂μ := by
    rw [← integral_const_mul, ← integral_sub I₁ (I₂.const_mul 2),
      ← integral_add (f := fun x ↦ Δ (fun y ↦ χ y * φ y) x * v x -
        2 * ((⟪∇ φ x, ∇ χ x⟫_ℝ + φ x * Δ χ x) * v x)) (I₁.sub (I₂.const_mul 2)) I₃]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [hχ2.contDiffAt.laplacian_fun_mul (hφ.contDiffAt.of_le (by simp)),
      real_inner_comm (∇ φ x) (∇ χ x)]
    ring
  have e₂ : ∫ x, φ x * (χ x * f x + 2 * ⟪∇ χ x, g x⟫_ℝ + Δ χ x * v x) ∂μ =
      (∫ x, χ x * φ x * f x ∂μ) + 2 * (∫ x, φ x * ⟪∇ χ x, g x⟫_ℝ ∂μ) +
        ∫ x, φ x * Δ χ x * v x ∂μ := by
    rw [← integral_const_mul, ← integral_add I₄ (I₅.const_mul 2),
      ← integral_add (f := fun x ↦ χ x * φ x * f x + 2 * (φ x * ⟪∇ χ x, g x⟫_ℝ))
        (I₄.add (I₅.const_mul 2)) I₃]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)
  rw [e₁, e₂, hB, hv.integral_inner_gradient_add_mul_laplacian_mul_eq hχ hχc hχΩ hφ]
  ring

end Cutoff

end TauCeti

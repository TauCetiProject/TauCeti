/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.HeatEquation
public import TauCeti.Analysis.PDE.HeatKernel.Semigroup
public import TauCeti.Analysis.Semigroups.Generator.Basic
public import TauCeti.MeasureTheory.Function.Lp.WeakLaplacian
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Semigroups.Resolvent.Identity
import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic

/-!
# The generator of the heat semigroup is the Laplacian

Let `E` be a finite-dimensional real inner product space, `F` a real Banach space and
`1 ≤ p < ∞`. The heat semigroup `e^{tΔ}` on `Lᵖ(E; F)` (`TauCeti.heatSemigroup`) is convolution
with the heat kernel `K_t`. This file shows that on functions `φ` of class `C²` with compact
support its generator is the Laplacian:

`(e^{tΔ} φ - φ) / t → Δ φ` in `Lᵖ` as `t → 0⁺`,

so `φ` lies in the domain of the generator `A` and `A φ = Δ φ`. Here `Δ` is Mathlib's Laplacian,
the sum of the pure second derivatives, so that `e^{tΔ}` solves `∂ₜu = Δu`.

The proof is Duhamel's formula `(K_t ⋆ φ)(x) - φ(x) = ∫₀ᵗ (K_s ⋆ Δ φ)(x) ds` at every point `x`
(`TauCeti.heatKernel_convolution_sub_eq_integral`). Integrating over sets of finite measure and
exchanging the two integrals lifts this to the identity `e^{tΔ} φ - φ = ∫₀ᵗ e^{sΔ} (Δ φ) ds` of
`Lᵖ`-valued integrals. The average of the orbit of `Δ φ` over `(0, t]` tends to `Δ φ` by strong
continuity (`TauCeti.Semigroups.StronglyContinuousSemigroup.tendsto_average_orbit_zero`).

## The full generator

The generator is then identified completely: it is the Laplacian in the sense of distributions,
`TauCeti.weakLaplacianLp`, whose domain is `{f ∈ Lᵖ : Δf ∈ Lᵖ}`
(`TauCeti.generator_heatSemigroup_eq_weakLaplacianLp`). For scalar-valued functions and
`1 < p < ∞` this domain is the Sobolev space `W^{2,p}`, by the Calderón–Zygmund estimates, while
for `p = 1` and `dim E ≥ 2` it is strictly larger than `W^{2,1}`; neither identification is made
here.

One inclusion comes from mollification. For a kernel `ρ` of class `C²` with compact support,
convolution with `ρ` commutes with the heat semigroup, and the difference quotients of the
semigroup at `ρ ⋆ f` are convolutions of `f` with the `L¹` difference quotients at `ρ`. By Young's
inequality and the convergence above in `L¹`, they converge to `Δρ ⋆ f`
(`TauCeti.tendsto_heatSemigroup_convolutionLp_sub`). So `A (ρ ⋆ f) = Δρ ⋆ f = ρ ⋆ A f` for `f` in
the domain of `A`; both sides are continuous functions, and evaluating at `0` with `ρ = φ(-·)`
gives `∫ Δφ • f = ∫ φ • A f`. Thus `A` is a restriction of the distributional Laplacian. The two
operators agree because `1 - A` is onto, `A` being the generator of a contraction semigroup, while
`1 - Δ` is injective on `{f ∈ Lᵖ : Δf ∈ Lᵖ}` (`TauCeti.smul_sub_weakLaplacianLp_injective`).

## Main declarations

* `TauCeti.heatSemigroup_sub_eq_integral`: the identity
  `e^{tΔ} φ - φ = ∫₀ᵗ e^{sΔ} (Δ φ) ds` in `Lᵖ`, lifting Duhamel's formula
  `TauCeti.heatKernel_convolution_sub_eq_integral`,
  `e^{tΔ} φ - φ = ∫₀ᵗ e^{sΔ} (Δ φ) ds`.
* `TauCeti.tendsto_heatSemigroup_sub`: `(e^{tΔ} φ - φ) / t → Δ φ` in `Lᵖ`.
* `TauCeti.mem_domain_heatSemigroup` and `TauCeti.generator_heatSemigroup`: `φ` lies in the
  domain of the generator, which sends it to `Δ φ`.
* `TauCeti.tendsto_heatSemigroup_convolutionLp_sub`,
  `TauCeti.convolutionLp_mem_domain_heatSemigroup` and
  `TauCeti.generator_heatSemigroup_convolutionLp`: the same for mollified `Lᵖ` functions `ρ ⋆ f`,
  which the generator sends to `Δρ ⋆ f`.
* `TauCeti.generator_heatSemigroup_eq_weakLaplacianLp`: the generator is the Laplacian in the
  sense of distributions on its natural domain.
* `TauCeti.mem_domain_heatSemigroup_iff`: the domain of the generator consists of the `f ∈ Lᵖ`
  whose distributional Laplacian lies in `Lᵖ`.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.3.1 (the fundamental solution of the
  heat equation) and Section 7.4 (semigroup theory).
* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (the diffusion semigroup and its generator).
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter InnerProductSpace Laplacian _root_.MeasureTheory Semigroups Set
  Topology TopologicalSpace
open scoped Convolution Distributions ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {φ : E → F}

/-- **Duhamel's formula for the heat semigroup.** Let `φ` be of class `C²` with compact support,
and let `f, g ∈ Lᵖ` be the classes of `φ` and `Δ φ`. Then for `t > 0`,
`e^{tΔ} f - f = ∫₀ᵗ e^{sΔ} g ds` as `Lᵖ`-valued integrals. -/
theorem heatSemigroup_sub_eq_integral (hp : p ≠ ∞) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) {f g : Lp F p (volume : Measure E)} (hf : f =ᵐ[volume] φ)
    (hg : g =ᵐ[volume] Δ φ) {t : ℝ} (ht : 0 < t) :
    (heatSemigroup hp).realOperator t f - f =
      ∫ s in Ioc 0 t, (heatSemigroup hp).realOperator s g := by
  set S := (heatSemigroup (E := E) (F := F) hp).toStronglyContinuousSemigroup
  have hΔ := hφ.continuous_laplacian
  obtain ⟨C₂, hC₂⟩ := hΔ.bounded_above_of_compact_support hc.laplacian
  -- At a positive time the semigroup is represented by the classical heat convolution.
  have hrep : ∀ {s : ℝ} (hs : 0 < s) {h : Lp F p (volume : Measure E)} {ψ : E → F},
      h =ᵐ[volume] ψ → S.realOperator s h =ᵐ[volume] heatKernel s ⋆ ψ := by
    intro s hs h ψ hψ
    rw [heatSemigroup_realOperator hp hs]
    conv_lhs => rw [← Lp.toLp_coeFn h (Lp.memLp h)]
    exact (convolutionLp_ae_eq_convolution hp (integrable_heatKernel hs) (Lp.memLp h)).trans
      (EventuallyEq.of_eq (convolution_congr _ EventuallyEq.rfl hψ))
  have hint : IntegrableOn (fun s => S.realOperator s g) (Ioc 0 t) :=
    (S.continuous_realOperator_apply g).integrableOn_Ioc
  refine Lp.ext (ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun A _ hA => ?_)
    (fun A _ hA => ?_) fun A hAm hA => ?_)
  · have _ : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.2 hA.ne
    exact ((Lp.memLp _).restrict A).integrable Fact.out
  · have _ : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.2 hA.ne
    exact ((Lp.memLp _).restrict A).integrable Fact.out
  -- Integrate both sides over `A`, and exchange the time and space integrals on the right.
  have _ : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.2 hA.ne
  have _ : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hprod : Integrable (Function.uncurry fun s x => (heatKernel s ⋆ Δ φ) x)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict A)) := by
    refine (integrable_const C₂).mono'
      (stronglyMeasurable_heatKernel_convolution hΔ).aestronglyMeasurable ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod hAm)] with z hz
    exact norm_heatKernel_convolution_le hz.1.1 (ae_of_all _ hC₂) z.2
  set I := Set.setIntegralLp (𝕜 := ℝ) (F := F) (p := p) (μ := (volume : Measure E)) A hA
  calc ∫ x in A, (S.realOperator t f - f) x
      = ∫ x in A, ((heatKernel t ⋆ φ) x - φ x) := by
        refine integral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [Lp.coeFn_sub (S.realOperator t f) f, hrep ht hf, hf] with x h₁ h₂ h₃
        rw [h₁, Pi.sub_apply, h₂, h₃]
    _ = ∫ x in A, ∫ s in Ioc 0 t, (heatKernel s ⋆ Δ φ) x := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        dsimp only
        rw [heatKernel_convolution_sub_eq_integral hφ hc ht x,
          intervalIntegral.integral_of_le ht.le]
    _ = ∫ s in Ioc 0 t, ∫ x in A, (heatKernel s ⋆ Δ φ) x := (integral_integral_swap hprod).symm
    _ = ∫ s in Ioc 0 t, I (S.realOperator s g) := by
        refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
        rw [Set.setIntegralLp_apply]
        exact integral_congr_ae (ae_restrict_of_ae (hrep hs.1 hg).symm)
    _ = I (∫ s in Ioc 0 t, S.realOperator s g) := I.integral_comp_comm hint
    _ = ∫ x in A, (∫ s in Ioc 0 t, S.realOperator s g) x := Set.setIntegralLp_apply _ _ _

/-- **The heat semigroup differentiates `C²` data into its Laplacian.** Let `φ` be of class `C²`
with compact support, and let `f, g ∈ Lᵖ` be the classes of `φ` and `Δ φ`. Then
`(e^{tΔ} f - f) / t → g` in `Lᵖ` as `t → 0⁺`. -/
theorem tendsto_heatSemigroup_sub (hp : p ≠ ∞) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    {f g : Lp F p (volume : Measure E)} (hf : f =ᵐ[volume] φ) (hg : g =ᵐ[volume] Δ φ) :
    Tendsto (fun t => (1 / t) • ((heatSemigroup hp).realOperator t f - f)) (𝓝[>] 0) (𝓝 g) :=
  ((heatSemigroup hp).tendsto_average_orbit_zero g).congr'
    (eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) => by
      dsimp only
      rw [heatSemigroup_sub_eq_integral hp hφ hc hf hg ht])

/-- **`C²` functions with compact support lie in the domain of the heat generator.** -/
theorem mem_domain_heatSemigroup (hp : p ≠ ∞) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    {f : Lp F p (volume : Measure E)} (hf : f =ᵐ[volume] φ) :
    f ∈ (heatSemigroup hp).domain :=
  ((heatSemigroup hp).mem_domain_iff_tendsto f).2
    ⟨_, tendsto_heatSemigroup_sub hp hφ hc hf
      (hφ.continuous_laplacian.memLp_of_hasCompactSupport hc.laplacian).coeFn_toLp⟩

/-- **The generator of the heat semigroup is the Laplacian** on `C²` functions with compact
support: if `f, g ∈ Lᵖ` are the classes of `φ` and `Δ φ`, then the generator sends `f` to `g`. -/
theorem generator_heatSemigroup (hp : p ≠ ∞) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    {f g : Lp F p (volume : Measure E)} (hf : f =ᵐ[volume] φ) (hg : g =ᵐ[volume] Δ φ) :
    (heatSemigroup hp).generator ⟨f, by
      rw [StronglyContinuousSemigroup.generator_domain]
      exact mem_domain_heatSemigroup hp hφ hc hf⟩ = g :=
  (heatSemigroup hp).generator_eq_of_tendsto (mem_domain_heatSemigroup hp hφ hc hf)
    (tendsto_heatSemigroup_sub hp hφ hc hf hg)

/-! ### The full domain of the generator -/

/-- **The heat semigroup differentiates mollified `Lᵖ` functions.** Let `ρ` be of class `C²` with
compact support and `f ∈ Lᵖ`. Then `(e^{tΔ} (ρ ⋆ f) - ρ ⋆ f) / t → Δρ ⋆ f` in `Lᵖ` as `t → 0⁺`. -/
theorem tendsto_heatSemigroup_convolutionLp_sub (hp : p ≠ ∞) {ρ : E → ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hc : HasCompactSupport ρ) (f : Lp F p (volume : Measure E)) :
    Tendsto (fun t => (1 / t) • ((heatSemigroup hp).realOperator t (convolutionLp hp ρ volume f) -
      convolutionLp hp ρ volume f)) (𝓝[>] 0) (𝓝 (convolutionLp hp (Δ ρ) volume f)) := by
  have hρi : Integrable ρ volume := hρ.continuous.integrable_of_hasCompactSupport hc
  have hΔi : Integrable (Δ ρ) volume :=
    hρ.continuous_laplacian.integrable_of_hasCompactSupport hc.laplacian
  -- The difference between the quotient and its limit is convolution with the kernel `k t`.
  set k : ℝ → E → ℝ := fun t => (1 / t) • (heatKernel t ⋆[lsmul ℝ ℝ, volume] ρ - ρ) - Δ ρ
  have hop : ∀ t, 0 < t → convolutionLp hp (k t) volume f =
      (1 / t) • ((heatSemigroup hp).realOperator t (convolutionLp hp ρ volume f) -
        convolutionLp hp ρ volume f) - convolutionLp hp (Δ ρ) volume f := by
    intro t ht
    have hKρ : Integrable (heatKernel t ⋆[lsmul ℝ ℝ, volume] ρ) volume :=
      (integrable_heatKernel ht).integrable_convolution (lsmul ℝ ℝ) hρi
    rw [convolutionLp_sub hp ((hKρ.sub hρi).smul _) hΔi, convolutionLp_smul,
      convolutionLp_sub hp hKρ hρi, convolutionLp_convolution hp (integrable_heatKernel ht) hρi,
      heatSemigroup_realOperator hp ht]
    simp only [sub_apply, smul_apply, comp_apply]
  -- The kernels `k t` tend to `0` in `L¹`: this is the generator on `L¹` applied to `ρ`.
  have hL1 : Tendsto (fun t => ∫ x, ‖k t x‖) (𝓝[>] 0) (𝓝 0) := by
    have hρL := hρ.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 1) hc
    have hΔL := hρ.continuous_laplacian.memLp_of_hasCompactSupport (μ := volume) (p := 1)
      hc.laplacian
    have h := tendsto_heatSemigroup_sub (E := E) (F := ℝ) ENNReal.one_ne_top hρ hc
      hρL.coeFn_toLp hΔL.coeFn_toLp
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    refine h.congr' (eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) => ?_)
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    have hrep := convolutionLp_ae_eq_convolution ENNReal.one_ne_top (integrable_heatKernel ht) hρL
    rw [← heatSemigroup_realOperator ENNReal.one_ne_top ht] at hrep
    filter_upwards [Lp.coeFn_sub ((1 / t) • ((heatSemigroup ENNReal.one_ne_top).realOperator t
      (hρL.toLp ρ) - hρL.toLp ρ)) (hΔL.toLp (Δ ρ)), Lp.coeFn_smul (1 / t)
      ((heatSemigroup ENNReal.one_ne_top).realOperator t (hρL.toLp ρ) - hρL.toLp ρ),
      Lp.coeFn_sub ((heatSemigroup ENNReal.one_ne_top).realOperator t (hρL.toLp ρ))
      (hρL.toLp ρ), hρL.coeFn_toLp, hΔL.coeFn_toLp, hrep] with x h₁ h₂ h₃ h₄ h₅ h₆
    simp only [h₁, h₂, h₃, h₄, h₅, h₆, Pi.sub_apply, Pi.smul_apply, k]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using hL1.mul_const ‖f‖)
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [← hop t ht]
  exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (norm_convolutionLp_le hp _)
    (norm_nonneg _))

/-- **Mollified `Lᵖ` functions lie in the domain of the heat generator**: `ρ ⋆ f` does, for `ρ`
of class `C²` with compact support and `f ∈ Lᵖ`. -/
theorem convolutionLp_mem_domain_heatSemigroup (hp : p ≠ ∞) {ρ : E → ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hc : HasCompactSupport ρ) (f : Lp F p (volume : Measure E)) :
    convolutionLp hp ρ volume f ∈ (heatSemigroup hp).domain :=
  ((heatSemigroup hp).mem_domain_iff_tendsto _).2
    ⟨_, tendsto_heatSemigroup_convolutionLp_sub hp hρ hc f⟩

/-- **The heat generator on mollified `Lᵖ` functions**: it sends `ρ ⋆ f` to `Δρ ⋆ f`, for `ρ` of
class `C²` with compact support and `f ∈ Lᵖ`. -/
theorem generator_heatSemigroup_convolutionLp (hp : p ≠ ∞) {ρ : E → ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hc : HasCompactSupport ρ) (f : Lp F p (volume : Measure E)) :
    (heatSemigroup hp).generator ⟨convolutionLp hp ρ volume f, by
      rw [StronglyContinuousSemigroup.generator_domain]
      exact convolutionLp_mem_domain_heatSemigroup hp hρ hc f⟩ =
      convolutionLp hp (Δ ρ) volume f :=
  (heatSemigroup hp).generator_eq_of_tendsto (convolutionLp_mem_domain_heatSemigroup hp hρ hc f)
    (tendsto_heatSemigroup_convolutionLp_sub hp hρ hc f)

/-- Mollification commutes with the heat generator: if the difference quotients of the heat
semigroup at `f` converge to `g`, then `Δρ ⋆ f = ρ ⋆ g`. -/
private theorem convolutionLp_laplacian_eq_of_tendsto (hp : p ≠ ∞) {ρ : E → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hc : HasCompactSupport ρ) {f g : Lp F p (volume : Measure E)}
    (hfg : Tendsto (fun t => (1 / t) • ((heatSemigroup hp).realOperator t f - f)) (𝓝[>] 0)
      (𝓝 g)) :
    convolutionLp hp (Δ ρ) volume f = convolutionLp hp ρ volume g := by
  have hρi : Integrable ρ volume := hρ.continuous.integrable_of_hasCompactSupport hc
  refine tendsto_nhds_unique (tendsto_heatSemigroup_convolutionLp_sub hp hρ hc f) ?_
  refine (((convolutionLp hp ρ volume).continuous.tendsto _).comp hfg).congr'
    (eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) => ?_)
  beta_reduce
  rw [Function.comp_apply, map_smul, map_sub, heatSemigroup_realOperator hp ht,
    ← comp_apply (convolutionLp hp ρ volume),
    convolutionLp_comp_comm hp hρi (integrable_heatKernel ht), comp_apply]

/-- If the difference quotients of the heat semigroup at `f` converge to `g`, then `Δf = g` in
the sense of distributions: `∫ Δφ • f = ∫ φ • g` for every test function `φ`. -/
private theorem integral_laplacian_smul_eq_of_tendsto (hp : p ≠ ∞)
    {f g : Lp F p (volume : Measure E)}
    (hfg : Tendsto (fun t => (1 / t) • ((heatSemigroup hp).realOperator t f - f)) (𝓝[>] 0)
      (𝓝 g)) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • f x = ∫ x, φ x • g x := by
  -- Mollify with the reflected test function `ρ = φ(-·)` and evaluate at `0`.
  set ρ : E → ℝ := fun z => φ (-z) with hρ_def
  have hρ : ContDiff ℝ 2 ρ := (φ.contDiff.comp contDiff_neg).of_le (WithTop.coe_le_coe.2 le_top)
  have hρc : HasCompactSupport ρ := φ.hasCompactSupport.comp_homeomorph (Homeomorph.neg E)
  have hΔρ : Δ ρ = fun z => Δ (φ : E → ℝ) (-z) := by
    simpa only [zero_sub] using laplacian_comp_sub_left (φ : E → ℝ) 0
  -- Both sides of `Δρ ⋆ f = ρ ⋆ g` have continuous representatives, which therefore agree.
  have hrep : ∀ {k : E → ℝ}, Continuous k → HasCompactSupport k →
      ∀ h : Lp F p (volume : Measure E),
        convolutionLp hp k volume h =ᵐ[volume] k ⋆[lsmul ℝ ℝ, volume] h := by
    intro k hk hkc h
    conv_lhs => rw [← Lp.toLp_coeFn h (Lp.memLp h)]
    exact convolutionLp_ae_eq_convolution hp (hk.integrable_of_hasCompactSupport hkc) (Lp.memLp h)
  have hcont : ∀ {k : E → ℝ}, Continuous k → HasCompactSupport k →
      ∀ h : Lp F p (volume : Measure E), Continuous (k ⋆[lsmul ℝ ℝ, volume] h) :=
    fun hk hkc h => hkc.continuous_convolution_left _ hk ((Lp.memLp h).locallyIntegrable Fact.out)
  have heq : Δ ρ ⋆[lsmul ℝ ℝ, volume] f = ρ ⋆[lsmul ℝ ℝ, volume] g := by
    refine (Continuous.ae_eq_iff_eq volume (hcont hρ.continuous_laplacian hρc.laplacian _)
      (hcont hρ.continuous hρc g)).1 ?_
    refine (hrep hρ.continuous_laplacian hρc.laplacian _).symm.trans ?_
    rw [convolutionLp_laplacian_eq_of_tendsto hp hρ hρc hfg]
    exact hrep hρ.continuous hρc g
  have h0 := congrFun heq 0
  rwa [hΔρ, hρ_def, convolution_lsmul_comp_neg_apply_zero,
    convolution_lsmul_comp_neg_apply_zero] at h0

/-- **The generator of the heat semigroup on `Lᵖ` is the Laplacian in the sense of
distributions.** For `1 ≤ p < ∞` its domain is `{f ∈ Lᵖ : Δf ∈ Lᵖ}`, the `f ∈ Lᵖ` whose
distributional Laplacian lies in `Lᵖ`, and it sends such `f` to `Δf`. -/
theorem generator_heatSemigroup_eq_weakLaplacianLp (hp : p ≠ ∞) :
    (heatSemigroup (E := E) (F := F) hp).generator = weakLaplacianLp E F p := by
  have hres := (heatSemigroup (E := E) (F := F) hp).mem_resolventSet_generator one_pos
  refine LinearPMap.eq_of_le_of_smul_sub_surjective_of_injective (lambda := (1 : ℝ)) ?_
    (LinearPMap.smul_sub_bijective hres).surjective (smul_sub_weakLaplacianLp_injective one_pos)
  refine LinearPMap.le_of_le_graph fun fg hfg => ?_
  obtain ⟨f, hf₁, hf₂⟩ := (LinearPMap.mem_graph_iff _).1 hfg
  have hf : (f : Lp F p (volume : Measure E)) ∈ (heatSemigroup hp).domain := by
    rw [← StronglyContinuousSemigroup.generator_domain]
    exact f.2
  obtain ⟨g, hg⟩ := ((heatSemigroup hp).mem_domain_iff_tendsto _).1 hf
  have hfg' : (heatSemigroup hp).generator f = g :=
    (congrArg (heatSemigroup hp).generator (Subtype.ext rfl)).trans
      ((heatSemigroup hp).generator_eq_of_tendsto hf hg)
  rw [← Prod.mk.eta (p := fg), mem_graph_weakLaplacianLp_iff, ← hf₁, ← hf₂, hfg']
  exact integral_laplacian_smul_eq_of_tendsto hp hg

/-- **The domain of the heat generator on `Lᵖ`** consists of the `f ∈ Lᵖ` whose Laplacian in the
sense of distributions lies in `Lᵖ`. -/
theorem mem_domain_heatSemigroup_iff (hp : p ≠ ∞) {f : Lp F p (volume : Measure E)} :
    f ∈ (heatSemigroup hp).domain ↔
      ∃ g : Lp F p (volume : Measure E),
        ∀ φ : 𝓓((⊤ : Opens E), ℝ), ∫ x, Δ (φ : E → ℝ) x • f x = ∫ x, φ x • g x := by
  rw [← StronglyContinuousSemigroup.generator_domain, generator_heatSemigroup_eq_weakLaplacianLp,
    mem_domain_weakLaplacianLp_iff]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
public import TauCeti.Analysis.PDE.HeatKernel.HeatEquation
public import TauCeti.Analysis.PDE.HeatKernel.Semigroup
public import TauCeti.Analysis.Semigroups.Generator.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# The generator of the heat semigroup is the Laplacian

Let `E` be a finite-dimensional real inner product space, `F` a real Banach space and
`1 ≤ p < ∞`. The heat semigroup `e^{tΔ}` on `Lᵖ(E; F)` (`TauCeti.heatSemigroup`) is convolution
with the heat kernel `K_t`. This file shows that on functions `φ` of class `C²` with compact
support its generator is the Laplacian:

`(e^{tΔ} φ - φ) / t → Δ φ` in `Lᵖ` as `t → 0⁺`,

so `φ` lies in the domain of the generator `A` and `A φ = Δ φ`. Here `Δ` is Mathlib's Laplacian,
the sum of the pure second derivatives, so that `e^{tΔ}` solves `∂ₜu = Δu`.

The proof is Duhamel's formula. For `C²` data with compact support the Laplacian commutes with
convolution (`HasCompactSupport.laplacian_convolution_right`), so the heat equation reads
`∂ₛ (K_s ⋆ φ) = K_s ⋆ Δ φ`, and integrating in `s` from `0`, where `K_s ⋆ φ → φ`, gives

`(K_t ⋆ φ)(x) - φ(x) = ∫₀ᵗ (K_s ⋆ Δ φ)(x) ds`

at every point `x`. Integrating over sets of finite measure and exchanging the two integrals
lifts this to the identity `e^{tΔ} φ - φ = ∫₀ᵗ e^{sΔ} (Δ φ) ds` of `Lᵖ`-valued integrals. The
average of the orbit of `Δ φ` over `(0, t]` tends to `Δ φ` by strong continuity
(`TauCeti.Semigroups.StronglyContinuousSemigroup.tendsto_average_orbit_zero`).

This identifies the generator only on `C²` functions with compact support; its full domain is not
determined here. For `1 < p < ∞` that domain is the Sobolev space `W^{2,p}`, by the
Calderón–Zygmund estimates, while for `p = 1` it is strictly larger than `W^{2,1}`.

## Main declarations

* `TauCeti.hasDerivAt_heatKernel_convolution_of_hasCompactSupport`: the heat equation
  `∂ₜ (K_t ⋆ φ) = K_t ⋆ Δ φ` for `C²` data with compact support.
* `TauCeti.heatKernel_convolution_sub_eq_integral`: Duhamel's formula
  `(K_t ⋆ φ)(x) - φ(x) = ∫₀ᵗ (K_s ⋆ Δ φ)(x) ds`.
* `TauCeti.heatSemigroup_sub_eq_integral`: the same identity in `Lᵖ`,
  `e^{tΔ} φ - φ = ∫₀ᵗ e^{sΔ} (Δ φ) ds`.
* `TauCeti.tendsto_heatSemigroup_sub`: `(e^{tΔ} φ - φ) / t → Δ φ` in `Lᵖ`.
* `TauCeti.mem_domain_heatSemigroup` and `TauCeti.generator_heatSemigroup`: `φ` lies in the
  domain of the generator, which sends it to `Δ φ`.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.3.1 (the fundamental solution of the
  heat equation) and Section 7.4 (semigroup theory).
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter InnerProductSpace Laplacian MeasureTheory Semigroups Set Topology
open scoped Convolution ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {φ : E → F}

/-- **The heat equation for `C²` data with compact support.** For `t > 0`, the function
`s ↦ (K_s ⋆ φ)(x)` has derivative `(K_t ⋆ Δ φ)(x)` at `t`: the Laplacian of the solution is the
heat convolution of the Laplacian of the datum. -/
theorem hasDerivAt_heatKernel_convolution_of_hasCompactSupport (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => (heatKernel s ⋆ φ) x) ((heatKernel t ⋆ Δ φ) x) t := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hc
  have h := hasDerivAt_heatKernel_convolution ht hφ.continuous.aestronglyMeasurable
    (ae_of_all _ hC) x
  rwa [hc.laplacian_convolution_right _ (integrable_heatKernel ht).locallyIntegrable hφ] at h

/-- **Duhamel's formula for the heat equation.** For `φ` of class `C²` with compact support and
`t > 0`, `(K_t ⋆ φ)(x) - φ(x) = ∫₀ᵗ (K_s ⋆ Δ φ)(x) ds` at every point `x`. -/
theorem heatKernel_convolution_sub_eq_integral (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    {t : ℝ} (ht : 0 < t) (x : E) :
    (heatKernel t ⋆ φ) x - φ x = ∫ s in 0..t, (heatKernel s ⋆ Δ φ) x := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hc
  obtain ⟨C₂, hC₂⟩ := hφ.continuous_laplacian.bounded_above_of_compact_support hc.laplacian
  -- The integrand is continuous at positive times, being differentiable there, and bounded.
  have hcont : ContinuousOn (fun s => (heatKernel s ⋆ Δ φ) x) (Ioi 0) := fun s hs =>
    (hasDerivAt_heatKernel_convolution hs hφ.continuous_laplacian.aestronglyMeasurable
      (ae_of_all _ hC₂) x).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun s => (heatKernel s ⋆ Δ φ) x) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    refine (integrableOn_const (C := C₂) measure_Ioc_lt_top.ne).mono'
      ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact norm_heatKernel_convolution_le hs.1 (ae_of_all _ hC₂) x
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht
    (fun s hs => hasDerivAt_heatKernel_convolution_of_hasCompactSupport hφ hc hs.1 x) hint
    ?_ ?_).symm
  · exact (tendsto_heatKernel_convolution hφ.continuous.aestronglyMeasurable (ae_of_all _ hC)
      hφ.continuous.continuousAt).comp (tendsto_id.prodMk tendsto_const_nhds)
  · exact (hasDerivAt_heatKernel_convolution_of_hasCompactSupport hφ hc ht x).continuousAt.tendsto
      |>.mono_left nhdsWithin_le_nhds

omit [CompleteSpace F] in
/-- The heat convolution of a continuous function is jointly strongly measurable in time
and space. -/
private theorem stronglyMeasurable_heatKernel_convolution {g : E → F} (hg : Continuous g) :
    StronglyMeasurable fun z : ℝ × E => (heatKernel z.1 ⋆ g) z.2 := by
  have hK : Measurable fun q : ℝ × E => heatKernel q.1 q.2 := by
    simp only [heatKernel_apply]
    fun_prop
  simp only [convolution_def, lsmul_apply]
  refine StronglyMeasurable.integral_prod_right
    (f := fun (z : ℝ × E) (y : E) => heatKernel z.1 y • g (z.2 - y)) ?_
  exact (hK.comp (measurable_fst.fst.prodMk measurable_snd)).stronglyMeasurable.smul
    (hg.comp (continuous_fst.snd.sub continuous_snd)).stronglyMeasurable

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
    have hs' : s.toNNReal ≠ 0 := (Real.toNNReal_pos.2 hs).ne'
    rw [S.realOperator_def, ContractionSemigroup.toStronglyContinuousSemigroup_apply]
    refine (heatSemigroup_ae_eq_convolution_coeFn hp hs' h).trans (EventuallyEq.of_eq ?_)
    rw [Real.coe_toNNReal _ hs.le]
    exact convolution_congr _ EventuallyEq.rfl hψ
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
  set I := Set.setIntegralLp (𝕜 := ℝ) (F := F) (p := p) (mu := (volume : Measure E)) A hA
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

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Semigroup
public import TauCeti.Analysis.Semigroups.Resolvent.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.HeatKernel.Generator
import TauCeti.Analysis.Semigroups.Resolvent.Identity
import TauCeti.MeasureTheory.Function.Lp.Dilation

/-!
# The resolvent of the heat semigroup

On a finite-dimensional real inner product space `E` of dimension `n`, the heat semigroup
`e^{tΔ}` on `Lᵖ(E; F)`, `1 ≤ p < ∞` (`TauCeti.heatSemigroup`), is convolution with the heat
kernel `K_t`. Its resolvent at `λ > 0` is the Laplace transform
`(λ - Δ)⁻¹ f = ∫₀^∞ e^{-λt} e^{tΔ} f dt` (`TauCeti.Semigroups.ContractionSemigroup.resolvent`).
This file shows that it is again a convolution operator, whose kernel is the Laplace transform
of the heat kernel,

`G_λ(x) = ∫₀^∞ e^{-λt} K_t(x) dt`

(`TauCeti.heatResolventKernel`). This kernel is nonnegative, radial and integrable, with mass
`∫ G_λ = 1 / λ` (`TauCeti.integral_heatResolventKernel`), so Young's inequality bounds the
resolvent on `Lᵖ` by `1 / λ`, the Hille–Yosida bound of a contraction semigroup. This bound is
attained: `‖(λ - Δ)⁻¹‖ = 1 / λ` on `Lᵖ(E; F)` for every nontrivial `F`
(`TauCeti.norm_resolvent_heatSemigroup`).

In dimension one `G_λ(x) = e^{-√λ |x|} / (2 √λ)`, the Green function of `λ - d²/dx²` on the
line. In dimension `n ≥ 2` it is expressed through the modified Bessel function
`K_{n/2 - 1}(√λ |x|)` and is singular at the origin, where the defining integral diverges and
the Bochner integral takes its junk value `0`. This one point is a null set and does not affect
the convolution.

## The arguments

The kernel identity exchanges the time integral of the resolvent with the space integral of the
convolution: the integrand `(t, y) ↦ e^{-λt} K_t(y) • f(· - y)` is integrable on
`(0, ∞) × E`, because `K_t` has mass one and the translates of `f` have norm `‖f‖`.

For the lower bound on the norm, the dilates `φ(r⁻¹ ·)` of a smooth compactly supported `φ ≠ 0`
are approximate solutions of `Δ u = 0`: they lie in the domain of the generator, which acts on
them as the Laplacian (`TauCeti.generator_heatSemigroup`), and their Laplacian has `Lᵖ` norm `r⁻²`
times smaller than their own. Writing `φ(r⁻¹ ·) = (λ - Δ)⁻¹ (λ φ(r⁻¹ ·) - Δ φ(r⁻¹ ·))` therefore
gives `1 ≤ λ ‖(λ - Δ)⁻¹‖ + O(r⁻²)`, and `r → ∞` gives `λ ‖(λ - Δ)⁻¹‖ ≥ 1`.

## Main declarations

* `TauCeti.heatResolventKernel`: the kernel `G_λ(x) = ∫₀^∞ e^{-λt} K_t(x) dt`.
* `TauCeti.integrable_heatResolventKernel` and `TauCeti.integral_heatResolventKernel`: `G_λ` is
  integrable with mass `1 / λ`.
* `TauCeti.resolvent_heatSemigroup`: the resolvent of the heat semigroup on `Lᵖ` is convolution
  with `G_λ`.
* `TauCeti.resolvent_heatSemigroup_ae_eq_convolution`,
  `TauCeti.resolvent_heatSemigroup_ae_eq_convolution_coeFn`: pointwise, `(λ - Δ)⁻¹ f` is
  represented almost everywhere by the classical convolution `G_λ ⋆ f`.
* `TauCeti.norm_resolvent_heatSemigroup`: the resolvent has operator norm exactly `1 / λ`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (the diffusion semigroup) and Theorem II.1.10 (the resolvent as a Laplace
  transform).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V,
  §3.1 (Bessel kernels as superpositions of heat kernels).
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian MeasureTheory Semigroups Set Real Topology
open scoped Convolution ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {lambda : ℝ}

/-- The **resolvent kernel of the heat semigroup**, the Laplace transform of the heat kernel in
time: `G_λ(x) = ∫₀^∞ e^{-λt} K_t(x) dt`. For `λ > 0` it is integrable with mass `1 / λ`
(`TauCeti.integral_heatResolventKernel`), and convolution with it is the resolvent `(λ - Δ)⁻¹`
of the heat semigroup (`TauCeti.resolvent_heatSemigroup`). -/
def heatResolventKernel (lambda : ℝ) (x : E) : ℝ :=
  ∫ t in Ioi 0, exp (-(lambda * t)) * heatKernel t x

/-- The defining integral of the heat resolvent kernel. -/
theorem heatResolventKernel_apply (lambda : ℝ) (x : E) :
    heatResolventKernel lambda x = ∫ t in Ioi 0, exp (-(lambda * t)) * heatKernel t x :=
  (rfl)

/-- The heat resolvent kernel is nonnegative. -/
theorem heatResolventKernel_nonneg (lambda : ℝ) (x : E) : 0 ≤ heatResolventKernel lambda x :=
  setIntegral_nonneg measurableSet_Ioi fun t (ht : 0 < t) ↦
    mul_nonneg (exp_pos _).le (heatKernel_pos ht x).le

/-- The heat resolvent kernel is even. -/
@[simp]
theorem heatResolventKernel_neg (lambda : ℝ) (x : E) :
    heatResolventKernel lambda (-x) = heatResolventKernel lambda x := by
  simp only [heatResolventKernel_apply, heatKernel_neg]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The space-time integrand `(t, x) ↦ e^{-λt} K_t(x)` of the heat resolvent kernel is
integrable on `(0, ∞) × E`. -/
theorem integrable_heatResolventKernel_integrand (hlambda : 0 < lambda) :
    Integrable (fun z : ℝ × E ↦ exp (-(lambda * z.1)) * heatKernel z.1 z.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hmeas : AEStronglyMeasurable (fun z : ℝ × E ↦ exp (-(lambda * z.1)) * heatKernel z.1 z.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
    have hc : ContinuousOn (fun z : ℝ × E ↦ exp (-(lambda * z.1)) * heatKernel z.1 z.2)
        (Ioi 0 ×ˢ univ) :=
      (by fun_prop : Continuous fun z : ℝ × E ↦ exp (-(lambda * z.1))).continuousOn.mul
        continuousOn_uncurry_heatKernel
    have h := hc.aestronglyMeasurable (μ := (volume : Measure ℝ).prod (volume : Measure E))
      (measurableSet_Ioi.prod .univ)
    rwa [← Measure.prod_restrict, Measure.restrict_univ] at h
  refine (integrable_prod_iff hmeas).2 ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    exact (integrable_heatKernel ht).const_mul _
  · refine (exp_neg_integrableOn_Ioi 0 hlambda).congr_fun (fun t (ht : 0 < t) ↦ ?_)
      measurableSet_Ioi
    simp_rw [norm_mul, norm_of_nonneg (exp_pos _).le, norm_of_nonneg (heatKernel_pos ht _).le,
      integral_const_mul, integral_heatKernel ht, mul_one, neg_mul]

/-- **The heat resolvent kernel is integrable** for `λ > 0`. -/
theorem integrable_heatResolventKernel (hlambda : 0 < lambda) :
    Integrable (heatResolventKernel lambda : E → ℝ) :=
  (integrable_heatResolventKernel_integrand hlambda).integral_prod_right

/-- **The mass of the heat resolvent kernel**: `∫ G_λ = 1 / λ` for `λ > 0`. -/
@[simp]
theorem integral_heatResolventKernel (hlambda : 0 < lambda) :
    ∫ x : E, heatResolventKernel lambda x = lambda⁻¹ := by
  have hswap := integral_integral_swap (f := fun t (x : E) ↦ exp (-(lambda * t)) * heatKernel t x)
    (integrable_heatResolventKernel_integrand hlambda)
  simp only [heatResolventKernel_apply]
  rw [← hswap, setIntegral_congr_fun measurableSet_Ioi (g := fun t ↦ exp ((-lambda) * t))
    fun t (ht : 0 < t) ↦ by simp [integral_const_mul, integral_heatKernel ht],
    integral_exp_mul_Ioi (neg_neg_iff_pos.2 hlambda)]
  simp

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The resolvent of the heat semigroup is convolution with the heat resolvent kernel.** For
`1 ≤ p < ∞` and `λ > 0`, the resolvent `(λ - Δ)⁻¹ = ∫₀^∞ e^{-λt} e^{tΔ} dt` of the heat semigroup
on `Lᵖ(E; F)` is convolution with `G_λ = ∫₀^∞ e^{-λt} K_t dt`. -/
theorem resolvent_heatSemigroup (hp : p ≠ ∞) (hlambda : 0 < lambda) :
    (heatSemigroup (E := E) (F := F) hp).resolvent lambda hlambda =
      convolutionLp hp (heatResolventKernel lambda) volume := by
  ext1 f
  set τ : E → Lp F p (volume : Measure E) := fun y ↦ volume.translateLp p (-y) f with hτ
  have hτc : Continuous τ := (Measure.continuous_translateLp hp f).comp continuous_neg
  -- The integrand `(t, y) ↦ e^{-λt} K_t(y) • f(· - y)` is integrable on `(0, ∞) × E`.
  have hint : Integrable (Function.uncurry fun t y ↦ (exp (-(lambda * t)) * heatKernel t y) • τ y)
      ((volume.restrict (Ioi 0)).prod volume) :=
    (integrable_heatResolventKernel_integrand hlambda).smul_of_top_left <| memLp_top_of_bound
      (hτc.comp continuous_snd).aestronglyMeasurable ‖f‖
      (ae_of_all _ fun _ ↦ (LinearIsometryEquiv.norm_map _ f).le)
  rw [ContractionSemigroup.resolvent_apply,
    convolutionLp_apply hp (integrable_heatResolventKernel hlambda)]
  calc ∫ t in Ioi 0, exp (-(lambda * t)) • (heatSemigroup hp).realOperator t f
      = ∫ t in Ioi 0, ∫ y, (exp (-(lambda * t)) * heatKernel t y) • τ y := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
        rw [heatSemigroup_realOperator hp ht, convolutionLp_apply hp (integrable_heatKernel ht),
          ← integral_smul]
        simp only [hτ, smul_smul]
    _ = ∫ y, ∫ t in Ioi 0, (exp (-(lambda * t)) * heatKernel t y) • τ y :=
        integral_integral_swap hint
    _ = ∫ y, heatResolventKernel lambda y • volume.translateLp p (-y) f := by
        simp only [integral_smul_const, heatResolventKernel_apply, hτ]

/-- **The pointwise representative of the heat resolvent.** For `1 ≤ p < ∞`, `λ > 0` and
`f ∈ Lᵖ`, the class `(λ - Δ)⁻¹ f` is represented almost everywhere by the classical convolution
`(G_λ ⋆ f)(x) = ∫ y, G_λ(y) • f(x - y) dy`. -/
theorem resolvent_heatSemigroup_ae_eq_convolution (hp : p ≠ ∞) (hlambda : 0 < lambda)
    {f : E → F} (hf : MemLp f p volume) :
    (heatSemigroup hp).resolvent lambda hlambda (hf.toLp f) =ᵐ[volume]
      heatResolventKernel lambda ⋆ f := by
  rw [resolvent_heatSemigroup hp hlambda]
  exact convolutionLp_ae_eq_convolution hp (integrable_heatResolventKernel hlambda) hf

/-- For `1 ≤ p < ∞` and `λ > 0`, the heat resolvent applied to `f : Lp` is represented almost
everywhere by convolution of `G_λ` with the chosen representative of `f`. -/
theorem resolvent_heatSemigroup_ae_eq_convolution_coeFn (hp : p ≠ ∞) (hlambda : 0 < lambda)
    (f : Lp F p (volume : Measure E)) :
    (heatSemigroup hp).resolvent lambda hlambda f =ᵐ[volume]
      heatResolventKernel lambda ⋆ (f : E → F) := by
  simpa only [Lp.toLp_coeFn] using
    resolvent_heatSemigroup_ae_eq_convolution hp hlambda (Lp.memLp f)

/-- An element `f` of the generator domain of the heat semigroup, with generator value `g`,
satisfies `‖f‖ ≤ λ ‖(λ - Δ)⁻¹‖ ‖f‖ + λ⁻¹ ‖g‖`: write `f = (λ - Δ)⁻¹ (λ f - g)`. -/
private theorem norm_le_mul_norm_resolvent_heatSemigroup_add (hp : p ≠ ∞) (hlambda : 0 < lambda)
    {f g : Lp F p (volume : Measure E)} (hf : f ∈ (heatSemigroup (E := E) (F := F) hp).domain)
    (hg : (heatSemigroup (E := E) (F := F) hp).generator
      ⟨f, by rwa [StronglyContinuousSemigroup.generator_domain]⟩ = g) :
    ‖f‖ ≤ lambda * ‖(heatSemigroup (E := E) (F := F) hp).resolvent lambda hlambda‖ * ‖f‖ +
      lambda⁻¹ * ‖g‖ := by
  set S := heatSemigroup (E := E) (F := F) hp
  set R := S.resolvent lambda hlambda
  have hleft := S.resolventLeftInv lambda hlambda ⟨f, hf⟩
  rw [hg] at hleft
  have hR : ‖R‖ ≤ lambda⁻¹ := (S.resolvent_norm_le lambda hlambda).trans_eq (one_div _)
  calc ‖f‖ = ‖R (lambda • f - g)‖ := by rw [hleft]
    _ ≤ ‖R‖ * (lambda * ‖f‖ + ‖g‖) := by
        refine (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        refine (norm_sub_le _ _).trans_eq ?_
        rw [norm_smul, norm_of_nonneg hlambda.le]
    _ = lambda * ‖R‖ * ‖f‖ + ‖R‖ * ‖g‖ := by ring
    _ ≤ lambda * ‖R‖ * ‖f‖ + lambda⁻¹ * ‖g‖ := by gcongr

/-- **The norm of the heat resolvent.** For `1 ≤ p < ∞`, `λ > 0` and a nontrivial Banach space
`F`, the resolvent `(λ - Δ)⁻¹` of the heat semigroup on `Lᵖ(E; F)` has operator norm exactly
`1 / λ`: the Hille–Yosida bound of a contraction semigroup is attained. -/
@[simp]
theorem norm_resolvent_heatSemigroup [Nontrivial F] (hp : p ≠ ∞) (hlambda : 0 < lambda) :
    ‖(heatSemigroup (E := E) (F := F) hp).resolvent lambda hlambda‖ = lambda⁻¹ := by
  set R := (heatSemigroup (E := E) (F := F) hp).resolvent lambda hlambda
  refine le_antisymm (((heatSemigroup hp).resolvent_norm_le lambda hlambda).trans_eq
    (one_div _)) ?_
  -- A nonzero smooth compactly supported test function `φ = b • v`.
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  let b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  set φ : E → F := fun x ↦ b x • v
  have hφ : ContDiff ℝ 2 φ := b.contDiff.smul contDiff_const
  have hφc : HasCompactSupport φ := b.hasCompactSupport.smul_right
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set a := (eLpNorm φ p volume).toReal
  set c := (eLpNorm (Δ φ) p volume).toReal
  have ha : 0 < a := by
    refine ENNReal.toReal_pos (fun h ↦ hv ?_)
      (hφ.continuous.memLp_of_hasCompactSupport hφc).eLpNorm_ne_top
    have h0 := (Continuous.ae_eq_iff_eq volume hφ.continuous continuous_const).1
      ((eLpNorm_eq_zero_iff hp0).1 h)
    have hb0 : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    have h1 := congr_fun h0 0
    simp only [φ, hb0, one_smul] at h1
    exact h1
  -- For every `r > 0`, the dilate `φ(r⁻¹ ·)` gives `1 ≤ λ ‖R‖ + λ⁻¹ r⁻² c / a`.
  have key : ∀ r : ℝ, 0 < r → 1 ≤ lambda * ‖R‖ + lambda⁻¹ * (r ^ 2)⁻¹ * (c / a) := by
    intro r hr
    set φr : E → F := fun x ↦ φ (r⁻¹ • x)
    have hφr : ContDiff ℝ 2 φr := hφ.comp (contDiff_const_smul _)
    have hφrc : HasCompactSupport φr := hφc.comp_smul (inv_ne_zero hr.ne')
    have hf := hφr.continuous.memLp_of_hasCompactSupport (μ := volume) (p := p) hφrc
    have hg := hφr.continuous_laplacian.memLp_of_hasCompactSupport (μ := volume) (p := p)
      hφrc.laplacian
    have h := norm_le_mul_norm_resolvent_heatSemigroup_add hp hlambda
      (mem_domain_heatSemigroup hp hφr hφrc hf.coeFn_toLp)
      (generator_heatSemigroup hp hφr hφrc hf.coeFn_toLp hg.coeFn_toLp)
    -- The `Lᵖ` norms of the dilate and of its Laplacian scale like `r^{n/p}` and `r^{n/p - 2}`.
    set s := r ^ ((Module.finrank ℝ E : ℝ) / p.toReal)
    have hs : 0 < s := by positivity
    have hnf : ‖hf.toLp φr‖ = s * a := by
      rw [Lp.norm_toLp, Measure.eLpNorm_comp_inv_smul volume φ hr.ne', abs_of_pos hr]
      simp [ENNReal.toReal_ofReal hs.le, s, a]
    have hng : ‖hg.toLp (Δ φr)‖ = (r ^ 2)⁻¹ * (s * c) := by
      have hΔ : Δ φr = (r⁻¹) ^ 2 • fun x ↦ Δ φ (r⁻¹ • x) := laplacian_comp_smul_right r⁻¹ φ
      rw [Lp.norm_toLp, hΔ, eLpNorm_const_smul, Measure.eLpNorm_comp_inv_smul volume _ hr.ne',
        abs_of_pos hr]
      simp [ENNReal.toReal_ofReal hs.le, abs_of_pos hr, s, c]
    rw [hnf, hng] at h
    refine le_of_mul_le_mul_right ?_ (mul_pos hs ha)
    calc 1 * (s * a) ≤ lambda * ‖R‖ * (s * a) + lambda⁻¹ * ((r ^ 2)⁻¹ * (s * c)) := by
          rwa [one_mul]
      _ = (lambda * ‖R‖ + lambda⁻¹ * (r ^ 2)⁻¹ * (c / a)) * (s * a) := by
          field_simp
  -- Let `r → ∞`.
  have hlim : Tendsto (fun r : ℝ ↦ lambda * ‖R‖ + lambda⁻¹ * (r ^ 2)⁻¹ * (c / a)) atTop
      (𝓝 (lambda * ‖R‖)) := by
    have h0 : Tendsto (fun r : ℝ ↦ (r ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)
    simpa using tendsto_const_nhds.add ((h0.const_mul lambda⁻¹).mul_const (c / a))
  have h1 : 1 ≤ lambda * ‖R‖ := ge_of_tendsto hlim ((eventually_gt_atTop 0).mono key)
  rwa [inv_le_iff_one_le_mul₀' hlambda]

end TauCeti

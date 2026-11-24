/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Semigroup
public import TauCeti.Analysis.Semigroups.Resolvent.Identity
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Normed.Operator.Resolvent.LowerBound
import TauCeti.Analysis.PDE.HeatKernel.Generator
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The resolvent of the heat semigroup

Let `E` be a finite-dimensional real inner product space of dimension `n`. For `λ > 0` the
**resolvent kernel** of the heat equation is the Laplace transform of the heat kernel `K_t` in
time,

`G_λ(x) = ∫₀^∞ e^{-λt} K_t(x) dt` (`TauCeti.heatResolventKernel`).

It is nonnegative, even and integrable with mass `∫ G_λ = 1 / λ`, and its Fourier transform is
`𝓕 G_λ(ξ) = (λ + 4π² ‖ξ‖²)⁻¹`, the reciprocal of the symbol of `λ - Δ` in Mathlib's normalization
of the Fourier transform. So `G_λ` is the Bessel-type kernel of `λ - Δ`.

The main theorem identifies the resolvent of the heat semigroup `e^{tΔ}` on `Lᵖ(E; F)`,
`1 ≤ p < ∞`: for `λ > 0`,

`(λ - A)⁻¹ f = ∫₀^∞ e^{-λt} e^{tΔ} f dt = G_λ ⋆ f`,

where `A` is the generator `(heatSemigroup hp).generator` of the heat semigroup
(`TauCeti.resolvent_heatSemigroup`, `TauCeti.resolvent_generator_heatSemigroup`).
In particular `u = G_λ ⋆ f` lies in the domain of `A` and solves `λ u - A u = f`. As a
convolution with a nonnegative kernel of mass `1 / λ`, the resolvent preserves positivity, has
norm at most `1 / λ` on every `Lᵖ` by Young's inequality, and on `L¹` it scales the integral by
`1 / λ`. The bound `1 / λ` is attained: `‖(λ - A)⁻¹‖ = 1 / λ` on `Lᵖ(E; F)` for every
nontrivial `F` (`TauCeti.norm_resolvent_heatSemigroup`).

## The argument

For `t > 0` the semigroup is convolution with `K_t`, an `Lᵖ`-valued Bochner integral
`∫ y, K_t(y) • f(· - y) dy` of the translates of `f`. The Laplace transform therefore is the
iterated integral of `(t, y) ↦ e^{-λt} K_t(y) • f(· - y)` over `(0, ∞) × E`, which is integrable
since `‖f(· - y)‖ = ‖f‖` and `∫∫ e^{-λt} K_t(y) dy dt = ∫ e^{-λt} dt = 1 / λ`. Exchanging the
two integrals gives `∫ y, G_λ(y) • f(· - y) dy = G_λ ⋆ f`. The Fourier transform is computed the
same way from the Fourier transform `exp(-4π² t ‖ξ‖²)` of `K_t`.

For the lower bound on the norm, the dilates `φ(r⁻¹ ·)` of a smooth compactly supported `φ ≠ 0`
are approximate solutions of `Δ u = 0`: they lie in the domain of the generator, which acts on
them as the Laplacian (`TauCeti.generator_heatSemigroup`), and their Laplacian has `Lᵖ` norm `r⁻²`
times smaller than their own. Writing `φ(r⁻¹ ·) = (λ - A)⁻¹ (λ φ(r⁻¹ ·) - Δ φ(r⁻¹ ·))` therefore
gives `1 ≤ λ ‖(λ - A)⁻¹‖ + O(r⁻²)`, and `r → ∞` gives `λ ‖(λ - A)⁻¹‖ ≥ 1`; this approximate
eigenvector argument holds for the resolvent of any operator
(`LinearPMap.IsResolventAt.inv_norm_sub_le_norm_of_tendsto`).

## Main declarations

* `TauCeti.heatResolventKernel`: the kernel `G_λ(x) = ∫₀^∞ e^{-λt} K_t(x) dt`.
* `TauCeti.integrable_heatResolventKernel`, `TauCeti.integral_heatResolventKernel`: `G_λ` is
  integrable with `∫ G_λ = 1 / λ`.
* `TauCeti.fourier_heatResolventKernel`: `𝓕 G_λ(ξ) = (λ + 4π² ‖ξ‖²)⁻¹`.
* `TauCeti.resolvent_heatSemigroup`: the Laplace-transform resolvent of the heat semigroup on
  `Lᵖ` is convolution with `G_λ`.
* `TauCeti.isResolventAt_generator_heatSemigroup`, `TauCeti.resolvent_generator_heatSemigroup`:
  convolution with `G_λ` is the resolvent `(λ - A)⁻¹` of the heat generator `A`.
* `TauCeti.resolvent_heatSemigroup_ae_eq_convolution`: the resolvent of the class of `f` is
  represented by the classical convolution `G_λ ⋆ f`.
* `TauCeti.norm_resolvent_heatSemigroup`: on `Lᵖ(E; F)` the resolvent has norm exactly `1 / λ`.

## References

* K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Chapter II,
  Theorem 1.10 (the resolvent as the Laplace transform of the semigroup) and Chapter II, 2.12
  (the diffusion semigroup).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V,
  Section 3.1 (the Bessel kernels as Laplace transforms of the heat kernel).
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Real Semigroups Set
open scoped Convolution ENNReal NNReal FourierTransform

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {lam : ℝ}

/-- The **resolvent kernel of the heat equation**, the Laplace transform of the heat kernel in
time: `G_λ(x) = ∫₀^∞ e^{-λt} K_t(x) dt`. For `λ > 0` it is integrable with mass `1 / λ`
(`TauCeti.integral_heatResolventKernel`), and convolution with it is the resolvent `(λ - A)⁻¹`
of the heat generator `A` (`TauCeti.resolvent_generator_heatSemigroup`). In dimension at least two
the integral diverges at `x = 0`, where the definition takes the junk value `0`; this does not
affect `G_λ` as an integrable function. -/
def heatResolventKernel (lam : ℝ) (x : E) : ℝ :=
  ∫ t in Ioi 0, exp (-(lam * t)) * heatKernel t x

/-- The defining formula of the heat resolvent kernel. -/
theorem heatResolventKernel_apply (lam : ℝ) (x : E) :
    heatResolventKernel lam x = ∫ t in Ioi 0, exp (-(lam * t)) * heatKernel t x :=
  (rfl)

/-- The heat resolvent kernel is nonnegative. -/
theorem heatResolventKernel_nonneg (lam : ℝ) (x : E) : 0 ≤ heatResolventKernel lam x :=
  setIntegral_nonneg measurableSet_Ioi fun _ ht ↦
    mul_nonneg (exp_pos _).le (heatKernel_pos ht x).le

/-- The heat resolvent kernel is even. -/
@[simp]
theorem heatResolventKernel_neg (lam : ℝ) (x : E) :
    heatResolventKernel lam (-x) = heatResolventKernel lam x := by
  simp only [heatResolventKernel_apply, heatKernel_neg]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a fixed time `t > 0` the space integral of `e^{-λt} K_t` is `e^{-λt}`. -/
private theorem integral_exp_mul_heatKernel {t : ℝ} (ht : 0 < t) :
    ∫ x : E, exp (-(lam * t)) * heatKernel t x = exp (-lam * t) := by
  rw [integral_const_mul, integral_heatKernel ht, mul_one, neg_mul]

/-- The space-time integrand `(t, x) ↦ e^{-λt} K_t(x)` of the heat resolvent kernel is integrable
on `(0, ∞) × E` for `λ > 0`: integrating out `x` leaves `e^{-λt}`. -/
theorem integrable_exp_mul_heatKernel (hlam : 0 < lam) :
    Integrable (fun z : ℝ × E ↦ exp (-(lam * z.1)) * heatKernel z.1 z.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hmeas : Measurable fun z : ℝ × E ↦ exp (-(lam * z.1)) * heatKernel z.1 z.2 := by
    simp only [heatKernel_apply]
    fun_prop
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (integrable_heatKernel ht).const_mul _
  · refine (exp_neg_integrableOn_Ioi 0 hlam).congr_fun (fun t ht ↦ ?_) measurableSet_Ioi
    have ht : 0 < t := ht
    simp_rw [norm_mul, norm_of_nonneg (exp_pos _).le, norm_of_nonneg (heatKernel_pos ht _).le,
      integral_exp_mul_heatKernel ht]

/-- The heat resolvent kernel is integrable for `λ > 0`. -/
theorem integrable_heatResolventKernel (hlam : 0 < lam) :
    Integrable (heatResolventKernel lam : E → ℝ) :=
  (integrable_exp_mul_heatKernel hlam).integral_prod_right

/-- **The mass of the heat resolvent kernel**: `∫ G_λ = 1 / λ` for `λ > 0`. -/
@[simp]
theorem integral_heatResolventKernel (hlam : 0 < lam) :
    ∫ x : E, heatResolventKernel lam x = lam⁻¹ := by
  simp_rw [heatResolventKernel_apply]
  rw [← integral_integral_swap (integrable_exp_mul_heatKernel hlam)]
  rw [setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ integral_exp_mul_heatKernel ht,
    integral_Ioi_exp_neg_mul hlam]

/-- **The Fourier transform of the heat resolvent kernel.** In Mathlib's normalization
`𝓕 f(ξ) = ∫ e^{-2πi⟪x, ξ⟫} f(x) dx`, `𝓕 G_λ(ξ) = (λ + 4π² ‖ξ‖²)⁻¹` for `λ > 0`: the reciprocal of
the symbol of `λ - Δ`. -/
theorem fourier_heatResolventKernel (hlam : 0 < lam) (ξ : E) :
    𝓕 (fun x : E ↦ (heatResolventKernel lam x : ℂ)) ξ =
      (((lam + 4 * π ^ 2 * ‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  -- The integrand of the Fourier transform, as a function of `(t, x)`, is dominated by the
  -- integrand of `G_λ`.
  have hint : Integrable (Function.uncurry fun (t : ℝ) (x : E) ↦
      (𝐞 (-inner ℝ x ξ) : ℂ) * ((exp (-(lam * t)) * heatKernel t x : ℝ) : ℂ))
      ((volume.restrict (Ioi 0)).prod volume) :=
    ((integrable_exp_mul_heatKernel hlam).ofReal (𝕜 := ℂ)).bdd_mul
      (by fun_prop : Continuous fun z : ℝ × E ↦ (𝐞 (-inner ℝ z.2 ξ) : ℂ)).aestronglyMeasurable
      (ae_of_all _ fun z ↦ (Circle.norm_coe _).le)
  -- At a fixed time the inner integral is `e^{-λt}` times the Fourier transform of `K_t`.
  have h : ∀ t ∈ Ioi (0 : ℝ), ∫ x : E, (𝐞 (-inner ℝ x ξ) : ℂ) *
      ((exp (-(lam * t)) * heatKernel t x : ℝ) : ℂ) =
      ((exp (-(lam + 4 * π ^ 2 * ‖ξ‖ ^ 2) * t) : ℝ) : ℂ) := fun t ht ↦ by
    have hK := fourier_heatKernel ht ξ
    simp_rw [fourier_eq, Circle.smul_def, smul_eq_mul] at hK
    simp_rw [Complex.ofReal_mul, mul_left_comm _ ((exp (-(lam * t)) : ℝ) : ℂ), integral_const_mul,
      hK, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have hsum : 0 < lam + 4 * π ^ 2 * ‖ξ‖ ^ 2 := by positivity
  simp_rw [fourier_eq, Circle.smul_def, smul_eq_mul, heatResolventKernel_apply,
    ← integral_complex_ofReal, ← integral_const_mul]
  rw [← integral_integral_swap hint, setIntegral_congr_fun measurableSet_Ioi h,
    integral_complex_ofReal, integral_Ioi_exp_neg_mul hsum]

variable [CompleteSpace F]

/-- **The resolvent of the heat semigroup is convolution with the resolvent kernel.** For
`1 ≤ p < ∞` and `λ > 0`, the Laplace transform `∫₀^∞ e^{-λt} e^{tΔ} f dt` of the heat semigroup
on `Lᵖ` is convolution with `G_λ`. -/
theorem resolvent_heatSemigroup (hp : p ≠ ∞) (hlam : 0 < lam) :
    (heatSemigroup (E := E) (F := F) hp).resolvent lam hlam =
      convolutionLp hp (heatResolventKernel lam) volume := by
  ext1 f
  -- The translates `y ↦ f(· - y)` form a bounded continuous `Lᵖ`-valued function.
  have hτ : MemLp (fun z : ℝ × E ↦ volume.translateLp p (-z.2) f) ∞
      ((volume.restrict (Ioi 0)).prod volume) :=
    memLp_top_of_bound
      (((Measure.continuous_translateLp hp f).comp continuous_neg).comp
        continuous_snd).aestronglyMeasurable ‖f‖
      (ae_of_all _ fun _ ↦ (LinearIsometryEquiv.norm_map _ f).le)
  have hint : Integrable (Function.uncurry fun (t : ℝ) (y : E) ↦
      (exp (-(lam * t)) * heatKernel t y) • volume.translateLp p (-y) f)
      ((volume.restrict (Ioi 0)).prod volume) :=
    (integrable_exp_mul_heatKernel hlam).smul_of_top_left hτ
  -- At a positive time the semigroup is the `Lᵖ`-valued convolution integral with `K_t`.
  have h : ∀ t ∈ Ioi (0 : ℝ), exp (-(lam * t)) • (heatSemigroup hp).realOperator t f =
      ∫ y, (exp (-(lam * t)) * heatKernel t y) • volume.translateLp p (-y) f := fun t ht ↦ by
    have ht' : t.toNNReal ≠ 0 := (toNNReal_pos.2 ht).ne'
    rw [StronglyContinuousSemigroup.realOperator_def,
      ContractionSemigroup.toStronglyContinuousSemigroup_apply, heatSemigroup_apply_apply hp ht',
      coe_toNNReal _ (le_of_lt ht), ← integral_smul]
    simp_rw [smul_smul]
  -- Exchange the time and space integrals.
  rw [ContractionSemigroup.resolvent_apply, setIntegral_congr_fun measurableSet_Ioi h,
    integral_integral_swap hint, convolutionLp_apply hp (integrable_heatResolventKernel hlam)]
  simp_rw [integral_smul_const, heatResolventKernel_apply]

/-- **Convolution with `G_λ` is the resolvent of the heat generator.** For `1 ≤ p < ∞` and
`λ > 0`, convolution with the heat resolvent kernel maps `Lᵖ` into the domain of the generator
`A` of the heat semigroup and inverts `λ - A` on both sides. -/
theorem isResolventAt_generator_heatSemigroup (hp : p ≠ ∞) (hlam : 0 < lam) :
    LinearPMap.IsResolventAt (heatSemigroup (E := E) (F := F) hp).generator lam
      (convolutionLp hp (heatResolventKernel lam) volume) := by
  rw [← resolvent_heatSemigroup hp hlam,
    ContractionSemigroup.resolvent_eq_stronglyContinuousSemigroup_resolvent]
  exact StronglyContinuousSemigroup.isResolventAt_generator _ _ (by simpa using hlam)

/-- **The resolvent `(λ - A)⁻¹` on `Lᵖ` is convolution with `G_λ`**: for `1 ≤ p < ∞` and `λ > 0`,
the resolvent of the generator `A` of the heat semigroup is convolution with the heat resolvent
kernel. -/
theorem resolvent_generator_heatSemigroup (hp : p ≠ ∞) (hlam : 0 < lam) :
    LinearPMap.resolvent (heatSemigroup (E := E) (F := F) hp).generator lam =
      convolutionLp hp (heatResolventKernel lam) volume :=
  LinearPMap.resolvent_eq_of_isResolventAt (isResolventAt_generator_heatSemigroup hp hlam)

/-- The resolvent of the heat semigroup applied to the class of `f ∈ Lᵖ` is represented almost
everywhere by the classical convolution `(G_λ ⋆ f)(x) = ∫ y, G_λ(y) • f(x - y) dy`. -/
theorem resolvent_heatSemigroup_ae_eq_convolution (hp : p ≠ ∞) (hlam : 0 < lam) {f : E → F}
    (hf : MemLp f p volume) :
    (heatSemigroup hp).resolvent lam hlam (hf.toLp f) =ᵐ[volume] heatResolventKernel lam ⋆ f := by
  rw [resolvent_heatSemigroup hp hlam]
  exact convolutionLp_ae_eq_convolution hp (integrable_heatResolventKernel hlam) hf

/-- **The resolvent of the heat semigroup preserves positivity.** -/
theorem resolvent_heatSemigroup_nonneg (hp : p ≠ ∞) (hlam : 0 < lam)
    {f : Lp ℝ p (volume : Measure E)} (hf : 0 ≤ f) :
    0 ≤ (heatSemigroup hp).resolvent lam hlam f := by
  rw [resolvent_heatSemigroup hp hlam]
  exact convolutionLp_nonneg hp (ae_of_all _ (heatResolventKernel_nonneg lam)) hf

/-- On `L¹` the resolvent of the heat semigroup scales the integral by `1 / λ`:
`∫ (λ - A)⁻¹ f = λ⁻¹ • ∫ f`, where `A` is the heat generator. -/
@[simp]
theorem integral_resolvent_heatSemigroup (hlam : 0 < lam) (f : Lp F 1 (volume : Measure E)) :
    ∫ x, (heatSemigroup ENNReal.one_ne_top).resolvent lam hlam f x = lam⁻¹ • ∫ x, f x := by
  rw [resolvent_heatSemigroup ENNReal.one_ne_top hlam, integral_convolutionLp,
    integral_heatResolventKernel hlam]

/-- On nonnegative functions in `L¹` the resolvent of the heat semigroup scales the norm by
`1 / λ`: for `0 ≤ f ∈ L¹`, `‖(λ - A)⁻¹ f‖₁ = λ⁻¹ ‖f‖₁`, where `A` is the heat generator. -/
theorem norm_resolvent_heatSemigroup_of_nonneg (hlam : 0 < lam)
    {f : Lp ℝ 1 (volume : Measure E)} (hf : 0 ≤ f) :
    ‖(heatSemigroup ENNReal.one_ne_top).resolvent lam hlam f‖ = lam⁻¹ * ‖f‖ := by
  rw [L1.norm_eq_integral_of_nonneg
      (resolvent_heatSemigroup_nonneg ENNReal.one_ne_top hlam hf),
    L1.norm_eq_integral_of_nonneg hf, integral_resolvent_heatSemigroup, smul_eq_mul]

open InnerProductSpace Laplacian Topology in
/-- **The norm of the heat resolvent.** For `1 ≤ p < ∞`, `λ > 0` and a nontrivial Banach space
`F`, the resolvent `(λ - A)⁻¹` of the heat generator `A` on `Lᵖ(E; F)` has operator norm exactly
`1 / λ`: the Hille–Yosida bound of a contraction semigroup is attained. -/
@[simp]
theorem norm_resolvent_heatSemigroup [Nontrivial F] (hp : p ≠ ∞) (hlam : 0 < lam) :
    ‖(heatSemigroup (E := E) (F := F) hp).resolvent lam hlam‖ = lam⁻¹ := by
  set S := heatSemigroup (E := E) (F := F) hp
  refine le_antisymm ((S.resolvent_norm_le lam hlam).trans_eq (one_div _)) ?_
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
  -- The dilates `φ(r⁻¹ ·)`, `r = n + 1`, lie in the generator domain, where the generator acts
  -- as the Laplacian.
  have hr (n : ℕ) : (0 : ℝ) < n + 1 := n.cast_add_one_pos
  have hφr (n : ℕ) : ContDiff ℝ 2 fun x ↦ φ (((n : ℝ) + 1)⁻¹ • x) :=
    hφ.comp (contDiff_const_smul _)
  have hφrc (n : ℕ) : HasCompactSupport fun x ↦ φ (((n : ℝ) + 1)⁻¹ • x) :=
    hφc.comp_smul (inv_ne_zero (hr n).ne')
  have hf (n : ℕ) :=
    (hφr n).continuous.memLp_of_hasCompactSupport (μ := volume) (p := p) (hφrc n)
  have hg (n : ℕ) := (hφr n).continuous_laplacian.memLp_of_hasCompactSupport (μ := volume)
    (p := p) (hφrc n).laplacian
  let f (n : ℕ) : S.generator.domain := ⟨(hf n).toLp _, by
    rw [StronglyContinuousSemigroup.generator_domain]
    exact mem_domain_heatSemigroup hp (hφr n) (hφrc n) (hf n).coeFn_toLp⟩
  -- They are nonzero approximate solutions of `Δ u = 0`: the `Lᵖ` norms of the dilate and of its
  -- Laplacian scale like `r^{n/p}` and `r^{n/p - 2}`.
  have hf_ratio (n : ℕ) : ‖(f n : Lp F p (volume : Measure E))‖ ≠ 0 ∧
      ‖S.generator (f n) - (0 : ℝ) • (f n : Lp F p (volume : Measure E))‖ /
        ‖(f n : Lp F p (volume : Measure E))‖ = (((n : ℝ) + 1) ^ 2)⁻¹ * (c / a) := by
    set s := ((n : ℝ) + 1) ^ ((Module.finrank ℝ E : ℝ) / p.toReal)
    have hs : 0 < s := by positivity
    have hnf : ‖(f n : Lp F p (volume : Measure E))‖ = s * a := by
      rw [Lp.norm_toLp, Measure.eLpNorm_comp_inv_smul volume φ (hr n).ne', abs_of_pos (hr n)]
      simp [ENNReal.toReal_ofReal hs.le, s, a]
    have hng : ‖(hg n).toLp (Δ fun x ↦ φ (((n : ℝ) + 1)⁻¹ • x))‖ =
        (((n : ℝ) + 1) ^ 2)⁻¹ * (s * c) := by
      have hΔ : (Δ fun x ↦ φ (((n : ℝ) + 1)⁻¹ • x)) =
          (((n : ℝ) + 1)⁻¹) ^ 2 • fun x ↦ Δ φ (((n : ℝ) + 1)⁻¹ • x) :=
        laplacian_comp_smul_right _ φ
      rw [Lp.norm_toLp, hΔ, eLpNorm_const_smul, Measure.eLpNorm_comp_inv_smul volume _ (hr n).ne',
        abs_of_pos (hr n)]
      simp [ENNReal.toReal_ofReal hs.le, abs_of_pos (hr n), s, c]
    refine ⟨hnf ▸ (mul_pos hs ha).ne', ?_⟩
    rw [zero_smul, sub_zero,
      generator_heatSemigroup hp (hφr n) (hφrc n) (hf n).coeFn_toLp (hg n).coeFn_toLp, hng, hnf]
    field_simp
  -- Let `r → ∞`.
  have h := (S.isResolventAt_generator S.hasGrowthBound (lambda := lam)
    (by simpa using hlam)).inv_norm_sub_le_norm_of_tendsto (mu := 0) (l := atTop) f
    (Eventually.of_forall fun n ↦ (hf_ratio n).1) ?_
  · rwa [sub_zero, Real.norm_eq_abs, abs_of_pos hlam,
      ← ContractionSemigroup.resolvent_eq_stronglyContinuousSemigroup_resolvent] at h
  · refine (tendsto_congr fun n ↦ (hf_ratio n).2).2 ?_
    simpa [one_div, inv_pow] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).mul_const (c / a)

end TauCeti

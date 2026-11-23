/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.Propagator
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.Deriv.OperatorFamily
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Strong solutions of the wave equation on `L²`: energy and Duhamel's formula

On a finite-dimensional real inner product space `E`, a **strong solution** of the wave equation

`∂ₜ²u - Δu = G` on a set `s ⊆ ℝ` of times

is a curve `u : ℝ → L²(E, F)` that is twice differentiable within `s`, with velocity `u'` and
acceleration `u''`, whose distributional Laplacian at every time of `s` is the `L²` function
`u'' - G` (`TauCeti.IsWaveSolutionOn`). For data `f, g` whose Laplacians lie in `L²`, the formula
`u(t) = cos(tD) f + D⁻¹ sin(tD) g` is a strong solution of the free equation on all of `ℝ`
(`TauCeti.isWaveSolutionOn_waveCosPropagator_add_waveSinPropagator`). Conversely:

* **Energy conservation** (`TauCeti.IsWaveSolutionOn.norm_sq_sub_re_inner_eq`). A strong solution
  of the free equation on an interval of times keeps its energy
  `‖∂ₜu(t)‖² + ‖D u(t)‖² = ‖u'(t)‖² - re ⟪u(t), u''(t)⟫`; here `D = √(-Δ)`, and
  `‖D u‖² = -re ⟪u, Δ u⟫ = ∫ 4π² ‖ξ‖² ‖𝓕 u(ξ)‖² dξ` is nonnegative
  (`MeasureTheory.Lp.re_inner_nonpos_of_laplacian_toTemperedDistribution_eq`).
* **Energy uniqueness** (`TauCeti.IsWaveSolutionOn.eq_zero`). A strong solution of the free
  equation on an interval of times with zero data at one time `t₀` of it vanishes on the interval.
* **Duhamel's formula**
  (`TauCeti.IsWaveSolutionOn.eq_waveCosPropagator_add_waveSinPropagator_add_integral`). A strong
  solution on an interval of times containing `t₀` and `t`, with forcing `G` integrable between
  them, is

  `u(t) = cos((t - t₀)D) u(t₀) + D⁻¹ sin((t - t₀)D) u'(t₀) + ∫_{t₀}^t D⁻¹ sin((t - s)D) G(s) ds`.

  Both directions of time are covered: `t` may lie before `t₀`. For the free equation and
  `t₀ = 0`, the mixed norms `L^q(s; L^r_x)` of a solution are therefore at most those of
  `cos(tD) u(0) + D⁻¹ sin(tD) u'(0)` over all times
  (`TauCeti.IsWaveSolutionOn.eLpNorm_eLpNorm_restrict_le`).

## The arguments

The energy is not differentiable as it stands, since `D u(t)` need not be differentiable in `L²`.
It is truncated in frequency: with `χ_R` the indicator of the ball of radius `R` on the Fourier
side, the truncated energy `‖χ_R(D) D u(t)‖² + ‖χ_R(D) u'(t)‖²` is differentiable, and its
derivative `2 re ⟪χ_R D u, χ_R D u'⟫ + 2 re ⟪χ_R u', χ_R u''⟫` vanishes because
`𝓕 u'' = -4π² ‖ξ‖² 𝓕 u`. Letting `R → ∞` gives the energy identity.

For Duhamel's formula, fix `t` and differentiate
`w(s) = cos((t - s)D) u(s) + D⁻¹ sin((t - s)D) u'(s)`. The propagators are only strongly
differentiable, so the product rule is `HasDerivWithinAt.clm_apply_of_tendsto`; the terms carrying
`u'` cancel, and those carrying `u''` cancel against `Δ u = u'' - G` up to
`D⁻¹ sin((t - s)D) G(s)`. Integrating from `t₀` to `t` gives the formula, since `w(t) = u(t)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 2.4.3 (energy methods) and
  Section 7.2 (hyperbolic equations).
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3 (Duhamel's formula).
-/

public section

noncomputable section

open scoped FourierTransform Laplacian SchwartzMap Topology ENNReal ComplexInnerProductSpace
open MeasureTheory Filter Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- `u` is a **strong solution** of the wave equation `∂ₜ²u - Δu = G` on the set of times `s`, with
velocity `u'` and acceleration `u''`: within `s`, `u` has derivative `u'` and `u'` has derivative
`u''` in `L²`, and at every time of `s` the distributional Laplacian of `u` is the `L²` function
`u'' - G`. -/
structure IsWaveSolutionOn (u u' u'' G : ℝ → Lp F 2 (volume : Measure E)) (s : Set ℝ) : Prop where
  hasDerivWithinAt : ∀ t ∈ s, HasDerivWithinAt u (u' t) s t
  hasDerivWithinAt_deriv : ∀ t ∈ s, HasDerivWithinAt u' (u'' t) s t
  laplacian_eq : ∀ t ∈ s, Δ (u t : 𝓢'(E, F)) = ((u'' t - G t : Lp F 2 (volume : Measure E)) :
    𝓢'(E, F))

variable {u u' u'' G : ℝ → Lp F 2 (volume : Measure E)} {s : Set ℝ}

/-- A strong solution on `s` is one on every subset of `s`. -/
theorem IsWaveSolutionOn.mono (hu : IsWaveSolutionOn u u' u'' G s) {s' : Set ℝ} (hs : s' ⊆ s) :
    IsWaveSolutionOn u u' u'' G s' where
  hasDerivWithinAt t ht := (hu.hasDerivWithinAt t (hs ht)).mono hs
  hasDerivWithinAt_deriv t ht := (hu.hasDerivWithinAt_deriv t (hs ht)).mono hs
  laplacian_eq t ht := hu.laplacian_eq t (hs ht)

/-- For a strong solution of the free equation, the Laplacian is the acceleration. -/
theorem IsWaveSolutionOn.laplacian_eq_of_zero (hu : IsWaveSolutionOn u u' u'' 0 s) {t : ℝ}
    (ht : t ∈ s) : Δ (u t : 𝓢'(E, F)) = (u'' t : 𝓢'(E, F)) := by
  simpa only [Pi.zero_apply, sub_zero] using hu.laplacian_eq t ht

/-- **Existence of strong solutions.** If the Laplacians of `f` and `g` are the `L²` functions
`h₁` and `h₂`, then `u(t) = cos(tD) f + D⁻¹ sin(tD) g` is a strong solution of the free wave
equation on every set of times, with velocity `D⁻¹ sin(tD) h₁ + cos(tD) g` and acceleration
`cos(tD) h₁ + D⁻¹ sin(tD) h₂`. It has `u(0) = f` and `u'(0) = g`. -/
theorem isWaveSolutionOn_waveCosPropagator_add_waveSinPropagator
    {f g h₁ h₂ : Lp F 2 (volume : Measure E)} (hf : Δ (f : 𝓢'(E, F)) = (h₁ : 𝓢'(E, F)))
    (hg : Δ (g : 𝓢'(E, F)) = (h₂ : 𝓢'(E, F))) (s : Set ℝ) :
    IsWaveSolutionOn (fun t ↦ waveCosPropagator F t f + waveSinPropagator F t g)
      (fun t ↦ waveSinPropagator F t h₁ + waveCosPropagator F t g)
      (fun t ↦ waveCosPropagator F t h₁ + waveSinPropagator F t h₂) 0 s where
  hasDerivWithinAt t _ :=
    ((hasDerivAt_waveCosPropagator_apply hf t).add
      (hasDerivAt_waveSinPropagator_apply g t)).hasDerivWithinAt
  hasDerivWithinAt_deriv t _ :=
    ((hasDerivAt_waveSinPropagator_apply h₁ t).add
      (hasDerivAt_waveCosPropagator_apply hg t)).hasDerivWithinAt
  laplacian_eq t _ := by
    simp only [Pi.zero_apply, sub_zero, Lp.toTemperedDistribution_add,
      ← TemperedDistribution.laplacianCLM_apply, map_add]
    simp only [TemperedDistribution.laplacianCLM_apply, laplacian_waveCosPropagator_apply hf,
      laplacian_waveSinPropagator_apply hg]

/-! ### The energy identity -/

section Energy

/-- The indicator of the closed ball of radius `R`, the frequency cutoff of the truncated
energies. -/
private def cutoff (R : ℝ) (ξ : E) : ℂ :=
  (Metric.closedBall (0 : E) R).indicator (fun _ ↦ 1) ξ

/-- The truncated symbol `χ_R(ξ) 2π ‖ξ‖` of `χ_R(D) D`. -/
private def cutoffSqrt (R : ℝ) (ξ : E) : ℂ :=
  (Metric.closedBall (0 : E) R).indicator (fun η ↦ (sqrtNegLaplacianSymbol η : ℂ)) ξ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_cutoff_le (R : ℝ) (ξ : E) : ‖cutoff R ξ‖ ≤ 1 :=
  (norm_indicator_le_norm_self _ _).trans norm_one.le

private theorem memLp_cutoff (R : ℝ) : MemLp (cutoff (E := E) R) ∞ volume :=
  memLp_top_of_bound (Measurable.aestronglyMeasurable
    (measurable_const.indicator Metric.isClosed_closedBall.measurableSet)) 1
    (Eventually.of_forall (norm_cutoff_le R))

private theorem memLp_cutoffSqrt (R : ℝ) : MemLp (cutoffSqrt (E := E) R) ∞ volume := by
  refine memLp_top_of_bound (Measurable.aestronglyMeasurable ((Complex.continuous_ofReal.comp
    sqrtNegLaplacianSymbol.continuous).measurable.indicator
      Metric.isClosed_closedBall.measurableSet)) (2 * Real.pi * |R|)
    (Eventually.of_forall fun ξ ↦ ?_)
  by_cases h : ξ ∈ Metric.closedBall (0 : E) R
  · have := (mem_closedBall_zero_iff.1 h).trans (le_abs_self R)
    simp only [cutoffSqrt, h, Set.indicator_of_mem, Complex.norm_real, Real.norm_eq_abs,
      sqrtNegLaplacianSymbol_apply, abs_mul, abs_two, abs_of_pos Real.pi_pos, abs_norm]
    gcongr
  · rw [cutoffSqrt, Set.indicator_of_notMem h, norm_zero]
    positivity

variable (F) in
/-- The frequency truncation `χ_R(D)`. -/
private def truncate (R : ℝ) : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM F ((memLp_cutoff R).toLp _)

variable (F) in
/-- The truncated square root `χ_R(D) D` of `-Δ`. -/
private def truncateSqrt (R : ℝ) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM F ((memLp_cutoffSqrt R).toLp _)

/-- The pairing behind the energy identity: if `Δ x = y`, then
`⟪χ_R z, χ_R y⟫ = -⟪χ_R D z, χ_R D x⟫`. -/
private theorem inner_truncate_eq {x y : Lp F 2 (volume : Measure E)}
    (hxy : Δ (x : 𝓢'(E, F)) = (y : 𝓢'(E, F))) (R : ℝ) (z : Lp F 2 (volume : Measure E)) :
    ⟪truncate F R z, truncate F R y⟫ = -⟪truncateSqrt F R z, truncateSqrt F R x⟫ := by
  rw [← Lp.inner_fourier_eq, ← Lp.inner_fourier_eq (truncateSqrt F R z), L2.inner_def,
    L2.inner_def, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [(Lp.laplacian_toTemperedDistribution_eq_iff x y).1 hxy,
    Lp.coeFn_fourier_fourierMultiplierCLM_toLp z (memLp_cutoff R),
    Lp.coeFn_fourier_fourierMultiplierCLM_toLp y (memLp_cutoff R),
    Lp.coeFn_fourier_fourierMultiplierCLM_toLp z (memLp_cutoffSqrt R),
    Lp.coeFn_fourier_fourierMultiplierCLM_toLp x (memLp_cutoffSqrt R)] with ξ h₁ h₂ h₃ h₄ h₅
  simp only [truncate, truncateSqrt]
  rw [h₂, h₃, h₄, h₅, h₁]
  by_cases h : ξ ∈ Metric.closedBall (0 : E) R
  · simp only [cutoff, cutoffSqrt, h, indicator_of_mem, one_smul, laplacianSymbol_apply,
      sqrtNegLaplacianSymbol_apply, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_pow, neg_smul, smul_neg, inner_neg_right, inner_smul_left, inner_smul_right,
      map_mul, map_ofNat, Complex.conj_ofReal, neg_inj]
    ring
  · simp [cutoff, cutoffSqrt, Set.indicator_of_notMem h]

/-- The truncations `χ_R(D)` converge strongly to the identity as `R → ∞`. -/
private theorem tendsto_truncate (x : Lp F 2 (volume : Measure E)) :
    Tendsto (fun R : ℕ ↦ truncate F (R : ℝ) x) atTop (𝓝 x) := by
  have h1 : MemLp (fun _ : E ↦ (1 : ℂ)) ∞ volume := memLp_top_const 1
  have hid : Lp.fourierMultiplierCLM F (h1.toLp _) x = x := by
    rw [Lp.fourierMultiplierCLM_of_ae_eq_const (c := 1) h1.coeFn_toLp, one_smul,
      ContinuousLinearMap.id_apply]
  conv_rhs => rw [← hid]
  refine Lp.tendsto_fourierMultiplierCLM_apply (C := 1) (Eventually.of_forall fun R ↦ ?_) ?_ x
  · refine Lp.norm_top_le_of_ae_bound zero_le_one ?_
    filter_upwards [(memLp_cutoff (E := E) R).coeFn_toLp] with ξ h
    rw [h]
    exact norm_cutoff_le _ ξ
  · filter_upwards [ae_all_iff.2 fun R : ℕ ↦ (memLp_cutoff (E := E) R).coeFn_toLp,
      h1.coeFn_toLp] with ξ hR h
    simp only [hR, h]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈‖ξ‖⌉₊] with R hR
    rw [cutoff, Set.indicator_of_mem (mem_closedBall_zero_iff.2 ((Nat.le_ceil _).trans
      (Nat.cast_le.2 hR)))]

/-- The truncated energy `‖χ_R(D) D u‖² + ‖χ_R(D) u'‖²` of a strong solution of the free equation
is constant on an order-connected set of times. -/
private theorem truncatedEnergy_eq [s.OrdConnected] (hu : IsWaveSolutionOn u u' u'' 0 s)
    (R : ℝ) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    (⟪truncateSqrt F R (u t), truncateSqrt F R (u t)⟫).re +
        (⟪truncate F R (u' t), truncate F R (u' t)⟫).re =
      (⟪truncateSqrt F R (u t₀), truncateSqrt F R (u t₀)⟫).re +
        (⟪truncate F R (u' t₀), truncate F R (u' t₀)⟫).re := by
  have hderiv : ∀ τ ∈ s, HasDerivWithinAt
      (fun τ ↦ (⟪truncateSqrt F R (u τ), truncateSqrt F R (u τ)⟫).re +
        (⟪truncate F R (u' τ), truncate F R (u' τ)⟫).re)
      (2 * (⟪truncateSqrt F R (u τ), truncateSqrt F R (u' τ)⟫).re +
        2 * (⟪truncate F R (u' τ), truncate F R (u'' τ)⟫).re) s τ := fun τ hτ ↦ by
    -- The derivative of `σ ↦ re ⟪v σ, v σ⟫ = ‖v σ‖²` along a curve `v`, from Mathlib's
    -- `HasDerivWithinAt.norm_sq` for the underlying real inner product `re ⟪·, ·⟫`.
    have hre : ∀ {v : ℝ → Lp F 2 (volume : Measure E)} {v' : Lp F 2 (volume : Measure E)},
        HasDerivWithinAt v v' s τ →
          HasDerivWithinAt (fun σ ↦ (⟪v σ, v σ⟫).re) (2 * (⟪v τ, v'⟫).re) s τ :=
      fun {v v'} hv ↦ by
        let := InnerProductSpace.complexToReal (G := Lp F 2 (volume : Measure E))
        simpa only [← RCLike.re_to_complex, inner_self_eq_norm_sq, real_inner_eq_re_inner ℂ]
          using hv.norm_sq
    exact (hre (((truncateSqrt F R).restrictScalars ℝ).hasFDerivAt
      |>.comp_hasDerivWithinAt τ (hu.hasDerivWithinAt τ hτ))).add
      (hre (((truncate F R).restrictScalars ℝ).hasFDerivAt
      |>.comp_hasDerivWithinAt τ (hu.hasDerivWithinAt_deriv τ hτ)))
  refine (Set.OrdConnected.isPreconnected ‹_›).eq_of_hasDerivWithinAt_zero
    (fun τ hτ ↦ (hderiv τ hτ).congr_deriv ?_) ht ht₀
  rw [inner_truncate_eq (hu.laplacian_eq_of_zero hτ), Complex.neg_re,
    ← inner_conj_symm (truncateSqrt F R (u' τ)), Complex.conj_re]
  ring

/-- The energy `‖χ_R(D) D x‖²` of a truncation is `-re ⟪χ_R x, χ_R Δx⟫`. -/
private theorem re_inner_truncateSqrt_self {x y : Lp F 2 (volume : Measure E)}
    (hxy : Δ (x : 𝓢'(E, F)) = (y : 𝓢'(E, F))) (R : ℝ) :
    (⟪truncateSqrt F R x, truncateSqrt F R x⟫).re = -(⟪truncate F R x, truncate F R y⟫).re := by
  rw [inner_truncate_eq hxy, Complex.neg_re, neg_neg]

/-- **Conservation of energy.** For a strong solution of the free wave equation `∂ₜ²u = Δu` on an
order-connected set of times `s`, the energy
`‖∂ₜu(t)‖² + ‖D u(t)‖² = ‖u'(t)‖² - re ⟪u(t), u''(t)⟫`, `D = √(-Δ)`, is constant on `s`. Here
`-re ⟪u, u''⟫ = -re ⟪u, Δ u⟫` is the nonnegative quantity `∫ 4π² ‖ξ‖² ‖𝓕 u(ξ)‖² dξ`. -/
theorem IsWaveSolutionOn.norm_sq_sub_re_inner_eq [s.OrdConnected]
    (hu : IsWaveSolutionOn u u' u'' 0 s) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s) :
    ‖u' t‖ ^ 2 - (⟪u t, u'' t⟫).re = ‖u' t₀‖ ^ 2 - (⟪u t₀, u'' t₀⟫).re := by
  -- The truncated energies converge to the energy as the cutoff is removed.
  have hlim : ∀ τ ∈ s, Tendsto (fun R : ℕ ↦
      (⟪truncateSqrt F (R : ℝ) (u τ), truncateSqrt F (R : ℝ) (u τ)⟫).re +
        (⟪truncate F (R : ℝ) (u' τ), truncate F (R : ℝ) (u' τ)⟫).re) atTop
        (𝓝 (‖u' τ‖ ^ 2 - (⟪u τ, u'' τ⟫).re)) := fun τ hτ ↦ by
    simp only [re_inner_truncateSqrt_self (hu.laplacian_eq_of_zero hτ)]
    rw [sub_eq_neg_add, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    exact (((Complex.continuous_re.tendsto _).comp ((tendsto_truncate (u τ)).inner
      (tendsto_truncate (u'' τ)))).neg).add ((Complex.continuous_re.tendsto _).comp
        ((tendsto_truncate (u' τ)).inner (tendsto_truncate (u' τ))))
  refine tendsto_nhds_unique (hlim t ht) ?_
  simpa only [truncatedEnergy_eq hu _ ht₀ ht] using hlim t₀ ht₀

/-- **Energy uniqueness.** A strong solution of the free wave equation `∂ₜ²u = Δu` on an
order-connected set of times `s`, with `u(t₀) = 0` and `∂ₜu(t₀) = 0` at some `t₀ ∈ s`, vanishes on
`s`. -/
theorem IsWaveSolutionOn.eq_zero [s.OrdConnected] (hu : IsWaveSolutionOn u u' u'' 0 s) {t₀ : ℝ}
    (ht₀ : t₀ ∈ s) (h₀ : u t₀ = 0) (h₁ : u' t₀ = 0) {t : ℝ} (ht : t ∈ s) : u t = 0 := by
  have hu' : ∀ τ ∈ s, u' τ = 0 := fun τ hτ ↦ by
    have hE := hu.norm_sq_sub_re_inner_eq ht₀ hτ
    have hneg := Lp.re_inner_nonpos_of_laplacian_toTemperedDistribution_eq
      (hu.laplacian_eq_of_zero hτ)
    rw [h₀, h₁, norm_zero, inner_zero_left, Complex.zero_re] at hE
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg (u' τ)])
  rw [← h₀]
  exact (Set.OrdConnected.isPreconnected ‹_›).eq_of_hasDerivWithinAt_zero
    (fun τ hτ ↦ hu' τ hτ ▸ hu.hasDerivWithinAt τ hτ) ht ht₀

end Energy

/-! ### Duhamel's formula -/

/-- The derivative of `s ↦ cos((t - s)D) u(s) + D⁻¹ sin((t - s)D) u'(s)` along a strong solution is
`D⁻¹ sin((t - s)D) G(s)`. -/
private theorem hasDerivWithinAt_duhamel (hu : IsWaveSolutionOn u u' u'' G s) (t : ℝ) {τ : ℝ}
    (hτ : τ ∈ s) :
    HasDerivWithinAt (fun σ ↦ waveCosPropagator F (t - σ) (u σ) +
        waveSinPropagator F (t - σ) (u' σ)) (waveSinPropagator F (t - τ) (G τ)) s τ := by
  have hΔ := hu.laplacian_eq τ hτ
  have hsub : HasDerivAt (fun σ : ℝ ↦ t - σ) (-1) τ := by
    simpa using (hasDerivAt_id τ).const_sub t
  -- `σ ↦ cos((t - σ)D) u(σ)`.
  have hC := HasDerivWithinAt.clm_apply_of_tendsto (T := fun σ ↦
      (waveCosPropagator F (t - σ)).restrictScalars ℝ) (M := 1)
    (((hasDerivAt_waveCosPropagator_apply hΔ (t - τ)).scomp τ hsub).hasDerivWithinAt)
    (hu.hasDerivWithinAt τ hτ)
    (((continuous_waveCosPropagator_apply (u' τ)).comp
      (continuous_const.sub continuous_id)).continuousWithinAt.tendsto)
    (Eventually.of_forall fun σ ↦ by
      rw [ContinuousLinearMap.norm_restrictScalars]; exact norm_waveCosPropagator_le _)
  -- `σ ↦ D⁻¹ sin((t - σ)D) u'(σ)`.
  have hS := HasDerivWithinAt.clm_apply_of_tendsto (T := fun σ ↦
      (waveSinPropagator F (t - σ)).restrictScalars ℝ) (M := |t - τ| + 1)
    (((hasDerivAt_waveSinPropagator_apply (u' τ) (t - τ)).scomp τ hsub).hasDerivWithinAt)
    (hu.hasDerivWithinAt_deriv τ hτ)
    (((continuous_waveSinPropagator_apply (u'' τ)).comp
      (continuous_const.sub continuous_id)).continuousWithinAt.tendsto)
    (by
      filter_upwards [nhdsWithin_le_nhds ((continuous_const.sub continuous_id).abs.continuousAt
        |>.eventually_lt continuousAt_const (lt_add_one |t - τ|))] with σ hσ
      rw [ContinuousLinearMap.norm_restrictScalars]
      exact (norm_waveSinPropagator_le _).trans hσ.le)
  have h := hC.add hS
  simp only [ContinuousLinearMap.coe_restrictScalars'] at h
  convert h using 1
  rw [neg_one_smul, neg_one_smul, map_sub]
  abel

/-- **Duhamel's formula.** A strong solution of the wave equation `∂ₜ²u - Δu = G` on an
order-connected set of times `s` containing `t₀` and `t`, with `G` integrable between `t₀` and
`t`, is

`u(t) = cos((t - t₀)D) u(t₀) + D⁻¹ sin((t - t₀)D) u'(t₀) + ∫_{t₀}^t D⁻¹ sin((t - s)D) G(s) ds`.

This holds forwards and backwards in time. In particular a solution is determined by its data
`u(t₀)`, `u'(t₀)` and `G`. -/
theorem IsWaveSolutionOn.eq_waveCosPropagator_add_waveSinPropagator_add_integral [s.OrdConnected]
    (hu : IsWaveSolutionOn u u' u'' G s) {t₀ t : ℝ} (ht₀ : t₀ ∈ s) (ht : t ∈ s)
    (hG : IntervalIntegrable G volume t₀ t) :
    u t = waveCosPropagator F (t - t₀) (u t₀) + waveSinPropagator F (t - t₀) (u' t₀) +
      ∫ τ in t₀..t, waveSinPropagator F (t - τ) (G τ) := by
  have hw := fun τ (hτ : τ ∈ uIcc t₀ t) ↦
    hasDerivWithinAt_duhamel (hu.mono (Set.OrdConnected.uIcc_subset ‹_› ht₀ ht)) t hτ
  -- `‖D⁻¹ sin((t - τ)D) G(τ)‖ ≤ |t - t₀| ‖G(τ)‖` for `τ` between `t₀` and `t`.
  have hint : IntervalIntegrable (fun τ ↦ waveSinPropagator F (t - τ) (G τ)) volume t₀ t := by
    refine (hG.smul |t - t₀|).mono_fun ?_ ?_
    · exact continuous_waveSinPropagator_uncurry.comp_aestronglyMeasurable
        ((continuous_const.sub continuous_id).aestronglyMeasurable.prodMk hG.def'.1)
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with τ hτ
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_abs]
      exact ((waveSinPropagator F (t - τ)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right ((norm_waveSinPropagator_le _).trans
          (abs_sub_right_of_mem_uIcc (uIoc_subset_uIcc hτ))) (norm_nonneg _))
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right
    (fun τ hτ ↦ (hw τ hτ).continuousWithinAt)
    (fun τ hτ ↦ ((hw τ (Ioo_subset_Icc_self hτ)).hasDerivAt
      (Icc_mem_nhds hτ.1 hτ.2)).hasDerivWithinAt) hint]
  simp

/-- A strong solution `u` of the free wave equation on an order-connected set of times `s`
containing `0` is `cos(tD) u(0) + D⁻¹ sin(tD) u'(0)` there, by Duhamel's formula. So its mixed
norm `L^q(s; L^r_x)` is at most that of this free solution over all times. -/
theorem IsWaveSolutionOn.eLpNorm_eLpNorm_restrict_le [s.OrdConnected]
    (hu : IsWaveSolutionOn u u' u'' 0 s) (h0 : 0 ∈ s) {q r : ℝ≥0∞} :
    eLpNorm (fun t ↦ eLpNorm (u t) r volume) q (volume.restrict s) ≤
      eLpNorm (fun t ↦ eLpNorm (waveCosPropagator F t (u 0) + waveSinPropagator F t (u' 0)) r
        volume) q volume := by
  have hrep : ∀ᵐ t ∂volume.restrict s, eLpNorm (u t) r volume =
      eLpNorm (waveCosPropagator F t (u 0) + waveSinPropagator F t (u' 0)) r volume :=
    ae_restrict_of_forall_mem (Set.OrdConnected.measurableSet ‹_›) fun t ht ↦ by
      rw [hu.eq_waveCosPropagator_add_waveSinPropagator_add_integral h0 ht
        intervalIntegrable_const]
      simp
  rw [eLpNorm_congr_ae hrep]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

end TauCeti

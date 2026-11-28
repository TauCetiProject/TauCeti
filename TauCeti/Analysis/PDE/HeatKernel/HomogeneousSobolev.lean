/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Fourier
public import TauCeti.Analysis.Sobolev.Homogeneous
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Space-time estimates for the heat flow in homogeneous Sobolev seminorms

For `f ∈ L²(E; F)`, with `F` a complex Hilbert space, and a viscosity `ν > 0`, the heat flow
`t ↦ e^{νtΔ} f` gains derivatives when integrated in time. On the Fourier side `e^{νtΔ}` is the
multiplier `exp(-4π²νt‖ξ‖²)`, and `∫₀^∞ (2π‖ξ‖)² exp(-8π²νt‖ξ‖²) dt = 1/(2ν)` for `ξ ≠ 0`. This
file proves, for every `s ≥ 0`:

* the energy identity `∫₀^∞ |e^{νtΔ} f|²_{\dot H^{s+1}} dt = |f|²_{\dot H^s} / (2ν)`
  (`TauCeti.lintegral_eHomogeneousSobolevNorm_heatSemigroup_sq_eq`, in dimension at least one;
  the inequality `≤` holds in every dimension);
* the `L⁴`-in-time estimate `∫₀^∞ |e^{νtΔ} f|⁴_{\dot H^{s+1/2}} dt ≤ |f|⁴_{\dot H^s} / (4ν)`
  (`TauCeti.lintegral_eHomogeneousSobolevNorm_heatSemigroup_pow_four_le`).

At `s = 0` the first is the identity `∫₀^∞ ‖∇e^{νtΔ} f‖²₂ dt = ‖f‖²₂ / (2ν)`. At `s = 1/2` the
second is the linear estimate of the Fujita–Kato theorem,
`‖e^{νtΔ} u₀‖_{L⁴(0,∞; \dot H^1)} ≤ (4ν)^{-1/4} |u₀|_{\dot H^{1/2}}`: the free heat flow of data in
the critical space `\dot H^{1/2}(ℝ³)` lies in `L⁴(0,∞; \dot H^1)`, the space in which the
Navier–Stokes equations are solved by a fixed-point argument. Both estimates are invariant under
the scaling `f ↦ f(λ·)`, `t ↦ λ²t`.

The `L⁴` estimate comes from the pointwise-in-time bound
`|e^{tΔ} f|⁴_{\dot H^{s+1/2}} ≤ |f|²_{\dot H^s} |e^{2tΔ} f|²_{\dot H^{s+1}}`
(`TauCeti.eHomogeneousSobolevNorm_heatSemigroup_pow_four_le`), the Cauchy–Schwarz inequality on
the Fourier side, integrated in time with the energy identity at viscosity `2ν`.

## References

* H. Bahouri, J.-Y. Chemin, R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, Chapter 5: the Fujita–Kato theorem in `L⁴(0,T; \dot H^1)`.
* J. Bedrossian, V. Vicol, *The Mathematical Analysis of the Incompressible Euler and
  Navier–Stokes Equations: An Introduction*, AMS, 2022, Theorem 5.4: the Fujita–Kato theorem in
  `C([0,T]; \dot H^{1/2}) ∩ L⁴(0,T; \dot H^1)`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Real Set
open scoped ENNReal NNReal FourierTransform

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- **The homogeneous seminorms of the heat flow on the Fourier side.** For `s ≥ 0`,
`|e^{tΔ} f|²_{\dot H^s} = ∫ (2π‖ξ‖)^{2s} exp(-8π²t‖ξ‖²) ‖𝓕 f(ξ)‖² dξ`. -/
theorem eHomogeneousSobolevNorm_heatSemigroup_sq {s : ℝ} (hs : 0 ≤ s) (t : ℝ≥0)
    (f : Lp F 2 (volume : Measure E)) :
    Lp.eHomogeneousSobolevNorm (heatSemigroup (p := 2) ENNReal.ofNat_ne_top t f) s ^ 2 =
      ∫⁻ ξ, ENNReal.ofReal (2 * π * ‖ξ‖) ^ (2 * s) *
        ENNReal.ofReal (exp (-(8 * π ^ 2 * t * ‖ξ‖ ^ 2))) *
          ‖(𝓕 f : Lp F 2 (volume : Measure E)) ξ‖ₑ ^ 2 := by
  rw [Lp.eHomogeneousSobolevNorm_sq hs]
  refine lintegral_congr_ae ?_
  filter_upwards [coeFn_fourier_heatSemigroup t f] with ξ hξ
  rw [hξ, eNorm_smul, Real.eNorm_of_nonneg (exp_pos _).le, mul_pow,
    ← ENNReal.ofReal_pow (exp_pos _).le, ← exp_natCast_mul, ← mul_assoc]
  congr 4
  push_cast
  ring

/-- The heat flow does not increase the homogeneous seminorms:
`|e^{tΔ} f|_{\dot H^s} ≤ |f|_{\dot H^s}`. -/
theorem eHomogeneousSobolevNorm_heatSemigroup_le (s : ℝ) (t : ℝ≥0)
    (f : Lp F 2 (volume : Measure E)) :
    Lp.eHomogeneousSobolevNorm (heatSemigroup (p := 2) ENNReal.ofNat_ne_top t f) s ≤
      Lp.eHomogeneousSobolevNorm f s := by
  rw [Lp.eHomogeneousSobolevNorm_def, Lp.eHomogeneousSobolevNorm_def]
  refine eLpNorm_mono_ae ((by fun_prop : Measurable fun ξ : E ↦ (2 * π * ‖ξ‖) ^ s)
    |>.aestronglyMeasurable.smul (Lp.aestronglyMeasurable _)) ?_
  filter_upwards [coeFn_fourier_heatSemigroup t f] with ξ hξ
  rw [hξ, smul_comm, norm_smul, Real.norm_of_nonneg (exp_pos _).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (exp_le_one_iff.2 (neg_nonpos.2 (by positivity)))

/-- The time integral of the Fourier weight of `|e^{νtΔ} f|²_{\dot H^{s+1}}` at a frequency of size
`r > 0`: `∫₀^∞ (2πr)^{2(s+1)} exp(-8π²νtr²) dt = (2πr)^{2s} / (2ν)`. -/
private theorem lintegral_Ioi_weight_mul_exp_eq {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) {r : ℝ}
    (hr : 0 < r) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * π * r) ^ (2 * (s + 1)) *
        ENNReal.ofReal (exp (-(8 * π ^ 2 * (ν * t) * r ^ 2))) =
      ENNReal.ofReal (2 * ν)⁻¹ * ENNReal.ofReal (2 * π * r) ^ (2 * s) := by
  have hc : 0 < 8 * π ^ 2 * ν * r ^ 2 := by positivity
  simp_rw [show ∀ t : ℝ, -(8 * π ^ 2 * (ν * t) * r ^ 2) = -(8 * π ^ 2 * ν * r ^ 2) * t from
    fun t ↦ by ring]
  rw [lintegral_const_mul' _ _ (by finiteness), lintegral_Ioi_ofReal_exp_neg_mul hc,
    show 2 * (s + 1) = 2 * s + 2 by ring,
    ENNReal.rpow_add_of_nonneg _ _ (by positivity) zero_le_two, ENNReal.rpow_two,
    ← ENNReal.ofReal_pow (by positivity), mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_comm]
  congr 2
  field_simp
  ring

/-- The time integral of `|e^{νtΔ} f|²_{\dot H^{s+1}}` as a frequency integral of the time integrals
of the Fourier weights. -/
private theorem lintegral_eHomogeneousSobolevNorm_heatSemigroup_sq_eq_lintegral {ν s : ℝ}
    (hν : 0 < ν) (hs : 0 ≤ s) (f : Lp F 2 (volume : Measure E)) :
    ∫⁻ t in Ioi 0, Lp.eHomogeneousSobolevNorm
        (heatSemigroup (p := 2) ENNReal.ofNat_ne_top (ν * t).toNNReal f) (s + 1) ^ 2 =
      ∫⁻ ξ, (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * π * ‖ξ‖) ^ (2 * (s + 1)) *
        ENNReal.ofReal (exp (-(8 * π ^ 2 * (ν * t) * ‖ξ‖ ^ 2)))) *
          ‖(𝓕 f : Lp F 2 (volume : Measure E)) ξ‖ₑ ^ 2 := by
  rw [setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ by
    rw [eHomogeneousSobolevNorm_heatSemigroup_sq (by positivity),
      Real.coe_toNNReal _ (mul_pos hν ht).le]]
  rw [lintegral_lintegral_swap (by fun_prop)]
  exact lintegral_congr fun ξ ↦ lintegral_mul_const _ (by fun_prop)

/-- **The energy inequality for the heat flow in homogeneous seminorms.** For `ν > 0`, `s ≥ 0` and
`f ∈ L²(E; F)`, `∫₀^∞ |e^{νtΔ} f|²_{\dot H^{s+1}} dt ≤ |f|²_{\dot H^s} / (2ν)`. This holds in every
dimension; in dimension at least one it is an equality
(`TauCeti.lintegral_eHomogeneousSobolevNorm_heatSemigroup_sq_eq`). -/
theorem lintegral_eHomogeneousSobolevNorm_heatSemigroup_sq_le {ν s : ℝ} (hν : 0 < ν)
    (hs : 0 ≤ s) (f : Lp F 2 (volume : Measure E)) :
    ∫⁻ t in Ioi 0, Lp.eHomogeneousSobolevNorm
        (heatSemigroup (p := 2) ENNReal.ofNat_ne_top (ν * t).toNNReal f) (s + 1) ^ 2 ≤
      ENNReal.ofReal (2 * ν)⁻¹ * Lp.eHomogeneousSobolevNorm f s ^ 2 := by
  rw [lintegral_eHomogeneousSobolevNorm_heatSemigroup_sq_eq_lintegral hν hs,
    Lp.eHomogeneousSobolevNorm_sq hs, ← lintegral_const_mul' _ _ (by finiteness)]
  refine lintegral_mono fun ξ ↦ ?_
  rw [← mul_assoc]
  gcongr
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [ENNReal.zero_rpow_of_pos (by positivity : (0 : ℝ) < 2 * (s + 1))]
  · exact (lintegral_Ioi_weight_mul_exp_eq hν hs (norm_pos_iff.2 hξ)).le

/-- **The energy identity for the heat flow in homogeneous seminorms.** For `ν > 0`, `s ≥ 0` and
`f ∈ L²(E; F)` on a space of dimension at least one,
`∫₀^∞ |e^{νtΔ} f|²_{\dot H^{s+1}} dt = |f|²_{\dot H^s} / (2ν)`. At `s = 0` this is
`∫₀^∞ ‖∇e^{νtΔ} f‖²₂ dt = ‖f‖²₂ / (2ν)`. -/
theorem lintegral_eHomogeneousSobolevNorm_heatSemigroup_sq_eq [Nontrivial E] {ν s : ℝ}
    (hν : 0 < ν) (hs : 0 ≤ s) (f : Lp F 2 (volume : Measure E)) :
    ∫⁻ t in Ioi 0, Lp.eHomogeneousSobolevNorm
        (heatSemigroup (p := 2) ENNReal.ofNat_ne_top (ν * t).toNNReal f) (s + 1) ^ 2 =
      ENNReal.ofReal (2 * ν)⁻¹ * Lp.eHomogeneousSobolevNorm f s ^ 2 := by
  rw [lintegral_eHomogeneousSobolevNorm_heatSemigroup_sq_eq_lintegral hν hs,
    Lp.eHomogeneousSobolevNorm_sq hs, ← lintegral_const_mul' _ _ (by finiteness)]
  have h0 : ∀ᵐ ξ ∂(volume : Measure E), ξ ≠ 0 := by
    simp [ae_iff]
  refine lintegral_congr_ae (h0.mono fun ξ hξ ↦ ?_)
  dsimp only
  rw [lintegral_Ioi_weight_mul_exp_eq hν hs (norm_pos_iff.2 hξ), mul_assoc]

/-- **The pointwise-in-time bound behind the `L⁴` estimate.** For `s ≥ 0` and `t ≥ 0`,
`|e^{tΔ} f|⁴_{\dot H^{s+1/2}} ≤ |f|²_{\dot H^s} |e^{2tΔ} f|²_{\dot H^{s+1}}`. -/
theorem eHomogeneousSobolevNorm_heatSemigroup_pow_four_le {s : ℝ} (hs : 0 ≤ s) (t : ℝ≥0)
    (f : Lp F 2 (volume : Measure E)) :
    Lp.eHomogeneousSobolevNorm (heatSemigroup (p := 2) ENNReal.ofNat_ne_top t f) (s + 1 / 2) ^ 4 ≤
      Lp.eHomogeneousSobolevNorm f s ^ 2 *
        Lp.eHomogeneousSobolevNorm
          (heatSemigroup (p := 2) ENNReal.ofNat_ne_top (2 * t) f) (s + 1) ^ 2 := by
  have hsq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  -- Cauchy–Schwarz for the measure `‖𝓕 f(ξ)‖² dξ`, splitting the weight of the left side as
  -- `(2π‖ξ‖)^{2s+1} exp(-8π²t‖ξ‖²) = (2π‖ξ‖)^s · (2π‖ξ‖)^{s+1} exp(-8π²t‖ξ‖²)`.
  rw [show 4 = 2 * 2 by rfl, pow_mul, eHomogeneousSobolevNorm_heatSemigroup_sq (by positivity),
    eHomogeneousSobolevNorm_heatSemigroup_sq (by positivity), Lp.eHomogeneousSobolevNorm_sq hs,
    ← hsq ((∫⁻ ξ, _) * _), ENNReal.mul_rpow_of_nonneg _ _ hhalf]
  gcongr
  refine le_of_eq_of_le (lintegral_congr fun ξ ↦ ?_)
    (ENNReal.lintegral_mul_norm_pow_le (by fun_prop) (by fun_prop) hhalf hhalf (by norm_num))
  have he : ENNReal.ofReal (exp (-(8 * π ^ 2 * ((2 * t : ℝ≥0) : ℝ) * ‖ξ‖ ^ 2))) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (exp (-(8 * π ^ 2 * t * ‖ξ‖ ^ 2))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le hhalf, ← exp_mul]
    congr 2
    push_cast
    ring
  have hw : ENNReal.ofReal (2 * π * ‖ξ‖) ^ (2 * s * (1 / 2)) *
      ENNReal.ofReal (2 * π * ‖ξ‖) ^ (2 * (s + 1) * (1 / 2)) =
        ENNReal.ofReal (2 * π * ‖ξ‖) ^ (2 * (s + 1 / 2)) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
    ring_nf
  have ha (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ hhalf hhalf]
    norm_num
  set w := ENNReal.ofReal (2 * π * ‖ξ‖)
  set x := ‖(𝓕 f : Lp F 2 (volume : Measure E)) ξ‖ₑ ^ 2
  rw [ENNReal.mul_rpow_of_nonneg _ _ hhalf, ENNReal.mul_rpow_of_nonneg _ _ hhalf,
    ENNReal.mul_rpow_of_nonneg _ _ hhalf, he, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  calc _ = (w ^ (2 * s * (1 / 2)) * w ^ (2 * (s + 1) * (1 / 2))) *
        ENNReal.ofReal (exp (-(8 * π ^ 2 * t * ‖ξ‖ ^ 2))) *
          (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by
        rw [hw, ha]
    _ = _ := by ring

/-- **The `L⁴`-in-time estimate for the heat flow in homogeneous seminorms.** For `ν > 0`, `s ≥ 0`
and `f ∈ L²(E; F)`, `∫₀^∞ |e^{νtΔ} f|⁴_{\dot H^{s+1/2}} dt ≤ |f|⁴_{\dot H^s} / (4ν)`. At `s = 1/2`
this is the linear estimate of the Fujita–Kato theorem,
`‖e^{νtΔ} u₀‖_{L⁴(0,∞; \dot H^1)} ≤ (4ν)^{-1/4} |u₀|_{\dot H^{1/2}}`. -/
theorem lintegral_eHomogeneousSobolevNorm_heatSemigroup_pow_four_le {ν s : ℝ} (hν : 0 < ν)
    (hs : 0 ≤ s) (f : Lp F 2 (volume : Measure E)) :
    ∫⁻ t in Ioi 0, Lp.eHomogeneousSobolevNorm
        (heatSemigroup (p := 2) ENNReal.ofNat_ne_top (ν * t).toNNReal f) (s + 1 / 2) ^ 4 ≤
      ENNReal.ofReal (4 * ν)⁻¹ * Lp.eHomogeneousSobolevNorm f s ^ 4 := by
  rcases eq_or_ne (Lp.eHomogeneousSobolevNorm f s) ∞ with hf | hf
  · simp [hf, ENNReal.top_pow, hν]
  calc _ ≤ ∫⁻ t in Ioi 0, Lp.eHomogeneousSobolevNorm f s ^ 2 * Lp.eHomogeneousSobolevNorm
          (heatSemigroup (p := 2) ENNReal.ofNat_ne_top (2 * ν * t).toNNReal f) (s + 1) ^ 2 := by
        refine lintegral_mono fun t ↦ ?_
        rw [mul_assoc, Real.toNNReal_mul zero_le_two, Real.toNNReal_ofNat]
        exact eHomogeneousSobolevNorm_heatSemigroup_pow_four_le hs _ f
    _ ≤ Lp.eHomogeneousSobolevNorm f s ^ 2 *
          (ENNReal.ofReal (2 * (2 * ν))⁻¹ * Lp.eHomogeneousSobolevNorm f s ^ 2) := by
        rw [lintegral_const_mul' _ _ (by finiteness)]
        gcongr
        exact lintegral_eHomogeneousSobolevNorm_heatSemigroup_sq_le (by positivity) hs f
    _ = _ := by
        rw [mul_left_comm, ← pow_add, ← mul_assoc]
        norm_num

end TauCeti

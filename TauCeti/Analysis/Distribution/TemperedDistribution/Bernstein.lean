/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent

/-!
# Bernstein's inequalities

A function whose Fourier transform is supported in a ball of radius `R` behaves, as far as `Lᵖ`
norms see, like a function on a lattice of mesh `1 / R`: differentiating it costs a factor `R`,
and raising the integrability exponent from `p` to `q ≥ p` costs a factor `R ^ (n (1 / p - 1 / q))`
in dimension `n`. These are **Bernstein's inequalities**: for `1 ≤ p ≤ q ≤ ∞` and `k : ℕ` there is
`C`, independent of `R`, `f` and the directions `m i`, such that

`‖∂_{m 0} ⋯ ∂_{m (k-1)} f‖_q ≤ C R ^ (k + n (1 / p - 1 / q)) ∏ ‖m i‖ ‖f‖_p`

for every `f ∈ Lᵖ` with Fourier transform supported in the closed ball of radius `R > 0`. They
turn bounds on the single Littlewood–Paley blocks of a function into bounds on its derivatives and
on its higher `L^q` norms, which is how the dyadic description of Besov and Sobolev spaces is
used.

The Fourier support condition is stated with Mathlib's `Distribution.IsVanishingOn`: the Fourier
transform of `f` vanishes on every Schwartz function supported in the complement of the closed
ball. Exponents are elements of `ℝ≥0∞` and `1 / p` is written `p.toReal⁻¹`, which reads as `0`
at `p = ∞`.

## Proof

Fix a smooth bump `χ` equal to `1` on the closed ball of radius `2`. If the Fourier transform of
`u` vanishes off a set `s` and a symbol `g` equals `1` near `s`, the Fourier multiplier with
symbol `g` fixes `u` (`TemperedDistribution.fourierMultiplierCLM_eq_self_of_isVanishingOn`); so
`f` is fixed by the multiplier with symbol `χ(R⁻¹ ·)`, which is convolution with the Schwartz
kernel `K_R = 𝓕⁻ (χ(R⁻¹ ·))`.

* One derivative: `∂_v f` is the multiplier with the Schwartz symbol
  `2πi ⟪ξ, v⟫ χ(R⁻¹ ξ)`, whose kernel is the dilate of `∂_{R v} K_1`, so it has `L¹` norm at most
  `R ‖v‖ ‖D K_1‖₁`. The `L¹` bound for multipliers with Schwartz symbols gives
  `‖∂_v f‖_p ≤ C R ‖v‖ ‖f‖_p`, and since differentiation does not enlarge the Fourier support
  (`TemperedDistribution.isVanishingOn_fourier_lineDerivOp`), this iterates to `k` derivatives.
* `Lᵖ → L^∞`, `p < ∞`: on Schwartz functions, Hölder's inequality for convolution
  (`MeasureTheory.enorm_convolution_le`) bounds the multiplier by `‖K_R‖_{p'}`,
  and interpolating between `‖K_R‖_∞ ≤ R ^ n ∫ χ` and `‖K_R‖₁ = ‖K_1‖₁` gives
  `‖K_R‖_{p'} ≤ C R ^ (n / p)`. Schwartz functions are dense in `Lᵖ`, so the bound extends to `f`.
* `Lᵖ → L^q`: interpolate between `‖f‖_p` and `‖f‖_∞`
  (`MeasureTheory.eLpNorm_le_eLpNorm_top_rpow_mul_eLpNorm_rpow`).

## Main declarations

* `TemperedDistribution.exists_eq_and_norm_le_of_isVanishingOn_fourier`: Bernstein's inequality
  `‖f‖_q ≤ C R ^ (n (1 / p - 1 / q)) ‖f‖_p`.
* `TemperedDistribution.exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier`:
  Bernstein's inequality for `k` derivatives.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren 343, Springer, 2011, Lemma 2.1.
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Graduate Texts in Mathematics 250, Springer,
  2014, Theorem 1.3.1 (Bernstein's inequalities in the `Lᵖ → L^q` form).
-/

public section

noncomputable section

open MeasureTheory Filter Topology Metric Distribution Module Real
open scoped ENNReal SchwartzMap FourierTransform Convolution LineDeriv

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### The low-pass cutoff at frequency scale `R` -/

/-- The smooth bump equal to `1` on the closed ball of radius `2` about the origin and supported
in the ball of radius `3`. -/
private def bump : ContDiffBump (0 : E) := ⟨2, 3, two_pos, by norm_num⟩

/-- The low-pass symbol `ξ ↦ χ(R⁻¹ ξ)` at frequency scale `R ≠ 0`, a Schwartz function. -/
private def lowPass {R : ℝ} (hR : R ≠ 0) : 𝓢(E, ℂ) :=
  ((bump.hasCompactSupport.comp_smul (inv_ne_zero hR)).comp_left
    Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp ((bump (E := E)).contDiff.comp (contDiff_const_smul _)))

omit [MeasurableSpace E] [BorelSpace E] in
private theorem lowPass_apply {R : ℝ} (hR : R ≠ 0) (ξ : E) :
    lowPass hR ξ = (bump (E := E) (R⁻¹ • ξ) : ℂ) :=
  HasCompactSupport.toSchwartzMap_toFun _ _ _

omit [MeasurableSpace E] [BorelSpace E] in
/-- The low-pass symbol at scale `R > 0` equals `1` near the closed ball of radius `R`. -/
private theorem eventually_lowPass_eq_one {R : ℝ} (hR : 0 < R) :
    ∀ᶠ ξ in 𝓝ˢ (closedBall (0 : E) R), lowPass hR.ne' ξ = 1 := by
  refine mem_nhdsSet_iff_exists.2 ⟨ball 0 (2 * R), isOpen_ball,
    closedBall_subset_ball (by linarith), fun ξ hξ ↦ ?_⟩
  rw [mem_ball_zero_iff] at hξ
  have hmem : R⁻¹ • ξ ∈ closedBall (0 : E) (bump (E := E)).rIn := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hR.le,
      inv_mul_le_iff₀ hR]
    exact (show (bump (E := E)).rIn = 2 from rfl) ▸ by linarith
  rw [Set.mem_ofPred_eq, lowPass_apply, bump.one_of_mem_closedBall hmem, Complex.ofReal_one]

/-- A tempered distribution whose Fourier transform vanishes off the closed ball of radius `R` is
fixed by the low-pass multiplier at scale `R`. -/
private theorem fourierMultiplierCLM_lowPass {R : ℝ} (hR : 0 < R) {u : 𝓢'(E, F)}
    (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) (closedBall 0 R)ᶜ) :
    fourierMultiplierCLM F (lowPass hR.ne') u = u :=
  fourierMultiplierCLM_eq_self_of_isVanishingOn (lowPass hR.ne').hasTemperateGrowth hu
    (eventually_lowPass_eq_one hR)

/-- The `L¹` norm `A = ∫ |χ|` of the bump. -/
private def bumpMass : ℝ := ∫ ξ, ‖(bump (E := E) ξ : ℂ)‖

/-- The `L¹` norm `B = ‖𝓕⁻ χ‖₁` of the kernel of the low-pass multiplier, the same at every
scale. -/
private def kernelMass : ℝ := ∫ x, ‖(𝓕⁻ (fun ξ ↦ (bump (E := E) ξ : ℂ)) : E → ℂ) x‖

/-- The kernel of the low-pass multiplier has the same `L¹` norm at every scale. -/
private theorem integral_norm_fourierInv_lowPass {R : ℝ} (hR : R ≠ 0) :
    ∫ x, ‖𝓕⁻ (lowPass hR : E → ℂ) x‖ = kernelMass (E := E) := by
  have h : (lowPass hR : E → ℂ) = fun ξ ↦ (fun η ↦ (bump (E := E) η : ℂ)) (R⁻¹ • ξ) :=
    funext (lowPass_apply hR)
  rw [h]
  exact TauCeti.integral_norm_fourierInv_comp_smul (fun η ↦ (bump (E := E) η : ℂ))
    (inv_ne_zero hR)

/-- The kernel of the low-pass multiplier at scale `R` is bounded by `R ^ n A`. -/
private theorem norm_fourierInv_lowPass_le {R : ℝ} (hR : 0 < R) (x : E) :
    ‖𝓕⁻ (lowPass hR.ne' : E → ℂ) x‖ ≤ R ^ finrank ℝ E * bumpMass (E := E) := by
  rw [Real.fourierInv_eq_fourier_neg]
  refine (Real.norm_fourier_le_integral_norm _ _).trans_eq ?_
  simp_rw [lowPass_apply]
  exact Measure.integral_comp_inv_smul_of_nonneg volume (fun ξ ↦ ‖(bump (E := E) ξ : ℂ)‖) hR.le

/-! ### Bernstein's inequality without derivatives -/

/-- The conjugate exponent `p' = (1 - p⁻¹)⁻¹` satisfies `1 / p' = 1 - 1 / p`, read through
`ENNReal.toReal`. -/
private theorem toReal_inv_one_sub_inv_inv {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ((1 - p⁻¹)⁻¹).toReal⁻¹ = 1 - p.toReal⁻¹ := by
  rw [ENNReal.toReal_inv, inv_inv, ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.2 hp)
    ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_inv]

/-- For the exponent `p'` conjugate to `p`, the kernel `K` of the low-pass multiplier at scale `R`
has `‖K‖_{p'} ≤ (R ^ n A) ^ (1 / p) B ^ (1 - 1 / p)`. This interpolates between `‖K‖_∞ ≤ R ^ n A`
and `‖K‖₁ = B`. -/
private theorem eLpNorm_fourierInv_lowPass_le {R : ℝ} (hR : 0 < R) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (𝓕⁻ (lowPass (E := E) hR.ne') : 𝓢(E, ℂ)) (1 - p⁻¹)⁻¹ volume ≤
      ENNReal.ofReal (R ^ finrank ℝ E * bumpMass (E := E)) ^ p.toReal⁻¹ *
        ENNReal.ofReal (kernelMass (E := E)) ^ (1 - p.toReal⁻¹) := by
  set κ : 𝓢(E, ℂ) := 𝓕⁻ (lowPass (E := E) hR.ne')
  have hp' : 1 ≤ (1 - p⁻¹)⁻¹ :=
    (ENNReal.HolderConjugate.inv_one_sub_inv' hp).symm.one_le
  have h_top : eLpNorm κ ∞ volume ≤ ENNReal.ofReal (R ^ finrank ℝ E * bumpMass (E := E)) := by
    rw [eLpNorm_exponent_top κ.continuous.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x ↦ by
      simpa only [κ, SchwartzMap.fourierInv_coe] using norm_fourierInv_lowPass_le hR x)
  have h_one : eLpNorm κ 1 volume = ENNReal.ofReal (kernelMass (E := E)) := by
    rw [eLpNorm_one_eq_lintegral_enorm κ.continuous.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (κ.integrable (μ := volume)),
      SchwartzMap.fourierInv_coe, integral_norm_fourierInv_lowPass hR.ne']
  have h := eLpNorm_le_eLpNorm_top_rpow_mul_eLpNorm_rpow κ.continuous.aestronglyMeasurable
    one_ne_zero hp' (μ := volume)
  rw [ENNReal.toReal_one, one_div, toReal_inv_one_sub_inv_inv hp, sub_sub_cancel, h_one] at h
  exact h.trans (by gcongr)

variable [CompleteSpace F]

/-- On Schwartz functions, the low-pass multiplier at scale `R` maps `Lᵖ` to `L^∞` with norm at
most `A ^ (1 / p) B ^ (1 - 1 / p) R ^ (n / p)`. It is convolution with its kernel `K`, so Hölder's
inequality bounds it by `‖K‖_{p'}`. -/
private theorem norm_toLp_top_fourierMultiplierCLM_lowPass_le {R : ℝ} (hR : 0 < R) {p : ℝ≥0∞}
    [hp : Fact (1 ≤ p)] (φ : 𝓢(E, F)) :
    ‖(SchwartzMap.fourierMultiplierCLM F (lowPass hR.ne') φ).toLp ∞‖ ≤
      bumpMass (E := E) ^ p.toReal⁻¹ * kernelMass (E := E) ^ (1 - p.toReal⁻¹) *
        R ^ (finrank ℝ E * p.toReal⁻¹) * ‖φ.toLp p‖ := by
  set σ := lowPass (E := E) hR.ne'
  have : ((1 - p⁻¹)⁻¹).HolderConjugate p :=
    (ENNReal.HolderConjugate.inv_one_sub_inv' hp.out).symm
  have hA : 0 ≤ bumpMass (E := E) := integral_nonneg fun _ ↦ norm_nonneg _
  have hB : 0 ≤ kernelMass (E := E) := integral_nonneg fun _ ↦ norm_nonneg _
  have ha : 0 ≤ 1 - p.toReal⁻¹ := by
    rw [← toReal_inv_one_sub_inv_inv hp.out]
    positivity
  have hconv : (SchwartzMap.fourierMultiplierCLM F σ φ : E → F) =
      ⇑(𝓕⁻ σ : 𝓢(E, ℂ)) ⋆[ContinuousLinearMap.lsmul ℂ ℂ] φ := by
    funext x
    rw [SchwartzMap.fourierMultiplierCLM_eq_convolution, SchwartzMap.convolution_apply]
  have hle : eLpNorm (SchwartzMap.fourierMultiplierCLM F σ φ) ∞ volume ≤
      ENNReal.ofReal (R ^ finrank ℝ E * bumpMass (E := E)) ^ p.toReal⁻¹ *
        ENNReal.ofReal (kernelMass (E := E)) ^ (1 - p.toReal⁻¹) * eLpNorm φ p volume := by
    rw [eLpNorm_exponent_top
      (SchwartzMap.fourierMultiplierCLM F σ φ).continuous.aestronglyMeasurable]
    refine eLpNormEssSup_le_of_ae_enorm_bound (Eventually.of_forall fun x ↦ ?_)
    rw [hconv]
    refine (enorm_convolution_le (p := (1 - p⁻¹)⁻¹) (q := p) _
      (𝓕⁻ σ).continuous.aestronglyMeasurable φ.continuous.aestronglyMeasurable x).trans ?_
    grw [ContinuousLinearMap.opENorm_lsmul_le, one_mul, eLpNorm_fourierInv_lowPass_le hR hp.out]
  have hfin : ENNReal.ofReal (R ^ finrank ℝ E * bumpMass (E := E)) ^ p.toReal⁻¹ *
      ENNReal.ofReal (kernelMass (E := E)) ^ (1 - p.toReal⁻¹) * eLpNorm φ p volume ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg ha ENNReal.ofReal_ne_top)) (φ.memLp p volume).eLpNorm_ne_top
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
  refine (ENNReal.toReal_mono hfin hle).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hB,
    Real.mul_rpow (by positivity) hA, ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
  ring

/-- **Bernstein's inequality, `Lᵖ → L^∞`.** For `1 ≤ p < ∞`, a function `f ∈ Lᵖ` whose Fourier
transform is supported in the closed ball of radius `R` is essentially bounded, with
`‖f‖_∞ ≤ C R ^ (n / p) ‖f‖_p`. -/
private theorem exists_eq_lpTop_and_norm_le {p : ℝ≥0∞} [hp1 : Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ →
      ∃ g : Lp F ∞ (volume : Measure E), (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ C * R ^ (finrank ℝ E * p.toReal⁻¹) * ‖f‖ := by
  have hA : 0 ≤ bumpMass (E := E) := integral_nonneg fun _ ↦ norm_nonneg _
  have hB : 0 ≤ kernelMass (E := E) := integral_nonneg fun _ ↦ norm_nonneg _
  refine ⟨bumpMass (E := E) ^ p.toReal⁻¹ * kernelMass (E := E) ^ (1 - p.toReal⁻¹),
    mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _), fun {R} hR f hf ↦ ?_⟩
  set σ := lowPass (E := E) hR.ne'
  -- The low-pass multiplier fixes `f`, and is bounded from `Lᵖ` to `L^∞` on Schwartz functions.
  have hT : ∀ φ : 𝓢(E, F), (fourierMultiplierCLM F σ ∘L
      Lp.toTemperedDistributionCLM F volume p) (φ.toLp p) =
        ((SchwartzMap.fourierMultiplierCLM F σ φ).toLp ∞ : 𝓢'(E, F)) := by
    intro φ
    simp only [ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistribution_toLp_eq,
      fourierMultiplierCLM_toTemperedDistributionCLM_eq σ.hasTemperateGrowth]
  obtain ⟨g, hg, hgf⟩ := (fourierMultiplierCLM F σ ∘L
    Lp.toTemperedDistributionCLM F volume p).exists_apply_eq_toTemperedDistribution_and_norm_le
      hp _ hT (norm_toLp_top_fourierMultiplierCLM_lowPass_le hR) f
  refine ⟨g, ?_, hgf.trans_eq (by ring)⟩
  rw [← hg, ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply,
    fourierMultiplierCLM_lowPass hR hf]

/-- **Bernstein's inequality, `Lᵖ → L^q`.** For `1 ≤ p ≤ q ≤ ∞` there is `C`, independent of `R`
and `f`, such that every `f ∈ Lᵖ` whose Fourier transform is supported in the closed ball of
radius `R > 0` lies in `L^q`, with `‖f‖_q ≤ C R ^ (n (1 / p - 1 / q)) ‖f‖_p` in dimension `n`.

The exponents `1 / p` and `1 / q` are written `p.toReal⁻¹` and `q.toReal⁻¹`, which read as `0` at
`∞`. The Fourier support condition is that the Fourier transform of `f` vanishes on every
Schwartz function supported off the closed ball. -/
theorem exists_eq_and_norm_le_of_isVanishingOn_fourier {p q : ℝ≥0∞}
    [hp1 : Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ →
      ∃ g : Lp F q (volume : Measure E), (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ C * R ^ (finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹)) * ‖f‖ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · obtain rfl := top_le_iff.1 hpq
    exact ⟨1, zero_le_one, fun _ f _ ↦ ⟨f, rfl, by simp⟩⟩
  obtain ⟨C, hC, hCf⟩ := exists_eq_lpTop_and_norm_le (E := E) (F := F) hp
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1.out).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set θ := p.toReal / q.toReal
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rcases eq_or_ne q ∞ with rfl | hq
    · simp [θ]
    · exact div_le_one_of_le₀ (ENNReal.toReal_mono hq hpq) ENNReal.toReal_nonneg
  refine ⟨C ^ (1 - θ), by positivity, fun {R} hR f hf ↦ ?_⟩
  obtain ⟨g, hfg, hg⟩ := hCf hR f hf
  -- `f` agrees almost everywhere with the bounded function `g`.
  have hae : (f : E → F) =ᵐ[volume] g := Lp.ae_eq_of_toTemperedDistribution_apply_eq f
    ((Lp.memLp g).locallyIntegrable le_top) fun φ ↦ by rw [hfg, Lp.toTemperedDistribution_apply]
  have hmem : MemLp (f : E → F) q volume :=
    (Lp.memLp f).of_le_of_le ((Lp.memLp g).ae_eq hae.symm) hp0 hpq le_top
  refine ⟨hmem.toLp f, ?_, ?_⟩
  · ext φ
    rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
    exact integral_congr_ae ((MemLp.coeFn_toLp hmem).mono fun x hx ↦ by simp only [hx])
  -- Interpolate between `‖f‖_∞ = ‖g‖_∞` and `‖f‖_p`.
  have hint := eLpNorm_le_eLpNorm_top_rpow_mul_eLpNorm_rpow (Lp.aestronglyMeasurable f) hp0 hpq
    (μ := volume)
  rw [eLpNorm_congr_ae (p := ∞) hae] at hint
  rw [Lp.norm_toLp]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hθ1) (Lp.eLpNorm_ne_top g))
    (ENNReal.rpow_ne_top_of_nonneg hθ0 (Lp.eLpNorm_ne_top f))) hint).trans ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← Lp.norm_def,
    ← Lp.norm_def]
  calc ‖g‖ ^ (1 - θ) * ‖f‖ ^ θ
      ≤ (C * R ^ (finrank ℝ E * p.toReal⁻¹) * ‖f‖) ^ (1 - θ) * ‖f‖ ^ θ := by
        gcongr
    _ = C ^ (1 - θ) * R ^ (finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹)) * ‖f‖ := by
        have hpq' : p.toReal⁻¹ * θ = q.toReal⁻¹ := by
          rw [show θ = p.toReal * q.toReal⁻¹ from div_eq_mul_inv _ _, ← mul_assoc,
            inv_mul_cancel₀ hpr.ne', one_mul]
        rw [Real.mul_rpow (by positivity) (norm_nonneg _), Real.mul_rpow hC (by positivity),
          ← Real.rpow_mul hR.le, mul_assoc, ← Real.rpow_add' (norm_nonneg _) (by norm_num),
          sub_add_cancel, Real.rpow_one, ← hpq', mul_assoc, ← mul_one_sub]
        ring_nf

/-! ### Bernstein's inequality for derivatives -/

/-- The symbol `ξ ↦ 2πi ⟪ξ, v⟫ χ(R⁻¹ ξ)` of the derivative `∂_v` followed by the low-pass
multiplier at scale `R`. -/
private def derivSymbol {R : ℝ} (hR : R ≠ 0) (v : E) : 𝓢(E, ℂ) :=
  (2 * π * Complex.I) • SchwartzMap.smulLeftCLM ℂ (inner ℝ · v) (lowPass hR)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem derivSymbol_apply {R : ℝ} (hR : R ≠ 0) (v ξ : E) :
    derivSymbol hR v ξ = 2 * π * Complex.I * (inner ℝ ξ v * bump (E := E) (R⁻¹ • ξ) : ℝ) := by
  have : (inner ℝ · v).HasTemperateGrowth := by fun_prop
  simp [derivSymbol, SchwartzMap.smulLeftCLM_apply_apply this, lowPass_apply]

omit [CompleteSpace F] in
/-- On a tempered distribution with Fourier transform supported in the closed ball of radius `R`,
the derivative `∂_v` is the Fourier multiplier with symbol `derivSymbol`. -/
private theorem lineDerivOp_eq_fourierMultiplierCLM_derivSymbol {R : ℝ} (hR : 0 < R) (v : E)
    {u : 𝓢'(E, F)} (hu : IsVanishingOn (𝓕 u : 𝓢'(E, F)) (closedBall 0 R)ᶜ) :
    ∂_{v} u = fourierMultiplierCLM F (derivSymbol hR.ne' v) u := by
  have hι : (fun ξ ↦ (inner ℝ ξ v : ℂ)).HasTemperateGrowth := by fun_prop
  have hσ := (lowPass (E := E) hR.ne').hasTemperateGrowth
  have hsym : (derivSymbol hR.ne' v : E → ℂ) =
      (2 * π * Complex.I) • ((lowPass hR.ne' : E → ℂ) * fun ξ ↦ (inner ℝ ξ v : ℂ)) := by
    funext ξ
    simp [derivSymbol_apply, lowPass_apply, mul_comm]
  rw [hsym, fourierMultiplierCLM_smul (hσ.mul hι), smul_apply,
    ← fourierMultiplierCLM_fourierMultiplierCLM_apply hσ hι, fourierMultiplierCLM_lowPass hR hu,
    lineDeriv_eq_fourierMultiplierCLM]

/-- The kernel of `derivSymbol` at scale `R` has `L¹` norm at most `D R ‖v‖`, where `D` is the
`L¹` norm of the derivative of the low-pass kernel at scale `1`. -/
private theorem integral_norm_fourierInv_derivSymbol_le {R : ℝ} (hR : 0 < R) (v : E) :
    ∫ x, ‖𝓕⁻ (derivSymbol hR.ne' v : E → ℂ) x‖ ≤
      (∫ x, ‖fderiv ℝ (𝓕⁻ (lowPass (E := E) one_ne_zero) : 𝓢(E, ℂ)) x‖) * (R * ‖v‖) := by
  set κ : 𝓢(E, ℂ) := 𝓕⁻ (lowPass (E := E) one_ne_zero)
  -- Dilating the symbol to scale `1` turns `v` into `R • v`.
  have hdil : (derivSymbol hR.ne' v : E → ℂ) =
      fun ξ ↦ (derivSymbol (E := E) one_ne_zero (R • v) : E → ℂ) (R⁻¹ • ξ) := by
    funext ξ
    simp only [derivSymbol_apply, inv_one, one_smul, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real]
    rw [mul_inv_cancel_left₀ hR.ne']
  -- At scale `1` the kernel of `derivSymbol` is the derivative `∂_w κ`.
  have hker (w : E) : 𝓕⁻ (derivSymbol (E := E) one_ne_zero w : E → ℂ) = ⇑(∂_{w} κ : 𝓢(E, ℂ)) := by
    rw [← SchwartzMap.fourierInv_coe, derivSymbol, SchwartzMap.lineDerivOp_fourierInv_eq]
  rw [hdil, TauCeti.integral_norm_fourierInv_comp_smul _ (inv_ne_zero hR.ne'), hker,
    ← norm_smul_of_nonneg hR.le, ← integral_mul_const]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ((SchwartzMap.fderivCLM ℝ E ℂ κ).integrable.norm.mul_const _)
    (Eventually.of_forall fun x ↦ ?_)
  simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using (fderiv ℝ κ x).le_opNorm (R • v)

/-- **Bernstein's inequality for one derivative.** There is `C`, independent of `p`, `R`, `f` and
`v`, such that for `1 ≤ p ≤ ∞` and `f ∈ Lᵖ` with Fourier transform supported in the closed ball of
radius `R > 0`, `∂_v f ∈ Lᵖ` with `‖∂_v f‖_p ≤ C R ‖v‖ ‖f‖_p`. -/
private theorem exists_lineDerivOp_eq_and_norm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ}, 0 < R →
      ∀ (f : Lp F p (volume : Measure E)) (v : E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ →
      ∃ g : Lp F p (volume : Measure E), ∂_{v} (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ C * R * ‖v‖ * ‖f‖ := by
  refine ⟨∫ x, ‖fderiv ℝ (𝓕⁻ (lowPass (E := E) one_ne_zero) : 𝓢(E, ℂ)) x‖,
    integral_nonneg fun _ ↦ norm_nonneg _, fun {p} _ {R} hR f v hf ↦ ?_⟩
  obtain ⟨g, hg, hgf⟩ := exists_fourierMultiplierCLM_eq_and_norm_le (derivSymbol hR.ne' v) f
  refine ⟨g, by rw [lineDerivOp_eq_fourierMultiplierCLM_derivSymbol hR v hf, hg], hgf.trans ?_⟩
  exact (mul_le_mul_of_nonneg_right (integral_norm_fourierInv_derivSymbol_le hR v)
    (norm_nonneg f)).trans_eq (by ring)

/-- **Bernstein's inequality for `k` derivatives.** There is `C`, independent of `p`, `R`, `f` and
the directions `m`, such that for `1 ≤ p ≤ ∞` and `f ∈ Lᵖ` with Fourier transform supported in
the closed ball of radius `R > 0`, `‖∂_{m 0} ⋯ ∂_{m (k-1)} f‖_p ≤ C R ^ k ∏ ‖m i‖ ‖f‖_p`. -/
private theorem exists_iteratedLineDerivOp_eq_and_norm_le (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ}, 0 < R →
      ∀ (f : Lp F p (volume : Measure E)) (m : Fin k → E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ →
      ∃ g : Lp F p (volume : Measure E), ∂^{m} (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ C * R ^ k * (∏ i, ‖m i‖) * ‖f‖ := by
  obtain ⟨C, hC, hCf⟩ := exists_lineDerivOp_eq_and_norm_le (E := E) (F := F)
  refine ⟨C ^ k, by positivity, fun {p} _ {R} hR f ↦ ?_⟩
  induction k with
  | zero => exact fun m _ ↦ ⟨f, LineDeriv.iteratedLineDerivOp_fin_zero m _, by simp⟩
  | succ k ih =>
    intro m hf
    obtain ⟨g₁, hg₁, hb₁⟩ := ih (Fin.tail m) hf
    have hf₁ : IsVanishingOn (𝓕 (g₁ : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ :=
      hg₁ ▸ isVanishingOn_fourier_iteratedLineDerivOp hf (Fin.tail m)
    obtain ⟨g₂, hg₂, hb₂⟩ := hCf hR g₁ (m 0) hf₁
    refine ⟨g₂, by rw [LineDeriv.iteratedLineDerivOp_succ_left, hg₁, hg₂], hb₂.trans ?_⟩
    calc C * R * ‖m 0‖ * ‖g₁‖
        ≤ C * R * ‖m 0‖ * (C ^ k * R ^ k * (∏ i, ‖Fin.tail m i‖) * ‖f‖) := by gcongr
      _ = C ^ (k + 1) * R ^ (k + 1) * (∏ i, ‖m i‖) * ‖f‖ := by
        rw [Fin.prod_univ_succ]
        simp only [Fin.tail]
        ring

/-- **Bernstein's inequality.** For `1 ≤ p ≤ q ≤ ∞` and `k : ℕ` there is `C`, independent of `R`,
`f` and the directions, such that for every `f ∈ Lᵖ` whose Fourier transform is supported in the
closed ball of radius `R > 0` and all directions `m 0, …, m (k-1)`, the derivative
`∂_{m 0} ⋯ ∂_{m (k-1)} f` lies in `L^q` with

`‖∂_{m 0} ⋯ ∂_{m (k-1)} f‖_q ≤ C R ^ (k + n (1 / p - 1 / q)) ∏ ‖m i‖ ‖f‖_p`

in dimension `n`.

The exponents `1 / p` and `1 / q` are written `p.toReal⁻¹` and `q.toReal⁻¹`, which read as `0` at
`∞`. -/
theorem exists_iteratedLineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ}, 0 < R → ∀ (f : Lp F p (volume : Measure E)) (m : Fin k → E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ →
      ∃ g : Lp F q (volume : Measure E), ∂^{m} (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ C * R ^ (k + finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹)) * (∏ i, ‖m i‖) * ‖f‖ := by
  obtain ⟨C₁, hC₁, hC₁f⟩ := exists_iteratedLineDerivOp_eq_and_norm_le (E := E) (F := F) k
  obtain ⟨C₂, hC₂, hC₂f⟩ :=
    exists_eq_and_norm_le_of_isVanishingOn_fourier (E := E) (F := F) hpq
  refine ⟨C₂ * C₁, by positivity, fun {R} hR f m hf ↦ ?_⟩
  obtain ⟨g₁, hg₁, hb₁⟩ := hC₁f hR f m hf
  obtain ⟨g₂, hg₂, hb₂⟩ := hC₂f hR g₁ (hg₁ ▸ isVanishingOn_fourier_iteratedLineDerivOp hf m)
  refine ⟨g₂, hg₁.trans hg₂, hb₂.trans ?_⟩
  rw [Real.rpow_add hR, Real.rpow_natCast]
  calc C₂ * R ^ (finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹)) * ‖g₁‖
      ≤ C₂ * R ^ (finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹)) *
          (C₁ * R ^ k * (∏ i, ‖m i‖) * ‖f‖) := by gcongr
    _ = _ := by ring

end TemperedDistribution

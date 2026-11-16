/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Distribution.Support
import TauCeti.Analysis.Convolution.Young
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier

/-!
# Fourier multipliers with integrable kernels on `Lᵖ` functions

Let `σ` be a Schwartz function on a finite-dimensional real inner product space `E`. The Fourier
multiplier `T_σ u = 𝓕⁻ (σ • 𝓕 u)` on tempered distributions
(`TemperedDistribution.fourierMultiplierCLM`) acts on the tempered distribution of an `Lᵖ`
function `f`, for any `1 ≤ p ≤ ∞`, as convolution with the Schwartz kernel `𝓕⁻ σ`:

`T_σ f = 𝓕⁻ σ ⋆ f`, where `(𝓕⁻ σ ⋆ f) x = ∫ y, 𝓕⁻ σ (x - y) • f y`.

Together with Young's convolution inequality this shows that `T_σ` maps `Lᵖ` to `Lᵠ` for every
`q ≥ p`, with `‖T_σ f‖_q ≤ ‖𝓕⁻ σ‖_r ‖f‖_p` whenever `1/p + 1/r = 1 + 1/q`.

More generally, the same holds for a symbol `g` of temperate growth which is the Fourier
transform `𝓕 K` of an integrable kernel `K`, not necessarily smooth or rapidly decreasing:
`T_g f = K ⋆ f`. The Bessel potentials `J^{-δ}`, whose kernels are singular at the origin, are of
this kind.

The identity is proved by pairing with a test function `φ`: by definition
`T_g f (φ) = ∫ 𝓕 (g • 𝓕⁻ φ) • f`, the convolution theorem writes
`𝓕 (g • 𝓕⁻ φ) y = ∫ x, K (x - y) * φ x`, and Fubini's theorem exchanges the two integrals. The
double integral converges absolutely by Hölder's inequality in `y` and Young's inequality for the
inner integral, so no restriction on `p` is needed. This covers `p = ∞`, where the Schwartz
functions are not dense and the multiplier cannot be obtained by extension from them. For
`p = 2` the same kernel represents the `L²` multiplier `MeasureTheory.Lp.fourierMultiplierCLM`
(`SchwartzMap.coeFn_fourierMultiplierCLM_toLp`).

This is the form in which frequency-localized functions are handled: a function whose Fourier
transform is supported in a ball is reproduced by a multiplier whose symbol is a bump function
equal to one on that ball, so that it is a convolution with a fixed Schwartz kernel
(`TemperedDistribution.ae_eq_fourierInv_convolution_of_isVanishingOn`). Bernstein's inequalities
are derived this way.

## Main declarations

* `TemperedDistribution.fourierMultiplierCLM_toTemperedDistribution_apply_of_fourier_eq`: for an
  integrable kernel `K` with `𝓕 K = g`, the pairing of `T_g f` with a test function is the pairing
  of the convolution `K ⋆ f`.
* `TemperedDistribution.fourier_smulLeftCLM_fourierInv_apply`: the convolution theorem
  `𝓕 (𝓕 K • 𝓕⁻ φ) y = ∫ x, K (x - y) * φ x` against a test function `φ`.
* `TemperedDistribution.integrable_uncurry_sub_mul_smul`: the absolute convergence of the double
  integral of the pairing.
* `TemperedDistribution.fourierMultiplierCLM_toTemperedDistribution_apply`: the pairing of `T_σ f`
  with a test function is the pairing of the convolution `𝓕⁻ σ ⋆ f`.
* `TemperedDistribution.exists_fourierMultiplierCLM_toTemperedDistribution_eq`: `T_σ f` is the
  `Lᵠ` function `𝓕⁻ σ ⋆ f`, with `‖T_σ f‖_q ≤ ‖𝓕⁻ σ‖_r ‖f‖_p`.
* `TemperedDistribution.exists_fourierMultiplierCLM_eq_and_norm_le`: the case `q = p`, `r = 1`,
  `‖T_σ f‖_p ≤ ‖𝓕⁻ σ‖₁ ‖f‖_p`.
* `TemperedDistribution.ae_eq_fourierInv_convolution_of_fourierMultiplierCLM_eq`: an `Lᵠ`
  function representing `T_σ f` is almost everywhere the convolution `𝓕⁻ σ ⋆ f`.
* `TemperedDistribution.ae_eq_fourierInv_convolution_of_isVanishingOn`: the reproducing formula
  `f = 𝓕⁻ σ ⋆ f` when `σ` equals one near the spectrum of `f`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Sections 2.3 and 2.5.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.1.
-/

public section

noncomputable section

namespace TemperedDistribution

open MeasureTheory SchwartzMap ContinuousLinearMap
open scoped ENNReal FourierTransform SchwartzMap Convolution RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

omit [CompleteSpace F] in
/-- For an integrable kernel `K`, a test function `φ` and `f ∈ Lᵖ`, `1 ≤ p ≤ ∞`, the function
`(y, x) ↦ (K (y - x) * φ x) • f y` is integrable on `E × E`: its integral in `x` is `‖f y‖` times
the convolution of `‖φ‖` with `‖K‖`, which lies in the conjugate space of `Lᵖ` by Young's
inequality. -/
theorem integrable_uncurry_sub_mul_smul {K : E → ℂ} (hK : Integrable K) (φ : 𝓢(E, ℂ))
    (f : Lp F p (volume : Measure E)) :
    Integrable (Function.uncurry fun y x ↦ (K (y - x) * φ x) • f y)
      ((volume : Measure E).prod volume) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun y x ↦ (K (y - x) * φ x) • f y)
      ((volume : Measure E).prod volume) :=
    ((hK.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)).mul
      (φ.continuous.comp continuous_snd).aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable f).comp_fst
  refine ⟨hmeas, ?_⟩
  set H : E → ℝ≥0∞ := (fun x ↦ ‖φ x‖ₑ) ⋆ₗ[volume] fun x ↦ ‖K x‖ₑ
  have hinner : ∀ y, ∫⁻ x, ‖(K (y - x) * φ x) • f y‖ₑ = ‖f y‖ₑ * H y := fun y ↦ by
    simp only [H, lconvolution_def]
    rw [← lintegral_const_mul' _ _ eNorm_ne_top]
    refine lintegral_congr fun x ↦ ?_
    rw [eNorm_smul, eNorm_mul, neg_add_eq_sub]
    ring
  rw [HasFiniteIntegral, lintegral_prod _ hmeas.eNorm]
  simp only [Function.uncurry_apply_pair, hinner]
  -- Hölder's inequality with the conjugate exponent `p'` of `p`, then Young's inequality
  -- `‖H‖_{p'} ≤ ‖φ‖_{p'} ‖K‖_1`.
  set p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  have hpp' : p.HolderConjugate p' := ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  have hp' : 1 ≤ p' := ENNReal.one_le_inv.2 tsub_le_self
  have hHm : AEMeasurable H volume :=
    aemeasurable_lconvolution φ.continuous.eNorm.aemeasurable
      hK.aestronglyMeasurable.eNorm
  have hfH : AEStronglyMeasurable (fun y ↦ ‖f y‖ₑ * H y) volume :=
    ((Lp.aestronglyMeasurable f).eNorm.mul hHm).aestronglyMeasurable
  calc ∫⁻ y, ‖f y‖ₑ * H y
      = eLpNorm (fun y ↦ ‖f y‖ₑ * H y) 1 volume := by
        rw [eLpNorm_one_eq_lintegral_eNorm hfH]
        simp
    _ ≤ 1 * eLpNorm f p volume * eLpNorm H p' volume :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_of_eNorm (fun v h ↦ ‖v‖ₑ * h) 1
          (fun hf hH ↦ (hf.eNorm.mul hH.aemeasurable).aestronglyMeasurable)
          (Lp.aestronglyMeasurable f) hHm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun _ ↦ by simp)
    _ ≤ 1 * eLpNorm f p volume *
          (eLpNorm (fun x ↦ ‖φ x‖ₑ) p' volume * eLpNorm (fun x ↦ ‖K x‖ₑ) 1 volume) := by
        gcongr
        exact eLpNorm_lconvolution_le hp' le_rfl (by rw [inv_one, add_comm])
          φ.continuous.eNorm.aemeasurable hK.aestronglyMeasurable.eNorm
    _ < ∞ := by
        rw [eLpNorm_eNorm _ φ.continuous.aestronglyMeasurable,
          eLpNorm_eNorm _ hK.aestronglyMeasurable, one_mul]
        exact ENNReal.mul_lt_top (Lp.eLpNorm_lt_top f)
          (ENNReal.mul_lt_top (φ.eLpNorm_lt_top p' volume)
            (memLp_one_iff_integrable.2 hK).eLpNorm_lt_top)

/-- **The convolution theorem against a test function.** If the symbol `g` of temperate growth is
the Fourier transform of an integrable kernel `K`, then for every test function `φ`,
`𝓕 (g • 𝓕⁻ φ) y = ∫ x, K (x - y) * φ x`. -/
theorem fourier_smulLeftCLM_fourierInv_apply {K : E → ℂ} (hK : Integrable K) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (hgK : 𝓕 K = g) (φ : 𝓢(E, ℂ)) (y : E) :
    𝓕 (SchwartzMap.smulLeftCLM ℂ g (𝓕⁻ φ)) y = ∫ x, K (x - y) * φ x := by
  set ψ := 𝓕⁻ φ
  have hint : Integrable (Function.uncurry fun (ξ z : E) ↦
      (𝐞 (-⟪z, ξ⟫) : ℂ) * K z * ((𝐞 (-⟪ξ, y⟫) : ℂ) * ψ ξ)) (volume.prod volume) := by
    refine (ψ.integrable.mul_prod hK).mono ?_ (.of_forall fun q ↦ ?_)
    · exact (((by fun_prop : Continuous fun q : E × E ↦ (𝐞 (-⟪q.2, q.1⟫) : ℂ)
        ).aestronglyMeasurable.mul hK.aestronglyMeasurable.comp_snd).mul
        ((by fun_prop : Continuous fun q : E × E ↦ (𝐞 (-⟪q.1, y⟫) : ℂ)).mul
          (ψ.continuous.comp continuous_fst)).aestronglyMeasurable)
    · simp [Function.uncurry, mul_comm]
  -- The exponentials combine into the character at `y + z`.
  have hexp : ∀ z ξ : E, (𝐞 (-⟪z, ξ⟫) : ℂ) * K z * ((𝐞 (-⟪ξ, y⟫) : ℂ) * ψ ξ) =
      K z * (𝐞 (-⟪ξ, y + z⟫) • ψ ξ) := fun z ξ ↦ by
    rw [Circle.smul_def, inner_add_right, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul,
      real_inner_comm ξ z]
    ring
  calc 𝓕 (SchwartzMap.smulLeftCLM ℂ g ψ) y
      = ∫ ξ, ∫ z, (𝐞 (-⟪z, ξ⟫) : ℂ) * K z * ((𝐞 (-⟪ξ, y⟫) : ℂ) * ψ ξ) := by
        rw [SchwartzMap.fourier_coe, Real.fourier_eq]
        refine integral_congr_ae (.of_forall fun ξ ↦ ?_)
        dsimp only
        rw [SchwartzMap.smulLeftCLM_apply_apply hg, ← hgK, Real.fourier_eq, integral_mul_const]
        simp_rw [Circle.smul_def, smul_eq_mul]
        ring
    _ = ∫ z, ∫ ξ, (𝐞 (-⟪z, ξ⟫) : ℂ) * K z * ((𝐞 (-⟪ξ, y⟫) : ℂ) * ψ ξ) :=
        integral_integral_swap hint
    _ = ∫ z, K z * φ (y + z) := by
        refine integral_congr_ae (.of_forall fun z ↦ ?_)
        simp_rw [hexp, integral_const_mul, ← Real.fourier_eq, ← SchwartzMap.fourier_coe, ψ,
          FourierTransform.fourier_fourierInv_eq]
    _ = ∫ x, K (x - y) * φ x := by
        rw [← integral_sub_right_eq_self (fun z ↦ K z * φ (y + z)) y]
        simp only [add_sub_cancel]

/-- **A Fourier multiplier whose symbol is the Fourier transform of an integrable kernel acts on
`Lᵖ` by convolution.** If the symbol `g` of temperate growth is `𝓕 K` for an integrable kernel
`K`, then for `f ∈ Lᵖ`, `1 ≤ p ≤ ∞`, the tempered distribution `T_g f = 𝓕⁻ (g • 𝓕 f)` pairs with
every test function `φ` as the convolution `K ⋆ f` does. -/
theorem fourierMultiplierCLM_toTemperedDistribution_apply_of_fourier_eq {K : E → ℂ}
    (hK : Integrable K) {g : E → ℂ} (hg : g.HasTemperateGrowth) (hgK : 𝓕 K = g)
    (f : Lp F p (volume : Measure E)) (φ : 𝓢(E, ℂ)) :
    fourierMultiplierCLM F g (f : 𝓢'(E, F)) φ =
      ∫ x, φ x • (K ⋆[lsmul ℂ ℂ] (f : E → F)) x := by
  rw [fourierMultiplierCLM_apply_apply, Lp.toTemperedDistribution_apply]
  have hconv : ∀ x, (K ⋆[lsmul ℂ ℂ] (f : E → F)) x = ∫ y, K (x - y) • f y := fun x ↦ by
    rw [convolution_eq_swap]
    rfl
  simp_rw [fourier_smulLeftCLM_fourierInv_apply hK hg hgK, hconv]
  calc ∫ y, (∫ x, K (x - y) * φ x) • f y
      = ∫ y, ∫ x, (K (x - y) * φ x) • f y := by
        simp_rw [integral_smul_const]
    _ = ∫ x, ∫ y, (K (x - y) * φ x) • f y := by
        refine integral_integral_swap ?_
        simpa only [neg_sub] using integrable_uncurry_sub_mul_smul (K := fun z ↦ K (-z))
          (hK.comp_neg) φ f
    _ = ∫ x, φ x • ∫ y, K (x - y) • f y := by
        simp_rw [← integral_smul, mul_comm (K _), mul_smul]

/-- **A Fourier multiplier with a Schwartz symbol acts on `Lᵖ` by convolution.** For a Schwartz
symbol `σ` and `f ∈ Lᵖ`, `1 ≤ p ≤ ∞`, the tempered distribution `T_σ f = 𝓕⁻ (σ • 𝓕 f)` pairs with
every test function `φ` as the convolution `𝓕⁻ σ ⋆ f` does. -/
theorem fourierMultiplierCLM_toTemperedDistribution_apply (σ : 𝓢(E, ℂ))
    (f : Lp F p (volume : Measure E)) (φ : 𝓢(E, ℂ)) :
    fourierMultiplierCLM F σ (f : 𝓢'(E, F)) φ =
      ∫ x, φ x • (𝓕⁻ (σ : E → ℂ) ⋆[lsmul ℂ ℂ] (f : E → F)) x := by
  rw [← SchwartzMap.fourierInv_coe]
  refine fourierMultiplierCLM_toTemperedDistribution_apply_of_fourier_eq (𝓕⁻ σ).integrable
    σ.hasTemperateGrowth ?_ f φ
  rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]

/-- **A Fourier multiplier with a Schwartz symbol maps `Lᵖ` to `Lᵠ`.** For a Schwartz symbol `σ`,
`f ∈ Lᵖ` and exponents with `1 ≤ r` and `1/p + 1/r = 1 + 1/q`, the tempered distribution
`T_σ f = 𝓕⁻ (σ • 𝓕 f)` is the `Lᵠ` function `𝓕⁻ σ ⋆ f`, and
`‖T_σ f‖_q ≤ ‖𝓕⁻ σ‖_r ‖f‖_p`. -/
theorem exists_fourierMultiplierCLM_toTemperedDistribution_eq (σ : 𝓢(E, ℂ))
    (f : Lp F p (volume : Measure E)) {q r : ℝ≥0∞} [Fact (1 ≤ q)] (hr : 1 ≤ r)
    (hpqr : p⁻¹ + r⁻¹ = 1 + q⁻¹) :
    ∃ g : Lp F q (volume : Measure E),
      fourierMultiplierCLM F σ (f : 𝓢'(E, F)) = g ∧
      g =ᵐ[volume] 𝓕⁻ (σ : E → ℂ) ⋆[lsmul ℂ ℂ] (f : E → F) ∧
      ‖g‖ ≤ (eLpNorm (𝓕⁻ (σ : E → ℂ)) r volume).toReal * ‖f‖ := by
  -- Work with the Schwartz kernel `𝓕⁻ σ`, which is continuous and lies in every `Lʳ`.
  rw [← SchwartzMap.fourierInv_coe]
  set K : 𝓢(E, ℂ) := 𝓕⁻ σ
  set h := (K : E → ℂ) ⋆[lsmul ℂ ℂ] (f : E → F)
  have hL : ‖lsmul ℂ ℂ (E := F)‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 opNorm_lsmul_le
  have hbound : eLpNorm h q volume ≤ eLpNorm K r volume * eLpNorm f p volume :=
    calc eLpNorm h q volume
        ≤ ‖lsmul ℂ ℂ (E := F)‖ₑ * eLpNorm K r volume * eLpNorm f p volume :=
          eLpNorm_convolution_le_of_inv_add_inv_eq _ hr hp.out (by rw [add_comm, hpqr])
            K.continuous.aestronglyMeasurable (Lp.aestronglyMeasurable f)
      _ ≤ eLpNorm K r volume * eLpNorm f p volume := by
          rw [mul_assoc]
          exact mul_le_of_le_one_left (zero_le) hL
  have hfin : eLpNorm K r volume * eLpNorm f p volume ≠ ∞ :=
    ENNReal.mul_ne_top (K.eLpNorm_lt_top r volume).ne (Lp.eLpNorm_lt_top f).ne
  have hmem : MemLp h q volume := memLp_iff.2 (lt_of_le_of_lt hbound (Ne.lt_top hfin))
  refine ⟨hmem.toLp h, ?_, hmem.coeFn_toLp, ?_⟩
  · ext φ
    rw [fourierMultiplierCLM_toTemperedDistribution_apply, Lp.toTemperedDistribution_apply,
      ← SchwartzMap.fourierInv_coe]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [hx]
  · rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono hfin hbound

/-- **`Lᵖ` bound for a multiplier with Schwartz symbol.** For `1 ≤ p ≤ ∞`, the Fourier multiplier
with a Schwartz symbol `σ` maps every `f ∈ Lᵖ` to a function `g ∈ Lᵖ` with
`‖g‖_p ≤ ‖𝓕⁻ σ‖₁ ‖f‖_p`. This is the case `q = p`, `r = 1` of
`TemperedDistribution.exists_fourierMultiplierCLM_toTemperedDistribution_eq`. -/
theorem exists_fourierMultiplierCLM_eq_and_norm_le (σ : 𝓢(E, ℂ))
    (f : Lp F p (volume : Measure E)) :
    ∃ g : Lp F p (volume : Measure E), fourierMultiplierCLM F σ (f : 𝓢'(E, F)) = g ∧
      ‖g‖ ≤ (∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖) * ‖f‖ := by
  obtain ⟨g, hg, -, hgf⟩ :=
    exists_fourierMultiplierCLM_toTemperedDistribution_eq σ f (q := p) (r := 1) le_rfl
      (by rw [inv_one, add_comm])
  have hK : AEStronglyMeasurable (𝓕⁻ (σ : E → ℂ)) volume := by
    rw [← SchwartzMap.fourierInv_coe]
    exact (𝓕⁻ σ).continuous.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_eNorm hK, ← integral_norm_eq_lintegral_eNorm hK] at hgf
  exact ⟨g, hg, hgf⟩

/-- **A Fourier multiplier of an `Lᵖ` function that is an `Lᵠ` function is a convolution.** For a
Schwartz symbol `σ` and `f ∈ Lᵖ`, `1 ≤ p ≤ ∞`, if the tempered distribution `T_σ f` is the
`Lᵠ` function `g`, `1 ≤ q ≤ ∞`, then `g` agrees almost everywhere with the convolution
`𝓕⁻ σ ⋆ f`. -/
theorem ae_eq_fourierInv_convolution_of_fourierMultiplierCLM_eq {σ : 𝓢(E, ℂ)}
    {f : Lp F p (volume : Measure E)} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {g : Lp F q (volume : Measure E)} (h : fourierMultiplierCLM F σ (f : 𝓢'(E, F)) = g) :
    g =ᵐ[volume] 𝓕⁻ (σ : E → ℂ) ⋆[lsmul ℂ ℂ] (f : E → F) := by
  obtain ⟨g', hg', hg'c, -⟩ :=
    exists_fourierMultiplierCLM_toTemperedDistribution_eq σ f (q := p) le_rfl
      (by rw [inv_one, add_comm])
  refine (Lp.ae_eq_of_toTemperedDistribution_apply_eq g
    ((Lp.memLp g').locallyIntegrable hp.out) fun φ ↦ ?_).trans hg'c
  rw [← h, hg', Lp.toTemperedDistribution_apply]

/-- **The reproducing formula for frequency-localized functions.** If the Fourier transform of
`f ∈ Lᵖ`, `1 ≤ p ≤ ∞`, vanishes on `s`, and the Schwartz symbol `σ` equals one outside a closed
subset of `s` (that is, `tsupport (σ - 1) ⊆ s`), then `f` agrees almost everywhere with its
convolution with the kernel `𝓕⁻ σ`. -/
theorem ae_eq_fourierInv_convolution_of_isVanishingOn {f : Lp F p (volume : Measure E)}
    {s : Set E} (hf : Distribution.IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) s)
    {σ : 𝓢(E, ℂ)} (hσ : tsupport (⇑σ - 1) ⊆ s) :
    f =ᵐ[volume] 𝓕⁻ (σ : E → ℂ) ⋆[lsmul ℂ ℂ] (f : E → F) :=
  ae_eq_fourierInv_convolution_of_fourierMultiplierCLM_eq
    (fourierMultiplierCLM_eq_self_of_isVanishingOn hf σ.hasTemperateGrowth hσ)

end TemperedDistribution

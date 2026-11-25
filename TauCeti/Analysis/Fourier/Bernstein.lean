/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Analysis.Fourier.ChangeOfVariables

/-!
# Bernstein's inequality for dyadic `L²` Fourier multipliers

Let `V` be a real inner product space of finite dimension `n` and let `σ` be a Schwartz symbol.
The `L²` Fourier multiplier `T_σ` with symbol `σ` is convolution with the Schwartz kernel `𝓕⁻ σ`
(`SchwartzMap.coeFn_fourierMultiplierCLM_toLp`), so Young's inequality bounds it from `Lᵖ` to
`L^q` for `1 ≤ p ≤ q ≤ ∞`:

`‖T_σ f‖_q ≤ ‖𝓕⁻ σ‖_c ‖f‖_p`, `1/c + 1/p = 1 + 1/q`,

for every `f ∈ L²` (`SchwartzMap.eLpNorm_fourierMultiplierCLM_toLp_le_of_inv_add_inv_eq`, in
`TauCeti.Analysis.Fourier.L2Multiplier`). For the
dyadic multipliers `Mⱼ` of `ContDiffBump.dyadicMultiplier`, whose symbols are the dilates
`σ₀ (2^{-j} ·)` of one Schwartz function, the kernels are the `L¹`-normalized dilates
`2^{jn} 𝓕⁻ σ₀ (2^j ·)`, whose `L^c` norms grow like `2^{jn (1 - 1/c)}`. This gives
**Bernstein's inequality** for dyadic multipliers
(`ContDiffBump.eLpNorm_dyadicMultiplier_le_of_le`):

`‖Mⱼ f‖_q ≤ 2^{jn (1/p - 1/q)} ‖𝓕⁻ σ₀‖_c ‖f‖_p`.

Some dyadic multiplier `Qⱼ` reproduces the homogeneous Littlewood–Paley blocks, `Pⱼ Qⱼ = Pⱼ`
(`ContDiffBump.exists_fourierMultiplierCLM_dyadicMultiplier_eq`): its symbols equal one on the
support of `ψⱼ`. So the `L²` image of `Pⱼ` gains integrability at the cost `2^{jn (1/p - 1/q)}`,
uniformly in `j`. This is how estimates for frequency-localized operators are moved from one
Lebesgue exponent to a larger one, as for the Strichartz estimates of the wave equation at the
pairs `(2, r)` beyond the endpoint exponent.

These are the `L²`-multiplier counterparts of the band-limited Bernstein inequality for tempered
distributions, `TauCeti.exists_eq_and_norm_le_of_isVanishingOn_fourier`, and of the periodic one,
`TauCeti.UnitAddTorus.exists_eLpNorm_le_of_mFourierCoeff_eq_zero_of_lt_norm`.

## References

* H. Bahouri, J.-Y. Chemin, R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, Lemma 2.1.
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace ContDiffBump

variable (φ : ContDiffBump (0 : V))

/-- **Bernstein's inequality for dyadic multipliers.** For `1 ≤ p ≤ q ≤ ∞`, every `j ∈ ℤ` and
every `f ∈ L²(V, F)`,

`‖Mⱼ f‖_q ≤ 2^{jn (1/p - 1/q)} ‖𝓕⁻ σ₀‖_c ‖f‖_p`, `1/c = 1 + 1/q - 1/p`,

where `n` is the dimension of `V`, `Mⱼ` is the multiplier whose symbol is the `j`-th dyadic dilate
`σⱼ` of the Schwartz function `σ`, and `1/∞ = 0`: the kernel `𝓕⁻ σⱼ` has `L^c` norm
`2^{jn (1 - 1/c)} ‖𝓕⁻ σ₀‖_c`. For `p = q` this is `ContDiffBump.eLpNorm_dyadicMultiplier_le`. -/
theorem eLpNorm_dyadicMultiplier_le_of_le (σ : 𝓢(V, ℂ)) (j : ℤ) (f : Lp F 2 (volume : Measure V))
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) :
    eLpNorm (φ.dyadicMultiplier F σ j f) q volume ≤
      ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ V : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹))) *
        eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate σ 0)) (1 + q⁻¹ - p⁻¹)⁻¹ volume * eLpNorm f p volume := by
  -- The exponent `c` of Young's inequality, with `1/c + 1/p = 1 + 1/q`.
  set c : ℝ≥0∞ := (1 + q⁻¹ - p⁻¹)⁻¹
  have hqp : q⁻¹ ≤ p⁻¹ := ENNReal.inv_le_inv.2 hpq
  have hp1 : p⁻¹ ≤ 1 + q⁻¹ := (ENNReal.inv_le_one.2 hp).trans le_self_add
  have hq1 : q⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (one_pos.trans_le (hp.trans hpq)).ne'
  have hc : 1 ≤ c := ENNReal.one_le_inv.2 (tsub_le_iff_right.2 (by gcongr))
  have hcpq : c⁻¹ + p⁻¹ = 1 + q⁻¹ := by rw [inv_inv, tsub_add_cancel_of_le hp1]
  have hcexp : (Module.finrank ℝ V : ℝ) - Module.finrank ℝ V / c.toReal =
      Module.finrank ℝ V * (p.toReal⁻¹ - q.toReal⁻¹) := by
    rw [div_eq_mul_inv, ← ENNReal.toReal_inv, inv_inv,
      ENNReal.toReal_sub_of_le hp1 (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hq1⟩),
      ENNReal.toReal_add ENNReal.one_ne_top hq1, ENNReal.toReal_inv, ENNReal.toReal_inv,
      ENNReal.toReal_one]
    ring
  -- The kernel of `Mⱼ` is the `L¹`-normalized dilate of that of `M₀`.
  have hdil : ⇑(φ.dyadicDilate σ j) = fun ξ ↦ (⇑(φ.dyadicDilate σ 0)) (((2 : ℝ) ^ j)⁻¹ • ξ) :=
    funext (φ.dyadicDilate_apply_eq_dyadicDilate_zero_apply σ j)
  rw [dyadicMultiplier_def, ← hcexp]
  refine ((φ.dyadicDilate σ j).eLpNorm_fourierMultiplierCLM_toLp_le_of_inv_add_inv_eq f hc hp
    hcpq).trans_eq ?_
  rw [hdil, TauCeti.eLpNorm_fourierInv_comp_inv_smul _ (zpow_pos two_pos j)]

/-- **A dyadic multiplier reproducing the Littlewood–Paley blocks.** There is a Schwartz function
`σ` whose dyadic multipliers `Qⱼ` satisfy `Pⱼ Qⱼ f = Pⱼ f` for every `j ∈ ℤ` and every
`f ∈ L²(V, F)`, where `Pⱼ` is the `L²` Fourier multiplier with any symbol in `L^∞` almost
everywhere equal to `ψⱼ`: the dyadic dilates of `σ` equal one on the support of `ψⱼ`. With
`ContDiffBump.eLpNorm_dyadicMultiplier_le_of_le`, this bounds the higher Lebesgue norms of a block
`Pⱼ f` by its lower ones. -/
theorem exists_fourierMultiplierCLM_dyadicMultiplier_eq :
    ∃ σ : 𝓢(V, ℂ), ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure V)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ f : Lp F 2 (volume : Measure V),
        Lp.fourierMultiplierCLM F m (φ.dyadicMultiplier F σ j f) =
          Lp.fourierMultiplierCLM F m f := by
  obtain ⟨σ, hσ⟩ := φ.exists_eqOn_inv_of_contDiffOn (a := fun _ ↦ 1) contDiffOn_const
    fun _ _ ↦ one_ne_zero
  refine ⟨σ, fun j m hm f ↦ ?_⟩
  -- As symbols in `L^∞`, `ψⱼ σⱼ = ψⱼ`, since `σⱼ = 1` where `ψⱼ ≠ 0`.
  have hsym : (m • (φ.dyadicDilate σ j).toLp ∞ : Lp ℂ ∞ (volume : Measure V)) = m := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_lpSMul (r := ∞) m ((φ.dyadicDilate σ j).toLp ∞),
      (φ.dyadicDilate σ j).coeFn_toLp ∞ volume, hm] with ξ hξ hσξ hmξ
    rw [hξ, Pi.smul_apply', hσξ, hmξ, smul_eq_mul]
    by_cases h : φ.littlewoodPaley j ξ = 0
    · rw [h, Complex.ofReal_zero, zero_mul]
    · rw [φ.dyadicDilate_apply_of_littlewoodPaley_ne_zero (a := fun _ ↦ 1) hσ h, inv_one,
        Complex.ofReal_one, mul_one]
  rw [dyadicMultiplier_def, Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply, hsym]

end ContDiffBump

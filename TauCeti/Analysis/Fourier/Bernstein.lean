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
uniformly in `j`: `‖Pⱼ f‖_q ≤ C 2^{jn (1/p - 1/q)} ‖Pⱼ f‖_p`
(`ContDiffBump.exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le`). With the uniform `Lᵖ`
bound of the blocks this gives `‖Pⱼ f‖_q ≤ C 2^{jn (1/p - 1/q)} ‖f‖_p`
(`ContDiffBump.exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le_eLpNorm`), and in particular
`‖Pⱼ f‖_r ≤ C 2^{j (n/2 - n/r)} ‖f‖₂` for `r ≥ 2`
(`ContDiffBump.exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le_of_two_le`). This is how
estimates for frequency-localized operators are moved from one Lebesgue exponent to a larger one,
as for the Strichartz estimates of the wave equation at the pairs `(2, r)` beyond the endpoint
exponent. It also makes `a ↦ Pⱼ y(a)` continuous into `L^r`, `r ≥ 2`, for every continuous
`y : α → L²` (`ContDiffBump.tendsto_eLpNorm_fourierMultiplierCLM_littlewoodPaley_sub`).

These are the `L²`-multiplier counterparts of the band-limited Bernstein inequality for tempered
distributions, `TauCeti.exists_eq_and_norm_le_of_isVanishingOn_fourier`, and of the periodic one,
`TauCeti.UnitAddTorus.exists_eLpNorm_le_of_mFourierCoeff_eq_zero_of_lt_norm`.

## References

* H. Bahouri, J.-Y. Chemin, R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, Lemma 2.1.
-/

public section

open Filter MeasureTheory Topology
open scoped ENNReal NNReal FourierTransform SchwartzMap

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

/-- **Bernstein's inequality for the Littlewood–Paley blocks.** For `1 ≤ p ≤ q ≤ ∞` there is `C`
such that for every `j ∈ ℤ` and every `f ∈ L²(V, F)`,

`‖Pⱼ f‖_q ≤ C 2^{jn (1/p - 1/q)} ‖Pⱼ f‖_p`,

where `n` is the dimension of `V` and `Pⱼ` is the `L²` Fourier multiplier with any symbol in `L^∞`
almost everywhere equal to `ψⱼ`. -/
theorem exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le {p q : ℝ≥0∞} (hp : 1 ≤ p)
    (hpq : p ≤ q) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure V)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm (Lp.fourierMultiplierCLM F m f) q volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^
            ((Module.finrank ℝ V : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹))) *
            eLpNorm (Lp.fourierMultiplierCLM F m f) p volume := by
  obtain ⟨σ, hσ⟩ := φ.exists_fourierMultiplierCLM_dyadicMultiplier_eq (F := F)
  set B := eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate σ 0)) (1 + q⁻¹ - p⁻¹)⁻¹ volume
  refine ⟨B.toNNReal, fun j m hm f ↦ ?_⟩
  -- `Qⱼ Pⱼ f = Pⱼ f`, since `Qⱼ` commutes with `Pⱼ` and `Pⱼ Qⱼ = Pⱼ`.
  have hQP : φ.dyadicMultiplier F σ j (Lp.fourierMultiplierCLM F m f) =
      Lp.fourierMultiplierCLM F m f := by
    rw [dyadicMultiplier_def, Lp.fourierMultiplierCLM_fourierMultiplierCLM_comm,
      ← dyadicMultiplier_def, hσ j m hm]
  have h := φ.eLpNorm_dyadicMultiplier_le_of_le σ j (Lp.fourierMultiplierCLM F m f) hp hpq
  rw [hQP] at h
  refine h.trans_eq ?_
  rw [ENNReal.coe_toNNReal (φ.memLp_fourierInv_dyadicDilate σ 0 _).eLpNorm_ne_top]
  ring

/-- **Bernstein's inequality from `Lᵖ` to `L^q` for the Littlewood–Paley blocks.** For
`1 ≤ p ≤ q ≤ ∞` there is `C` such that for every `j ∈ ℤ` and every `f ∈ L²(V, F)`,

`‖Pⱼ f‖_q ≤ C 2^{jn (1/p - 1/q)} ‖f‖_p`,

where `n` is the dimension of `V` and `Pⱼ` is the `L²` Fourier multiplier with any symbol in `L^∞`
almost everywhere equal to `ψⱼ`. This combines
`ContDiffBump.exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le` with the uniform `Lᵖ` bound
`ContDiffBump.eLpNorm_fourierMultiplierCLM_littlewoodPaley_le` of the blocks. -/
theorem exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le_eLpNorm {p q : ℝ≥0∞} (hp : 1 ≤ p)
    (hpq : p ≤ q) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure V)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm (Lp.fourierMultiplierCLM F m f) q volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^
            ((Module.finrank ℝ V : ℝ) * (p.toReal⁻¹ - q.toReal⁻¹))) * eLpNorm f p volume := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le (F := F) hp hpq
  set K := eLpNorm (𝓕⁻ (fun ξ ↦ (φ.littlewoodPaley 0 ξ : ℂ))) 1 volume
  refine ⟨C * K.toNNReal, fun j m hm f ↦ (hC j m hm f).trans ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (φ.memLp_fourierInv_littlewoodPaley 0 1).eLpNorm_ne_top,
    mul_right_comm _ K, mul_assoc _ K]
  gcongr
  exact φ.eLpNorm_fourierMultiplierCLM_littlewoodPaley_le hm f hp

/-- **Bernstein's inequality from `L²` for the Littlewood–Paley blocks.** For `2 ≤ r ≤ ∞` there is
`C` such that for every `j ∈ ℤ` and every `f ∈ L²(V, F)`,

`‖Pⱼ f‖_r ≤ C 2^{j (n/2 - n/r)} ‖f‖₂`,

where `n` is the dimension of `V` and `Pⱼ` is the `L²` Fourier multiplier with any symbol in `L^∞`
almost everywhere equal to `ψⱼ`. -/
theorem exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le_of_two_le {r : ℝ≥0∞} (hr : 2 ≤ r) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure V)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ f : Lp F 2 (volume : Measure V),
        eLpNorm (Lp.fourierMultiplierCLM F m f) r volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^
            ((Module.finrank ℝ V : ℝ) / 2 - Module.finrank ℝ V * (r⁻¹).toReal)) * ‖f‖ₑ := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le_eLpNorm (F := F)
    one_le_two hr
  refine ⟨C, fun j m hm f ↦ (hC j m hm f).trans_eq ?_⟩
  have hexp : (Module.finrank ℝ V : ℝ) * ((2 : ℝ≥0∞).toReal⁻¹ - r.toReal⁻¹) =
      (Module.finrank ℝ V : ℝ) / 2 - Module.finrank ℝ V * (r⁻¹).toReal := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    ring
  rw [hexp, Lp.eNorm_def]

/-- **Continuity of the Littlewood–Paley blocks into `L^r`.** Let `2 ≤ r ≤ ∞`. If `y : α → L²(V, F)`
is continuous, then so is `a ↦ Pⱼ y(a)` for the `L^r` distance:
`‖Pⱼ y(a) - Pⱼ y(a₀)‖_r → 0` as `a → a₀`. -/
theorem tendsto_eLpNorm_fourierMultiplierCLM_littlewoodPaley_sub {α : Type*} [TopologicalSpace α]
    {r : ℝ≥0∞} (hr : 2 ≤ r) {j : ℤ} {m : Lp ℂ ∞ (volume : Measure V)}
    (hm : m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))) {y : α → Lp F 2 (volume : Measure V)}
    (hy : Continuous y) (a₀ : α) :
    Tendsto (fun a ↦ eLpNorm (⇑(Lp.fourierMultiplierCLM F m (y a)) -
      ⇑(Lp.fourierMultiplierCLM F m (y a₀))) r volume) (𝓝 a₀) (𝓝 0) := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le_of_two_le (F := F) hr
  have h : Tendsto (fun a ↦ ‖y a - y a₀‖ₑ) (𝓝 a₀) (𝓝 0) := by
    have hsub := (hy.tendsto a₀).sub_const (y a₀)
    rw [sub_self] at hsub
    have h' := (continuous_eNorm.tendsto (0 : Lp F 2 (volume : Measure V))).comp hsub
    rw [eNorm_zero] at h'
    exact h'
  set a : ℝ≥0∞ := C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ V : ℝ) / 2 -
    Module.finrank ℝ V * (r⁻¹).toReal))
  have hlim : Tendsto (fun x ↦ a * ‖y x - y a₀‖ₑ) (𝓝 a₀) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul h (Or.inr (by finiteness : a ≠ ∞))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le)
    fun a ↦ ?_
  calc _ = eLpNorm (Lp.fourierMultiplierCLM F m (y a - y a₀)) r volume := by
        rw [map_sub]
        exact eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm
    _ ≤ _ := hC j m hm _

end ContDiffBump

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Strichartz.TTStar
public import TauCeti.Analysis.PDE.Wave.Dispersive
import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Star
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Integral.RieszThorin

/-!
# Frequency-localized Strichartz estimates for the half-wave propagator

On a finite-dimensional real inner product space `E` of dimension `n`, let `W₊(t) = exp(itD)`,
`D = √(-Δ)`, be the half-wave propagator (`TauCeti.halfWavePropagator`) and let `Pⱼ` be the
`L²` Fourier multiplier with the Littlewood–Paley cutoff `ψⱼ` as symbol, so that `Pⱼ f` has
frequencies in the annulus `‖ξ‖ ≈ 2^j`. Call `(q, r)` *sharp wave-admissible* when

`2 / q + (n - 1) / r = (n - 1) / 2`,

and put `s(q, r) = n / 2 - n / r - 1 / q`, the scaling-critical regularity. With `2 < q < ∞` and
`n ≥ 1` this forces `n ≥ 2` and `2 < r`; on a point, `n = 0`, the cutoffs `ψⱼ` vanish and the
estimates hold trivially. For every such pair this file proves the frequency-localized wave
Strichartz estimate

`‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{j s(q, r)} ‖f‖₂`

in weak form, with `C` independent of `j ∈ ℤ`
(`ContDiffBump.exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le`), its dual
`‖∫ Pⱼ W₊(-τ) F(τ) dτ‖₂ ≤ C 2^{j s(q, r)} ‖F‖_{L^{q'}_t L^{r'}_x}`
(`ContDiffBump.exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le`), and the
bilinear bound on the Duhamel pairings `⟪W₊(t - τ) Pⱼ² F(τ), G(t)⟫` with constant
`C 2^{2j s(q, r)}`, whose restriction to `τ < t` is the frequency-localized retarded estimate.

## The argument

The `TT*` argument of `TauCeti.Analysis.PDE.Strichartz.TTStar` applies to the family
`U(t) = W₊(t) Pⱼ`. Since `ψⱼ` is real, `Pⱼ` is self-adjoint, and the time pairings are

`U(t) U(τ)* = W₊(t - τ) Pⱼ²`,

the Fourier multiplier with the Schwartz symbol `exp(2πi (t - τ) ‖ξ‖) ψⱼ(ξ)²`. Its kernel obeys
the dispersive bound for frequency-localized half-wave kernels rescaled to frequency `2^j`
(`TauCeti.exists_norm_fourierInv_phaseSymbol_sqrtNegLaplacianSymbol_mul_inv_smul_le`), applied to
the profile `ψ₀²`: for `T = t - τ ≠ 0`,

`‖W₊(T) Pⱼ² g‖_∞ ≤ C 2^{jn} (1 + 2^j |T|)^(-(n - 1)/2) ‖g‖₁`
`            ≤ C 2^{j(n + 1)/2} |T|^(-(n - 1)/2) ‖g‖₁`.

Since `|ψⱼ| ≤ 1`, the same operator is a contraction on `L²`, and the Riesz–Thorin theorem gives
the bound from `L^{r'}` to `L^r` with decay `|T|^(-(n - 1)(1/2 - 1/r)) = |T|^(-2/q)` and constant
`C' 2^{2j s(q, r)}`. The `TT*` engine turns this into the estimates above.

## Main declarations

* `ContDiffBump.exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le`: the
  homogeneous estimate in weak form.
* `ContDiffBump.exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le`: the dual
  homogeneous estimate.
* `ContDiffBump.exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_le`: the bilinear
  estimate for the Duhamel pairings.
* `ContDiffBump.exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_le`: the
  retarded estimate in weak form.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3, Theorem 2.6 and its proof.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
-/

public section

noncomputable section

open scoped FourierTransform ContDiff SchwartzMap ENNReal NNReal InnerProductSpace InnerProduct
open MeasureTheory Filter Complex

namespace ContDiffBump

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (φ : ContDiffBump (0 : E))

/-! ### The kernels of the time pairings -/

/-- For `n ≥ 1` and `τ ≠ 0`, the dispersive decay `2^{jn} (1 + 2^j |τ|)^(-(n - 1)/2)` is at most
`2^{j(n + 1)/2} |τ|^(-(n - 1)/2)`. -/
private theorem pow_mul_one_add_rpow_le {n : ℕ} (hn : 1 ≤ n) (j : ℤ) {τ : ℝ} (hτ : τ ≠ 0) :
    ((2 : ℝ) ^ j) ^ n * (1 + 2 ^ j * |τ|) ^ (-((n : ℝ) - 1) / 2) ≤
      ((2 : ℝ) ^ j) ^ (((n : ℝ) + 1) / 2) * |τ| ^ (-((n : ℝ) - 1) / 2) := by
  have h2 : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  have hτ' : 0 < |τ| := abs_pos.2 hτ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc ((2 : ℝ) ^ j) ^ n * (1 + 2 ^ j * |τ|) ^ (-((n : ℝ) - 1) / 2)
      ≤ ((2 : ℝ) ^ j) ^ n * (2 ^ j * |τ|) ^ (-((n : ℝ) - 1) / 2) := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity)
          (by linarith) (by linarith)) (by positivity)
    _ = ((2 : ℝ) ^ j) ^ (((n : ℝ) + 1) / 2) * |τ| ^ (-((n : ℝ) - 1) / 2) := by
        rw [Real.mul_rpow h2.le hτ'.le, ← mul_assoc, ← Real.rpow_natCast,
          ← Real.rpow_add h2]
        congr 2
        ring

/-- The dispersive bound for the half-wave kernels localized by the squared dyadic cutoffs `ψⱼ²`:
in dimension `n ≥ 1`, `|𝓕⁻ (exp(2πiτ‖·‖) ψⱼ²) (x)| ≤ C 2^{j(n + 1)/2} |τ|^(-(n - 1)/2)` for
`τ ≠ 0`, uniformly in `j` and `x`, with `C > 0`. -/
private theorem exists_norm_fourierInv_phaseSymbol_mul_littlewoodPaley_sq_le :
    ∃ C, 0 < C ∧ ∀ (j : ℤ) {τ : ℝ}, τ ≠ 0 → 1 ≤ Module.finrank ℝ E → ∀ x : E,
      ‖𝓕⁻ (fun ξ ↦ phaseSymbol sqrtNegLaplacianSymbol τ ξ *
          ((φ.littlewoodPaley j ξ ^ 2 : ℝ) : ℂ)) x‖ ≤
        C * ((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) + 1) / 2) *
          |τ| ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2) := by
  have hc : HasCompactSupport fun ξ ↦ φ.littlewoodPaley 0 ξ ^ 2 := by
    convert (φ.hasCompactSupport_littlewoodPaley 0).mul_right (f' := φ.littlewoodPaley 0) using 1
    funext ξ
    simp [sq]
  obtain ⟨C, hC0, hC⟩ := exists_norm_fourierInv_phaseSymbol_sqrtNegLaplacianSymbol_mul_inv_smul_le
    (ψ := fun ξ ↦ ((φ.littlewoodPaley 0 ξ ^ 2 : ℝ) : ℂ))
    (ofRealCLM.contDiff.comp ((φ.contDiff_littlewoodPaley 0).pow 2))
    (hc.comp_left ofReal_zero)
    (fun h ↦ φ.zero_notMem_tsupport_littlewoodPaley 0 <| by
      have h' := tsupport_comp_subset ofReal_zero _ h
      simp only [sq] at h'
      exact tsupport_mul_subset_left h')
  refine ⟨C + 1, by linarith, fun j τ hτ hn x ↦ ?_⟩
  -- `ψⱼ²` is the rescaling `ψ₀² (2^{-j} ·)`.
  have heq : (fun ξ ↦ phaseSymbol sqrtNegLaplacianSymbol τ ξ *
      ((φ.littlewoodPaley j ξ ^ 2 : ℝ) : ℂ)) =
      fun ξ ↦ phaseSymbol sqrtNegLaplacianSymbol τ ξ *
        (fun η ↦ ((φ.littlewoodPaley 0 η ^ 2 : ℝ) : ℂ)) (((2 : ℝ) ^ j)⁻¹ • ξ) := by
    ext ξ
    rw [littlewoodPaley_apply_eq_littlewoodPaley_zero_apply]
  rw [heq, mul_assoc]
  calc _ ≤ C * (((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
        (1 + 2 ^ j * |τ|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)) := by
        rw [← mul_assoc]
        exact hC (zpow_pos two_pos j) τ x
    _ ≤ (C + 1) * (((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
        (1 + 2 ^ j * |τ|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)) := by
        gcongr
        linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_mul_one_add_rpow_le hn j hτ) (by linarith)

/-! ### The time pairings -/

variable {φ}

/-- The adjoint of `W₊(t) Pⱼ` is `Pⱼ W₊(-t)`. -/
private theorem adjoint_halfWavePropagator_comp {j : ℤ} {m : Lp ℂ ∞ (volume : Measure E)}
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (t : ℝ) :
    ((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) =
      Lp.fourierMultiplierCLM ℂ m ∘L halfWavePropagator ℂ (-t) := by
  rw [ContinuousLinearMap.adjoint_comp, Lp.adjoint_fourierMultiplierCLM,
    Lp.star_eq_self_of_ae_eq_ofReal hm, halfWavePropagator_def, adjoint_phasePropagator]

variable (φ) in
/-- The Schwartz symbol `exp(2πiτ‖ξ‖) ψⱼ(ξ)²` of `W₊(τ) Pⱼ²`. -/
private def pairingSymbol (j : ℤ) (τ : ℝ) : 𝓢(E, ℂ) :=
  φ.littlewoodPaleyPiece (m := fun ξ ↦ phaseSymbol sqrtNegLaplacianSymbol τ ξ *
      (φ.littlewoodPaley j ξ : ℂ))
    ((contDiffOn_phaseSymbol_sqrtNegLaplacianSymbol τ).mul
      (ofRealCLM.contDiff.comp (φ.contDiff_littlewoodPaley j)).contDiffOn) j

omit [MeasurableSpace E] [BorelSpace E] in
/-- The values of the pairing symbol: `exp(2πiτ‖ξ‖) ψⱼ(ξ)²`. -/
private theorem coe_pairingSymbol (j : ℤ) (τ : ℝ) :
    ⇑(φ.pairingSymbol j τ) = fun ξ ↦ phaseSymbol sqrtNegLaplacianSymbol τ ξ *
      ((φ.littlewoodPaley j ξ ^ 2 : ℝ) : ℂ) := by
  rw [pairingSymbol, coe_littlewoodPaleyPiece]
  funext ξ
  rw [Complex.real_smul]
  push_cast
  ring

/-- `W₊(τ) Pⱼ²` is the multiplier with symbol `exp(2πiτ‖ξ‖) ψⱼ(ξ)²`. -/
private theorem halfWavePropagator_fourierMultiplierCLM_fourierMultiplierCLM {j : ℤ}
    {m : Lp ℂ ∞ (volume : Measure E)} (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    (τ : ℝ) (g : Lp ℂ 2 (volume : Measure E)) :
    halfWavePropagator ℂ τ (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m g)) =
      Lp.fourierMultiplierCLM ℂ ((φ.pairingSymbol j τ).toLp ∞) g := by
  rw [Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply, halfWavePropagator_def]
  refine phasePropagator_fourierMultiplierCLM_apply_of_ae_eq _ τ ?_ g
  filter_upwards [(φ.pairingSymbol j τ).coeFn_toLp ∞, Lp.coeFn_lpSMul (r := ∞) m m, hm]
    with ξ h₁ h₂ h₃
  rw [h₁, h₂, Pi.smul_apply', h₃, coe_pairingSymbol, smul_eq_mul]
  push_cast
  ring

/-- The time pairing `W₊(s) Pⱼ (W₊(t) Pⱼ)*` is the multiplier with symbol
`exp(2πi (s - t) ‖ξ‖) ψⱼ(ξ)²`. -/
private theorem halfWavePropagator_comp_adjoint_apply {j : ℤ} {m : Lp ℂ ∞ (volume : Measure E)}
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (s t : ℝ)
    (g : Lp ℂ 2 (volume : Measure E)) :
    (halfWavePropagator ℂ s ∘L Lp.fourierMultiplierCLM ℂ m)
        (((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) g) =
      Lp.fourierMultiplierCLM ℂ ((φ.pairingSymbol j (s - t)).toLp ∞) g := by
  -- `Pⱼ` commutes with `W₊(-t)`, and `W₊(s) W₊(-t) = W₊(s - t)`.
  have hc (τ : ℝ) (h : Lp ℂ 2 (volume : Measure E)) :
      Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ τ h) =
        halfWavePropagator ℂ τ (Lp.fourierMultiplierCLM ℂ m h) :=
    (DFunLike.congr_fun (phasePropagator_comp_fourierMultiplierCLM _ τ m) h).symm
  simp only [adjoint_halfWavePropagator_comp hm, ContinuousLinearMap.comp_apply]
  rw [hc, hc, halfWavePropagator_def, halfWavePropagator_def, ← phasePropagator_add_apply,
    ← sub_eq_add_neg, ← halfWavePropagator_def,
    halfWavePropagator_fourierMultiplierCLM_fourierMultiplierCLM hm]

/-- The multiplier `W₊(τ) Pⱼ²` is a contraction on `L²`. -/
private theorem norm_fourierMultiplierCLM_pairingSymbol_le (j : ℤ) (τ : ℝ) :
    ‖Lp.fourierMultiplierCLM (E := E) ℂ ((φ.pairingSymbol j τ).toLp ∞)‖ ≤ 1 := by
  refine (Lp.norm_fourierMultiplierCLM_le _).trans (Lp.norm_top_le_of_ae_bound zero_le_one ?_)
  filter_upwards [(φ.pairingSymbol j τ).coeFn_toLp ∞] with ξ h
  rw [h, coe_pairingSymbol, norm_mul, norm_phaseSymbol, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (φ.abs_littlewoodPaley_le_one j ξ)

/-- The constant bookkeeping of the time pairings: interpolating the dispersive constant
`c 2^{j(n + 1)/2} |τ|^(-(n - 1)/2)` with exponent `1 - 2ρ` along a sharp wave-admissible pair
gives `c^(1 - 2ρ) 2^{2js} |τ|^(-2/q)`, `s = n / 2 - nρ - 1 / q`. -/
private theorem mul_rpow_mul_rpow_rpow_eq {c x a n ρ q : ℝ} (hc : 0 ≤ c) (hx : 0 < x)
    (ha : 0 < a) (hqr : 2 / q + (n - 1) * ρ = (n - 1) / 2) :
    (c * x ^ ((n + 1) / 2) * a ^ (-(n - 1) / 2)) ^ (1 - 2 * ρ) =
      c ^ (1 - 2 * ρ) * x ^ (2 * (n / 2 - n * ρ - 1 / q)) * a ^ (-(2 / q)) := by
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hc (by positivity),
    ← Real.rpow_mul hx.le, ← Real.rpow_mul ha.le]
  congr 3 <;> linear_combination hqr

omit [MeasurableSpace E] [BorelSpace E] in
/-- On a point the cutoff `ψⱼ` vanishes, and so does the symbol `exp(2πiτ‖ξ‖) ψⱼ(ξ)²`. -/
private theorem pairingSymbol_eq_zero (hn : Module.finrank ℝ E = 0) (j : ℤ) (τ : ℝ) :
    ⇑(φ.pairingSymbol j τ) = 0 := by
  have : Subsingleton E := Module.finrank_zero_iff.1 hn
  funext ξ
  rw [coe_pairingSymbol, Subsingleton.elim ξ 0]
  simp

variable (φ) in
/-- **The decay of the time pairings.** Along a sharp wave-admissible pair
`2 / q + (n - 1) / r = (n - 1) / 2` with `2 < q`, the time pairings
`W₊(s) Pⱼ (W₊(t) Pⱼ)* = W₊(s - t) Pⱼ²` decay from `L^{r'}` to `L^r` like `|s - t| ^ (-2 / q)`,
with constant `K 2^{2j s(q, r)}`, `s(q, r) = n / 2 - n / r - 1 / q`. -/
private theorem exists_eLpNorm_halfWavePropagator_comp_adjoint_le {q : ℝ≥0} {r r' : ℝ≥0∞}
    [r'.HolderConjugate r] (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal =
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ s t, s ≠ t →
      ∀ g : Lp ℂ 2 (volume : Measure E),
        eLpNorm ((halfWavePropagator ℂ s ∘L Lp.fourierMultiplierCLM ℂ m)
            (((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) g)) r volume ≤
          ENNReal.ofReal (K * ((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) *
            ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' volume := by
  obtain ⟨C, hC0, hC⟩ := φ.exists_norm_fourierInv_phaseSymbol_mul_littlewoodPaley_sq_le
  refine ⟨C ^ (1 - 2 * (r⁻¹).toReal), by positivity, fun j m hm s t hst g ↦ ?_⟩
  rw [halfWavePropagator_comp_adjoint_apply hm]
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hn | hn
  · -- On a point the pairing vanishes.
    have hσ : (φ.pairingSymbol j (s - t)).toLp ∞ (volume : Measure E) = 0 := by
      apply Lp.ext
      filter_upwards [(φ.pairingSymbol j (s - t)).coeFn_toLp ∞,
        Lp.coeFn_zero ℂ ∞ (volume : Measure E)] with ξ h₁ h₂
      rw [h₁, h₂, φ.pairingSymbol_eq_zero hn j (s - t)]
    rw [hσ, Lp.fourierMultiplierCLM_zero, zero_apply,
      eLpNorm_congr_ae (Lp.coeFn_zero ℂ 2 (volume : Measure E)), eLpNorm_zero]
    exact bot_le
  have hst' : s - t ≠ 0 := sub_ne_zero.2 hst
  have h2 : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  by_cases hg : MemLp g r' volume
  swap
  · rw [top_unique (not_lt.1 (memLp_iff.not.1 hg)), ENNReal.mul_top]
    · exact le_top
    · refine mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' ?_
      exact (ENNReal.rpow_pos (by simpa using hst') (by simp)).ne'
  -- Interpolate between the `L¹ → L^∞` bound `B` of the kernel and the `L² → L²` bound `1`.
  set B : ℝ := C * ((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) + 1) / 2) *
    |s - t| ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2) with hB
  have hB0 : 0 ≤ B := by positivity
  have h₀ : ∀ f : Lp ℂ 2 (volume : Measure E), Integrable f →
      eLpNorm (Lp.fourierMultiplierCLM ℂ ((φ.pairingSymbol j (s - t)).toLp ∞) f) ∞ volume ≤
        (B.toNNReal : ℝ≥0∞) * eLpNorm f 1 volume := fun f hf ↦ by
    rw [ENNReal.ofNNReal_toNNReal]
    refine (φ.pairingSymbol j (s - t)).eLpNorm_fourierMultiplierCLM_toLp_top_le (fun x ↦ ?_) hf
    rw [SchwartzMap.fourierInv_coe, coe_pairingSymbol]
    exact hC j hst' hn x
  have h₁ : ‖Lp.fourierMultiplierCLM (E := E) ℂ ((φ.pairingSymbol j (s - t)).toLp ∞)‖ ≤
      ((1 : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_one]
    exact norm_fourierMultiplierCLM_pairingSymbol_le j (s - t)
  have hn1 : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hn
  have hq0 : (0 : ℝ) < 2 / q := div_pos two_pos (by exact_mod_cast zero_lt_two.trans hq)
  -- Admissibility with `2 < q` and `n ≥ 1` forces `1 / r < 1 / 2`, so `2 ≤ r`.
  have hr : 2 ≤ r :=
    ENNReal.two_le_of_toReal_inv_le (ENNReal.HolderConjugate.ne_zero r r') (by nlinarith)
  refine (ContinuousLinearMap.eLpNorm_apply_le_rpow_mul_rpow_mul_eLpNorm _ h₀ h₁ hr g hg).trans
    (le_of_eq ?_)
  -- Bookkeeping of the constants.
  rw [NNReal.one_rpow, mul_one, ← ofReal_norm, Real.norm_eq_abs,
    ENNReal.ofReal_rpow_of_pos (abs_pos.2 hst'), ← ENNReal.ofReal_mul (by positivity),
    ← Real.toNNReal_rpow_of_nonneg hB0, ENNReal.ofNNReal_toNNReal]
  congr 2
  rw [hB, mul_rpow_mul_rpow_rpow_eq hC0.le h2 (abs_pos.2 hst') hqr]

/-! ### The Strichartz estimates -/

section Admissible

variable {p q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- Square root of the constant `K 2^{2j s(q, r)}` of the time pairings. -/
private theorem ofReal_mul_rpow_rpow_inv_two {K : ℝ} (hK : 0 ≤ K) (j : ℤ) (σ : ℝ) :
    ENNReal.ofReal (K * ((2 : ℝ) ^ j) ^ (2 * σ)) ^ (2⁻¹ : ℝ) =
      ENNReal.ofReal (K ^ (2⁻¹ : ℝ)) * ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) := by
  have h2 : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    Real.mul_rpow hK (by positivity), ← Real.rpow_mul h2.le,
    ENNReal.ofReal_mul (by positivity)]
  congr 3
  ring

/-- **The frequency-localized Strichartz estimate for the half-wave propagator**, in weak form.
Let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, let `(q, r)` be sharp wave-admissible,
`2 / q + (n - 1) / r = (n - 1) / 2` with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates of
`q` and `r`, and put `s(q, r) = n / 2 - n / r - 1 / q`. There is `C` such that for every `j ∈ ℤ`
and every `L^∞` symbol `m` equal to `ψⱼ` almost everywhere, with `L²` multiplier `Pⱼ`, every
`f ∈ L²(E)` and every almost everywhere strongly measurable `G : ℝ → L²(E)` for which
`t ↦ Pⱼ W₊(-t) G(t)` is integrable,

`|∫ ⟪W₊(t) Pⱼ f, G(t)⟫ dt| ≤ C 2^{j s(q, r)} ‖f‖₂ ‖G‖_{L^p_t L^{r'}_x}`.

This is `‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{j s(q, r)} ‖f‖₂` tested against `G`. -/
theorem exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal =
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (f : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)),
      AEStronglyMeasurable G →
      Integrable (fun t ↦ Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ (-t) (G t))) →
      ‖∫ t, ⟪halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f), G t⟫_ℂ‖ₑ ≤
        C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q)) * ‖f‖ₑ *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨K, hK0, hK⟩ := φ.exists_eLpNorm_halfWavePropagator_comp_adjoint_le (r' := r') hq hqr
  obtain ⟨C, hC⟩ := exists_enorm_integral_inner_apply_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq hpq
  refine ⟨C * (K ^ (2⁻¹ : ℝ)).toNNReal, fun j m hm f G hG hPG ↦ ?_⟩
  have h := hC (fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m) _
    (hK j m hm) f G hG
    (by simpa only [adjoint_halfWavePropagator_comp hm, ContinuousLinearMap.comp_apply] using hPG)
  rw [ofReal_mul_rpow_rpow_inv_two hK0] at h
  rw [ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal]
  simpa only [ContinuousLinearMap.comp_apply, mul_assoc] using h

/-- **The dual frequency-localized Strichartz estimate for the half-wave propagator.**
Let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, let `(q, r)` be sharp wave-admissible,
`2 / q + (n - 1) / r = (n - 1) / 2` with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates of
`q` and `r`, and put `s(q, r) = n / 2 - n / r - 1 / q`. There is `C` such that for every `j ∈ ℤ`
and every `L^∞` symbol `m` equal to `ψⱼ` almost everywhere, with `L²` multiplier `Pⱼ`, and
every almost everywhere strongly measurable `F : ℝ → L²(E)` for which `τ ↦ Pⱼ W₊(-τ) F(τ)` is
integrable,

`‖∫ Pⱼ W₊(-τ) F(τ) dτ‖₂ ≤ C 2^{j s(q, r)} ‖F‖_{L^p_t L^{r'}_x}`. -/
theorem exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal =
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      Integrable (fun s ↦ Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ (-s) (F s))) →
      ‖∫ s, Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ (-s) (F s))‖ₑ ≤
        C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q)) *
          eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume := by
  obtain ⟨K, hK0, hK⟩ := φ.exists_eLpNorm_halfWavePropagator_comp_adjoint_le (r' := r') hq hqr
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq hpq
  refine ⟨C * (K ^ (2⁻¹ : ℝ)).toNNReal, fun j m hm F hF hPF ↦ ?_⟩
  have h := hC (fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m) _
    (hK j m hm) F hF
    (by simpa only [adjoint_halfWavePropagator_comp hm, ContinuousLinearMap.comp_apply] using hPF)
  rw [ofReal_mul_rpow_rpow_inv_two hK0] at h
  rw [ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal]
  simpa only [adjoint_halfWavePropagator_comp hm, ContinuousLinearMap.comp_apply,
    mul_assoc] using h

/-- **The bilinear frequency-localized Strichartz estimate for the half-wave propagator.**
Let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, let `(q, r)` be sharp wave-admissible,
`2 / q + (n - 1) / r = (n - 1) / 2` with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates of
`q` and `r`, and put `s(q, r) = n / 2 - n / r - 1 / q`. There is `C` such that for every `j ∈ ℤ`
and every `L^∞` symbol `m` equal to `ψⱼ` almost everywhere, with `L²` multiplier `Pⱼ`, and
all almost everywhere strongly measurable `F, G : ℝ → L²(E)`,

`∫∫ |⟪W₊(t - τ) Pⱼ² F(τ), G(t)⟫| dτ dt`
`  ≤ C 2^{2j s(q, r)} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

Since the integrand is the absolute value of the Duhamel pairing, the bound also controls the
integral over any part of the `(τ, t)` plane, such as the retarded region `τ < t`
(`ContDiffBump.exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_le`). -/
theorem exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal =
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      AEStronglyMeasurable G →
      ∫⁻ t, ∫⁻ s, ‖⟪halfWavePropagator ℂ (t - s)
          (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ ≤
        C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) *
          eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨K, hK0, hK⟩ := φ.exists_eLpNorm_halfWavePropagator_comp_adjoint_le (r' := r') hq hqr
  obtain ⟨C, hC⟩ := exists_lintegral_lintegral_enorm_inner_adjoint_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq
    hpq
  refine ⟨C * K.toNNReal, fun j m hm F G hF hG ↦ ?_⟩
  set U := fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m
  -- The Duhamel pairing `⟪W₊(t - τ) Pⱼ² F(τ), G(t)⟫` is the time pairing
  -- `⟪U(t)* G(t), U(s)* F(s)⟫` up to complex conjugation.
  have hpair (s t : ℝ) : ‖⟪halfWavePropagator ℂ (t - s)
      (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ =
      ‖⟪((U t)†) (G t), ((U s)†) (F s)⟫_ℂ‖ₑ := by
    rw [ContinuousLinearMap.adjoint_inner_left, halfWavePropagator_comp_adjoint_apply hm,
      halfWavePropagator_fourierMultiplierCLM_fourierMultiplierCLM hm, ← ofReal_norm,
      ← ofReal_norm, norm_inner_symm]
  simp_rw [hpair]
  calc _ ≤ _ := hC U _ (hK j m hm) G F hG hF
    _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal, ENNReal.ofReal_mul hK0]
        ring

/-- **The retarded frequency-localized Strichartz estimate for the half-wave propagator**, in
weak form. Let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, let `(q, r)` be sharp
wave-admissible, `2 / q + (n - 1) / r = (n - 1) / 2` with `2 < q < ∞`, let `p` and `r'` be the
Hölder conjugates of `q` and `r`, and put `s(q, r) = n / 2 - n / r - 1 / q`. There is `C` such
that for every `j ∈ ℤ` and every `L^∞` symbol `m` equal to `ψⱼ` almost everywhere, with `L²`
multiplier `Pⱼ`, and all almost everywhere strongly measurable `F, G : ℝ → L²(E)`,

`|∫ ∫_{τ < t} ⟪W₊(t - τ) Pⱼ² F(τ), G(t)⟫ dτ dt|`
`  ≤ C 2^{2j s(q, r)} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

This is the Duhamel estimate
`‖∫_{τ < t} W₊(t - τ) Pⱼ² F(τ) dτ‖_{L^q_t L^r_x} ≤ C 2^{2j s(q, r)} ‖F‖_{L^p_t L^{r'}_x}`
tested against `G`. -/
theorem exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal =
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      AEStronglyMeasurable G →
      ‖∫ t, ∫ s in Set.Iio t, ⟪halfWavePropagator ℂ (t - s)
          (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ ≤
        C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) *
          eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C, hC⟩ :=
    φ.exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_le (r' := r') hq hpq hqr
  exact ⟨C, fun j m hm F G hF hG ↦
    (enorm_integral_setIntegral_le_lintegral_lintegral _).trans (hC j m hm F G hF hG)⟩

end Admissible

end ContDiffBump

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.Propagator
public import TauCeti.Analysis.PDE.Wave.Strichartz
import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.Lp.MixedNorm

/-!
# Mixed-norm Strichartz estimates for the frequency-localized wave equation

On a real inner product space `E` of dimension `n`, let `D = √(-Δ)` and let `Pⱼ`, `j ∈ ℤ`, be the
`L²` Fourier multiplier with the homogeneous Littlewood–Paley cutoff `ψⱼ`
(`ContDiffBump.littlewoodPaley`) as symbol. The solution of the wave equation `∂ₜ²u - Δu = F` with
`u(0) = f` and `∂ₜu(0) = g` is

`u(t) = cos(tD) f + D⁻¹ sin(tD) g + ∫_0^t D⁻¹ sin((t - s)D) F(s) ds`

(`TauCeti.waveCosPropagator`, `TauCeti.waveSinPropagator`). The Strichartz estimates for the
frequency-localized half-wave propagators `W₊(t) Pⱼ`, `W₊(t) = exp(itD)`, are proved in weak form
in `TauCeti.Analysis.PDE.Wave.Strichartz`. This file turns them into mixed-norm estimates for the
three terms of `u`, uniformly in the scale `j`. Let `(q, r)` be wave-admissible,
`2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates
of `q` and `r`, and let `γ = n / 2 - n / r - 1 / q`. Then there is `C` such that for every
`j ∈ ℤ`,

* `‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{jγ} ‖f‖₂` and `‖cos(tD) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{jγ} ‖f‖₂`;
* `‖D⁻¹ sin(tD) Pⱼ g‖_{L^q_t L^r_x} ≤ C 2^{j(γ - 1)} ‖g‖₂`;
* `‖∫_{s < t} D⁻¹ sin((t - s)D) Pⱼ Pⱼ F(s) ds‖_{L^q_t L^r_x} ≤ C 2^{j(2γ - 1)} ‖F‖_{L^p_t L^{r'}_x}`
  for forcing terms `F : ℝ → L²(E)` integrable in time.

The last one comes from the bilinear estimate for the Duhamel pairings,
`∫∫ |⟪D⁻¹ sin((t - s)D) Pⱼ Pⱼ F(s), G(t)⟫| ds dt ≤ C 2^{j(2γ - 1)} ‖F‖_{L^p_t L^{r'}_x}
‖G‖_{L^p_t L^{r'}_x}`. The factor `2^{-j}` gained over the
half-wave estimates is the size of `D⁻¹` at frequencies `‖ξ‖ ≈ 2^j`. These are the
frequency-localized estimates from which the Strichartz estimates for the inhomogeneous wave
equation, with data and forcing in homogeneous Besov classes, are assembled by Littlewood–Paley
summation.

## The argument

The symbol `1 / (2π ‖·‖)` is smooth away from the origin, so it agrees on the annulus
`φ.rIn / 2 ≤ ‖ξ‖ ≤ φ.rOut`, which contains the support of `ψ₀`, with a Schwartz function `θ`
(`SchwartzMap.exists_eqOn_annulus_of_contDiffOn`). Let `Mⱼ` be the multiplier with symbol
`θ(2^{-j} ·)`. Its kernel is the `L¹`-normalised dilate of `𝓕⁻ θ`, so `Mⱼ` is bounded on every
`Lᵖ` uniformly in `j`, and `2^{-j} θ(2^{-j} ξ) · 2π ‖ξ‖ = 1` on the support of `ψⱼ`. Since
`sin x = (e^{ix} - e^{-ix}) / 2i`,

`D⁻¹ sin(τD) Pⱼ = 2^{-j} (2i)⁻¹ (W₊(τ) - W₊(-τ)) Pⱼ Mⱼ`,

and likewise with `Pⱼ Pⱼ` in place of `Pⱼ`, while `cos(τD) = (W₊(τ) + W₊(-τ)) / 2`
(`TauCeti.waveCosPropagator_eq_halfWavePropagator`). The `W₊(τ)` halves are controlled by the
half-wave estimates, and the `W₊(-τ)` halves reduce to them by reflecting time, `t ↦ -t`, which
preserves the mixed norms. The mixed-norm forms follow from the weak forms by testing against
`L²`-valued functions
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le`).

## Main declarations

All in the `ContDiffBump` namespace, with `φ` the bump function defining the cutoffs.

* `exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le`: the estimate for `W₊(t) Pⱼ`.
* `exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le`: the estimate for `cos(tD) Pⱼ`.
* `exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le`: the estimate for
  `D⁻¹ sin(tD) Pⱼ`.
* `exists_lintegral_lintegral_enorm_inner_waveSinPropagator_sub_littlewoodPaley_le`: the bilinear
  estimate for the Duhamel pairings.
* `exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le`: the retarded
  estimate for the Duhamel integral.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3 (Theorem 2.6 and its proof).
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
-/

public section

noncomputable section

open scoped ENNReal NNReal FourierTransform InnerProductSpace InnerProduct SchwartzMap
open MeasureTheory TauCeti

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (φ : ContDiffBump (0 : E))

/-! ### The frequency-localized inverse of `D` -/

/-- A Schwartz function `θ₀` equal to `1 / (2π ‖(φ.rIn / 2) • η‖)` on the annulus
`1 ≤ ‖η‖ ≤ 2 φ.rOut / φ.rIn`: the symbol is smooth away from the origin. -/
private theorem exists_invCutoff : ∃ σ : 𝓢(E, ℂ), Set.EqOn σ
    (fun η ↦ (((sqrtNegLaplacianSymbol ((φ.rIn / 2) • η))⁻¹ : ℝ) : ℂ))
    {η | 1 ≤ ‖η‖ ∧ ‖η‖ ≤ 2 * φ.rOut / φ.rIn} := by
  have ha : φ.rIn / 2 ≠ 0 := (half_pos φ.rIn_pos).ne'
  refine SchwartzMap.exists_eqOn_annulus_of_contDiffOn
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (ContDiffOn.inv (fun η hη ↦ ?_) fun η hη ↦ ?_)) _
  · simp only [sqrtNegLaplacianSymbol_apply]
    exact (contDiffAt_const.mul ((contDiffAt_norm ℝ (smul_ne_zero ha hη)).comp η
      (contDiff_const_smul _).contDiffAt)).contDiffWithinAt
  · rw [sqrtNegLaplacianSymbol_apply]
    have := norm_pos_iff.2 (smul_ne_zero ha hη)
    positivity

/-- The Schwartz function `θ₀` of `exists_invCutoff`. -/
private def invCutoff : 𝓢(E, ℂ) :=
  φ.exists_invCutoff.choose

/-- The symbol `θ(2^{-j} ·)` as a Schwartz function, where `θ = θ₀((φ.rIn / 2)⁻¹ ·)` equals
`1 / (2π ‖·‖)` on the annulus `φ.rIn / 2 ≤ ‖ξ‖ ≤ φ.rOut` containing the support of `ψ₀`. -/
private def invCutoffSchwartz (j : ℤ) : 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.smulLeft
    (Units.mk0 ((2 : ℝ) ^ j * (φ.rIn / 2))⁻¹ (inv_ne_zero
      (mul_pos (zpow_pos two_pos j) (half_pos φ.rIn_pos)).ne'))) φ.invCutoff

/-- The values of `θ(2^{-j} ·)`. -/
private theorem invCutoffSchwartz_apply (j : ℤ) (ξ : E) :
    φ.invCutoffSchwartz j ξ = φ.invCutoff (((2 : ℝ) ^ j * (φ.rIn / 2))⁻¹ • ξ) := by
  rw [invCutoffSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_mk0]

/-- On the support of `ψⱼ`, `2^{-j} θ(2^{-j} ξ)` inverts the symbol `2π ‖ξ‖` of `D`. -/
private theorem inv_mul_invCutoffSchwartz_mul {j : ℤ} {ξ : E} (hξ : φ.littlewoodPaley j ξ ≠ 0) :
    (((2 : ℝ) ^ j)⁻¹ : ℂ) * φ.invCutoffSchwartz j ξ * (sqrtNegLaplacianSymbol ξ : ℂ) = 1 := by
  have h2j : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  have hb : (0 : ℝ) < 2 ^ j * (φ.rIn / 2) := mul_pos h2j (half_pos φ.rIn_pos)
  have h1 : 2 ^ (j - 1) * φ.rIn < ‖ξ‖ := by
    by_contra h
    exact hξ (φ.littlewoodPaley_eq_zero_of_norm_le (not_lt.1 h))
  have h2 : ‖ξ‖ < 2 ^ j * φ.rOut := by
    by_contra h
    exact hξ (φ.littlewoodPaley_eq_zero_of_le_norm (not_lt.1 h))
  rw [zpow_sub_one₀ two_ne_zero] at h1
  set η := ((2 : ℝ) ^ j * (φ.rIn / 2))⁻¹ • ξ
  have hη : ‖η‖ = ‖ξ‖ / (2 ^ j * (φ.rIn / 2)) := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hb.le), inv_mul_eq_div]
  have hmem : 1 ≤ ‖η‖ ∧ ‖η‖ ≤ 2 * φ.rOut / φ.rIn := by
    rw [hη, le_div_iff₀ hb, div_le_div_iff₀ hb φ.rIn_pos]
    constructor <;> nlinarith [φ.rIn_pos]
  have haη : (φ.rIn / 2) • η = ((2 : ℝ) ^ j)⁻¹ • ξ := by
    rw [smul_smul, mul_inv, ← mul_assoc, mul_comm (φ.rIn / 2), mul_assoc,
      mul_inv_cancel₀ (half_pos φ.rIn_pos).ne', mul_one]
  have hξ0 : (‖ξ‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (lt_trans (by have := φ.rIn_pos; positivity) h1).ne'
  rw [invCutoffSchwartz_apply, invCutoff, φ.exists_invCutoff.choose_spec hmem]
  beta_reduce
  rw [haη, sqrtNegLaplacianSymbol_apply, sqrtNegLaplacianSymbol_apply, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 h2j.le)]
  push_cast
  field_simp

variable [MeasurableSpace E] [BorelSpace E]

/-- The kernel of the multiplier `θ(2^{-j} ·)` has the same `L¹` norm for every `j`. -/
private theorem eLpNorm_fourierInv_invCutoffSchwartz (j : ℤ) :
    eLpNorm (𝓕⁻ ⇑(φ.invCutoffSchwartz j)) 1 volume =
      eLpNorm (𝓕⁻ ⇑(φ.invCutoffSchwartz 0)) 1 volume := by
  have h : ⇑(φ.invCutoffSchwartz j) =
      fun ξ ↦ (⇑(φ.invCutoffSchwartz 0)) (((2 : ℝ) ^ j)⁻¹ • ξ) :=
    funext fun ξ ↦ by
      rw [invCutoffSchwartz_apply, invCutoffSchwartz_apply, smul_smul, zpow_zero, one_mul,
        ← mul_inv, mul_comm (φ.rIn / 2)]
  rw [h, TauCeti.eLpNorm_fourierInv_comp_inv_smul _ (zpow_pos two_pos j)]
  simp

/-- The kernel `𝓕⁻ θ` is integrable, so its `L¹` norm is a finite constant. -/
private theorem coe_toNNReal_eLpNorm_fourierInv_invCutoffSchwartz :
    ((eLpNorm (𝓕⁻ ⇑(φ.invCutoffSchwartz 0)) 1 volume).toNNReal : ℝ≥0∞) =
      eLpNorm (𝓕⁻ ⇑(φ.invCutoffSchwartz 0)) 1 volume := by
  rw [← SchwartzMap.fourierInv_coe]
  exact ENNReal.coe_toNNReal ((𝓕⁻ (φ.invCutoffSchwartz 0)).memLp 1 volume).eLpNorm_ne_top

/-- The multiplier `Mⱼ` with symbol `θ(2^{-j} ·)`: on frequencies `‖ξ‖ ≈ 2^j` it is `2^j D⁻¹`. -/
private def invMultiplier (j : ℤ) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM ℂ ((φ.invCutoffSchwartz j).toLp ∞)

/-- `Mⱼ` is bounded on every `Lᵖ`, `1 ≤ p ≤ ∞`, uniformly in `j`. -/
private theorem eLpNorm_invMultiplier_le (j : ℤ) (f : Lp ℂ 2 (volume : Measure E))
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (φ.invMultiplier j f) p volume ≤
      eLpNorm (𝓕⁻ ⇑(φ.invCutoffSchwartz 0)) 1 volume * eLpNorm f p volume := by
  rw [← φ.eLpNorm_fourierInv_invCutoffSchwartz j]
  exact (φ.invCutoffSchwartz j).eLpNorm_fourierMultiplierCLM_toLp_le f hp

/-! ### The decomposition of `D⁻¹ sin(τD)` -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise form of `D⁻¹ sin(τD) = (2i)⁻¹ (W₊(τ) - W₊(-τ)) 2^{-j} Mⱼ` on the support of
`ψⱼ`. -/
private theorem waveSinSymbol_mul_eq {j : ℤ} (τ : ℝ) (ξ : E) {a : ℂ}
    (ha : φ.littlewoodPaley j ξ = 0 → a = 0) :
    waveSinSymbol τ ξ * a = (((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹ : ℂ) *
      (phaseSymbol sqrtNegLaplacianSymbol τ ξ * (a * φ.invCutoffSchwartz j ξ) -
        phaseSymbol sqrtNegLaplacianSymbol (-τ) ξ * (a * φ.invCutoffSchwartz j ξ)) := by
  by_cases h : φ.littlewoodPaley j ξ = 0
  · simp [ha h]
  have hkey := φ.inv_mul_invCutoffSchwartz_mul h
  have hs := sqrtNegLaplacianSymbol_mul_waveSinSymbol τ ξ
  have hph : phaseSymbol sqrtNegLaplacianSymbol τ ξ - phaseSymbol sqrtNegLaplacianSymbol (-τ) ξ =
      2 * Complex.I * Real.sin (τ * sqrtNegLaplacianSymbol ξ) := by
    rw [phaseSymbol_apply, phaseSymbol_apply, Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [neg_mul, Complex.cos_neg, Complex.sin_neg]
    ring
  have hc : (2 * Complex.I)⁻¹ * (2 * Complex.I) = 1 :=
    inv_mul_cancel₀ (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  push_cast at hkey ⊢
  linear_combination (-((2 : ℂ) ^ j)⁻¹ * (2 * Complex.I)⁻¹ * a *
      φ.invCutoffSchwartz j ξ) * hph -
    (((2 : ℂ) ^ j)⁻¹ * (Real.sin (τ * sqrtNegLaplacianSymbol ξ) : ℂ) * a *
      φ.invCutoffSchwartz j ξ) * hc +
    (((2 : ℂ) ^ j)⁻¹ * a * φ.invCutoffSchwartz j ξ) * hs -
    waveSinSymbol τ ξ * a * hkey

/-- `D⁻¹ sin(τD) T_k = 2^{-j} (2i)⁻¹ (W₊(τ) - W₊(-τ)) T_k Mⱼ` for every multiplier `T_k` whose
symbol vanishes off the support of `ψⱼ`. -/
private theorem waveSinPropagator_fourierMultiplierCLM_eq {j : ℤ} {k : Lp ℂ ∞ (volume : Measure E)}
    (hk : ∀ᵐ ξ ∂volume, φ.littlewoodPaley j ξ = 0 → k ξ = 0) (τ : ℝ)
    (f : Lp ℂ 2 (volume : Measure E)) :
    waveSinPropagator ℂ τ (Lp.fourierMultiplierCLM ℂ k f) =
      (((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹ : ℂ) •
        (halfWavePropagator ℂ τ (Lp.fourierMultiplierCLM ℂ k (φ.invMultiplier j f)) -
          halfWavePropagator ℂ (-τ) (Lp.fourierMultiplierCLM ℂ k (φ.invMultiplier j f))) := by
  simp only [waveSinPropagator_def, phasePropagator_def, invMultiplier,
    Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply]
  rw [← sub_apply, ← Lp.fourierMultiplierCLM_sub,
    ← smul_apply, ← Lp.fourierMultiplierCLM_smul]
  congr 2
  set σ : Lp ℂ ∞ (volume : Measure E) := (φ.invCutoffSchwartz j).toLp ∞ volume with hσ
  set w := (memLp_waveSinSymbol (E := E) τ).toLp _ with hw
  set ep := (memLp_phaseSymbol (E := E) sqrtNegLaplacianSymbol τ).toLp _ with hep
  set em := (memLp_phaseSymbol (E := E) sqrtNegLaplacianSymbol (-τ)).toLp _ with hem
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := ∞) w k,
    Lp.coeFn_smul (((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹ : ℂ) (ep • k • σ - em • k • σ),
    Lp.coeFn_sub (ep • k • σ) (em • k • σ), Lp.coeFn_lpSMul (r := ∞) ep (k • σ),
    Lp.coeFn_lpSMul (r := ∞) em (k • σ), Lp.coeFn_lpSMul (r := ∞) k σ,
    (memLp_waveSinSymbol (E := E) τ).coeFn_toLp,
    (memLp_phaseSymbol (E := E) sqrtNegLaplacianSymbol τ).coeFn_toLp,
    (memLp_phaseSymbol (E := E) sqrtNegLaplacianSymbol (-τ)).coeFn_toLp,
    (φ.invCutoffSchwartz j).coeFn_toLp ∞ volume, hk] with ξ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁
  rw [← hw] at h₇
  rw [← hep] at h₈
  rw [← hem] at h₉
  rw [← hσ] at h₁₀
  simp only [Pi.smul_apply', Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀]
  exact φ.waveSinSymbol_mul_eq τ ξ h₁₁

/-- `D⁻¹ sin(τD) Pⱼ = 2^{-j} (2i)⁻¹ (W₊(τ) - W₊(-τ)) Pⱼ Mⱼ`. -/
private theorem waveSinPropagator_littlewoodPaley_eq {j : ℤ} {m : Lp ℂ ∞ (volume : Measure E)}
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (τ : ℝ)
    (g : Lp ℂ 2 (volume : Measure E)) :
    waveSinPropagator ℂ τ (Lp.fourierMultiplierCLM ℂ m g) =
      (((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹ : ℂ) •
        (halfWavePropagator ℂ τ (Lp.fourierMultiplierCLM ℂ m (φ.invMultiplier j g)) -
          halfWavePropagator ℂ (-τ) (Lp.fourierMultiplierCLM ℂ m (φ.invMultiplier j g))) :=
  φ.waveSinPropagator_fourierMultiplierCLM_eq
    (hm.mono fun ξ h h0 ↦ by simp only [h, h0, Complex.ofReal_zero]) τ g

/-- `D⁻¹ sin(τD) Pⱼ Pⱼ = 2^{-j} (2i)⁻¹ (W₊(τ) - W₊(-τ)) Pⱼ Pⱼ Mⱼ`. -/
private theorem waveSinPropagator_littlewoodPaley_littlewoodPaley_eq {j : ℤ}
    {m : Lp ℂ ∞ (volume : Measure E)}
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (τ : ℝ)
    (g : Lp ℂ 2 (volume : Measure E)) :
    waveSinPropagator ℂ τ (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m g)) =
      (((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹ : ℂ) •
        (halfWavePropagator ℂ τ (Lp.fourierMultiplierCLM ℂ m
            (Lp.fourierMultiplierCLM ℂ m (φ.invMultiplier j g))) -
          halfWavePropagator ℂ (-τ) (Lp.fourierMultiplierCLM ℂ m
            (Lp.fourierMultiplierCLM ℂ m (φ.invMultiplier j g)))) := by
  have hk : ∀ᵐ ξ ∂volume, φ.littlewoodPaley j ξ = 0 →
      ((m • m : Lp ℂ ∞ (volume : Measure E)) : E → ℂ) ξ = 0 := by
    filter_upwards [Lp.coeFn_lpSMul (r := ∞) m m, hm] with ξ h₁ h₂ h
    rw [h₁, Pi.smul_apply', h₂, h, Complex.ofReal_zero, zero_smul]
  simp only [Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply]
  exact φ.waveSinPropagator_fourierMultiplierCLM_eq hk τ g

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The constant `2^{-j} (2i)⁻¹` of the decomposition of `D⁻¹ sin(τD)`, counted twice, is
`2^{-j}`. -/
private theorem enorm_two_zpow_inv_mul_two_mul_I_inv_mul_two (j : ℤ) :
    ‖(((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹ : ℂ)‖ₑ * 2 = ENNReal.ofReal (((2 : ℝ) ^ j)⁻¹) := by
  have hnorm : ‖(((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹ : ℂ)‖ = ((2 : ℝ) ^ j)⁻¹ * 2⁻¹ := by
    simp
  rw [← ofReal_norm, hnorm, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-! ### Measurability and reflection of time -/

/-- Joint measurability of the pairings `(t, s) ↦ ‖⟪W₊(τ(t, s)) T Y(s), G(t)⟫‖`. -/
private theorem aemeasurable_enorm_inner_halfWavePropagator {τ : ℝ × ℝ → ℝ} (hτ : Continuous τ)
    (T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    {Y G : ℝ → Lp ℂ 2 (volume : Measure E)} (hY : AEStronglyMeasurable Y)
    (hG : AEStronglyMeasurable G) :
    AEMeasurable (fun z : ℝ × ℝ ↦ ‖⟪halfWavePropagator ℂ (τ z) (T (Y z.2)), G z.1⟫_ℂ‖ₑ)
      (volume.prod volume) :=
  ((aestronglyMeasurable_phasePropagator_apply sqrtNegLaplacianSymbol hτ.aestronglyMeasurable
    (T.continuous.comp_aestronglyMeasurable hY.comp_snd)).inner hG.comp_fst).eNorm

/-- Reflecting time, `t ↦ -t`, preserves mixed norms. -/
private theorem eLpNorm_eLpNorm_comp_neg {H : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hH : AEStronglyMeasurable H) {q r : ℝ≥0∞} :
    eLpNorm (fun t ↦ eLpNorm (H (-t)) r volume) q volume =
      eLpNorm (fun t ↦ eLpNorm (H t) r volume) q volume :=
  eLpNorm_comp_measurePreserving (g := fun t ↦ eLpNorm (H t) r volume)
    (hH.aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable
    (Measure.measurePreserving_neg (volume : Measure ℝ))

/-- The mixed norm of a family vanishing at every time is zero. -/
private theorem eLpNorm_eLpNorm_eq_zero {H : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hH : ∀ t, H t = 0) {q r : ℝ≥0∞} :
    eLpNorm (fun t ↦ eLpNorm (H t) r volume) q volume = 0 := by
  simp_rw [hH, eLpNorm_congr_ae (Lp.coeFn_zero ℂ 2 (volume : Measure E)), eLpNorm_zero,
    eLpNorm_fun_zero]

/-- A mixed norm controlled pointwise by `a (‖u(t)‖_r + ‖u(-t)‖_r)` is at most `2 a` times the
mixed norm of `u`, since reflecting time preserves the latter. -/
private theorem eLpNorm_eLpNorm_le_mul_two_mul {w u : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hw : AEStronglyMeasurable w) (hu : AEStronglyMeasurable u) {q r a : ℝ≥0∞} (hq : 1 ≤ q)
    (h : ∀ t, eLpNorm (w t) r volume ≤
      a * (eLpNorm (u t) r volume + eLpNorm (u (-t)) r volume)) :
    eLpNorm (fun t ↦ eLpNorm (w t) r volume) q volume ≤
      a * 2 * eLpNorm (fun t ↦ eLpNorm (u t) r volume) q volume := by
  have hU := (hu.aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable
  have hUn : AEStronglyMeasurable (fun t ↦ eLpNorm (u (-t)) r volume) :=
    hU.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
  calc _ ≤ eLpNorm (fun t ↦ a * (eLpNorm (u t) r volume + eLpNorm (u (-t)) r volume)) q volume :=
        eLpNorm_mono_eNorm (hw.aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable fun t ↦ by
          simpa only [eNorm_eq_self] using h t
    _ = a * eLpNorm (fun t ↦ eLpNorm (u t) r volume + eLpNorm (u (-t)) r volume) q volume :=
        eLpNorm_const_mul_ennreal (hU.add hUn)
    _ ≤ a * (eLpNorm (fun t ↦ eLpNorm (u t) r volume) q volume +
          eLpNorm (fun t ↦ eLpNorm (u (-t)) r volume) q volume) := by
        gcongr
        exact eLpNorm_add_le hq
    _ = _ := by
        rw [eLpNorm_eLpNorm_comp_neg hu]
        ring

/-- Reflecting time turns a bilinear bound for the pairings `⟪W₊(t - s) T F(s), G(t)⟫` into the
same bound for `⟪W₊(-(t - s)) T F(s), G(t)⟫`: substitute `(t, s) ↦ (-t, -s)` and use that the
mixed norms are invariant under `s ↦ -s`. -/
private theorem lintegral_lintegral_enorm_inner_halfWavePropagator_neg_sub_le
    (T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) {p r : ℝ≥0∞} {X : ℝ≥0∞}
    (h : ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      AEStronglyMeasurable G →
        ∫⁻ t, ∫⁻ s, ‖⟪halfWavePropagator ℂ (t - s) (T (F s)), G t⟫_ℂ‖ₑ ≤
          X * eLpNorm (fun s ↦ eLpNorm (F s) r volume) p volume *
            eLpNorm (fun t ↦ eLpNorm (G t) r volume) p volume)
    {F G : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : AEStronglyMeasurable F)
    (hG : AEStronglyMeasurable G) :
    ∫⁻ t, ∫⁻ s, ‖⟪halfWavePropagator ℂ (-(t - s)) (T (F s)), G t⟫_ℂ‖ₑ ≤
      X * eLpNorm (fun s ↦ eLpNorm (F s) r volume) p volume *
        eLpNorm (fun t ↦ eLpNorm (G t) r volume) p volume := by
  have hneg := Measure.measurePreserving_neg (volume : Measure ℝ)
  calc _ = ∫⁻ t, ∫⁻ s, ‖⟪halfWavePropagator ℂ (-(-t - -s)) (T (F (-s))), G (-t)⟫_ℂ‖ₑ := by
        rw [← lintegral_neg_eq_self]
        exact lintegral_congr fun t ↦ (lintegral_neg_eq_self _).symm
    _ = ∫⁻ t, ∫⁻ s, ‖⟪halfWavePropagator ℂ (t - s) (T (F (-s))), G (-t)⟫_ℂ‖ₑ := by
        simp only [neg_sub_neg, neg_sub]
    _ ≤ _ := h _ _ (hF.comp_measurePreserving hneg) (hG.comp_measurePreserving hneg)
    _ = _ := by rw [eLpNorm_eLpNorm_comp_neg hF, eLpNorm_eLpNorm_comp_neg hG]

/-- If the pairings `⟪W₊(t - s) T F(s), G(t)⟫` satisfy a bilinear bound with constant `X`, then
those of `c (W₊(t - s) - W₊(-(t - s))) T F(s)` satisfy it with constant `2 ‖c‖ X`. -/
private theorem lintegral_lintegral_enorm_inner_smul_halfWavePropagator_sub_le
    (T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) (c : ℂ)
    {p r X : ℝ≥0∞}
    (h : ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      AEStronglyMeasurable G →
        ∫⁻ t, ∫⁻ s, ‖⟪halfWavePropagator ℂ (t - s) (T (F s)), G t⟫_ℂ‖ₑ ≤
          X * eLpNorm (fun s ↦ eLpNorm (F s) r volume) p volume *
            eLpNorm (fun t ↦ eLpNorm (G t) r volume) p volume)
    {F G : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : AEStronglyMeasurable F)
    (hG : AEStronglyMeasurable G) :
    ∫⁻ t, ∫⁻ s, ‖⟪c • (halfWavePropagator ℂ (t - s) (T (F s)) -
        halfWavePropagator ℂ (-(t - s)) (T (F s))), G t⟫_ℂ‖ₑ ≤
      ‖c‖ₑ * 2 * (X * eLpNorm (fun s ↦ eLpNorm (F s) r volume) p volume *
        eLpNorm (fun t ↦ eLpNorm (G t) r volume) p volume) := by
  set A : ℝ → ℝ → ℝ≥0∞ := fun t s ↦ ‖⟪halfWavePropagator ℂ (t - s) (T (F s)), G t⟫_ℂ‖ₑ
  set B : ℝ → ℝ → ℝ≥0∞ := fun t s ↦ ‖⟪halfWavePropagator ℂ (-(t - s)) (T (F s)), G t⟫_ℂ‖ₑ
  have hAm : AEMeasurable (fun z : ℝ × ℝ ↦ A z.1 z.2) (volume.prod volume) :=
    aemeasurable_enorm_inner_halfWavePropagator (τ := fun z ↦ z.1 - z.2) (by fun_prop) T hF hG
  have hBm : AEMeasurable (fun z : ℝ × ℝ ↦ B z.1 z.2) (volume.prod volume) :=
    aemeasurable_enorm_inner_halfWavePropagator (τ := fun z ↦ -(z.1 - z.2)) (by fun_prop) T hF hG
  calc _ ≤ ∫⁻ t, ∫⁻ s, ‖c‖ₑ * (A t s + B t s) :=
        lintegral_mono fun t ↦ lintegral_mono fun s ↦ by
          rw [inner_smul_left, inner_sub_left, eNorm_mul, RCLike.eNorm_conj]
          gcongr
          exact eNorm_sub_le
    _ = ‖c‖ₑ * ((∫⁻ t, ∫⁻ s, A t s) + ∫⁻ t, ∫⁻ s, B t s) := by
        simp_rw [lintegral_const_mul' _ _ eNorm_ne_top]
        rw [← lintegral_prod (fun z ↦ A z.1 z.2 + B z.1 z.2) (hAm.add hBm),
          lintegral_add_left' hAm, lintegral_prod _ hAm, lintegral_prod _ hBm]
    _ ≤ ‖c‖ₑ * (X * eLpNorm (fun s ↦ eLpNorm (F s) r volume) p volume *
          eLpNorm (fun t ↦ eLpNorm (G t) r volume) p volume +
          X * eLpNorm (fun s ↦ eLpNorm (F s) r volume) p volume *
          eLpNorm (fun t ↦ eLpNorm (G t) r volume) p volume) := by
        gcongr
        · exact h F G hF hG
        · exact lintegral_lintegral_enorm_inner_halfWavePropagator_neg_sub_le T h hF hG
    _ = _ := by ring

/-- The integrand `s ↦ c (W₊(t - s) - W₊(-(t - s))) Z(s)` of the decomposed Duhamel integral is
integrable when `Z` is. -/
private theorem integrable_smul_halfWavePropagator_sub {Z : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hZ : Integrable Z) (c : ℂ) (t : ℝ) :
    Integrable fun s ↦ c • (halfWavePropagator ℂ (t - s) (Z s) -
      halfWavePropagator ℂ (-(t - s)) (Z s)) := by
  exact ((integrable_phasePropagator_apply _ (continuous_sub_left t).aestronglyMeasurable hZ).sub
    (integrable_phasePropagator_apply _ (continuous_sub_left t).neg.aestronglyMeasurable
      hZ)).smul c

/-- The retarded integral `t ↦ ∫_{s < t} c (W₊(t - s) - W₊(-(t - s))) Z(s) ds` is almost
everywhere strongly measurable when `Z` is integrable. -/
private theorem aestronglyMeasurable_setIntegral_Iio_smul_halfWavePropagator_sub
    {Z : ℝ → Lp ℂ 2 (volume : Measure E)} (hZ : Integrable Z) (c : ℂ) :
    AEStronglyMeasurable fun t ↦ ∫ s in Set.Iio t, c • (halfWavePropagator ℂ (t - s) (Z s) -
      halfWavePropagator ℂ (-(t - s)) (Z s)) := by
  have heq : (fun t ↦ ∫ s in Set.Iio t, c • (halfWavePropagator ℂ (t - s) (Z s) -
      halfWavePropagator ℂ (-(t - s)) (Z s))) =
      fun t ↦ c • ((∫ s in Set.Iio t, halfWavePropagator ℂ (t - s) (Z s)) -
        ∫ s in Set.Iio t, phasePropagator ℂ (-sqrtNegLaplacianSymbol) (t - s) (Z s)) := by
    funext t
    rw [integral_smul, integral_sub
      (integrable_phasePropagator_apply sqrtNegLaplacianSymbol (τ := fun s ↦ t - s)
        (continuous_sub_left t).aestronglyMeasurable hZ).integrableOn
      (integrable_phasePropagator_apply sqrtNegLaplacianSymbol (τ := fun s ↦ -(t - s))
        (continuous_sub_left t).neg.aestronglyMeasurable hZ).integrableOn]
    simp_rw [halfWavePropagator_neg]
  rw [heq]
  exact ((aestronglyMeasurable_setIntegral_Iio_phasePropagator_sub _ hZ.aestronglyMeasurable).sub
    (aestronglyMeasurable_setIntegral_Iio_phasePropagator_sub _
      hZ.aestronglyMeasurable)).const_smul c

/-! ### Mixed-norm estimates -/

section Admissible

variable {p q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- **The Strichartz estimate for the frequency-localized half-wave propagator** in mixed norm.
Let `E` have dimension `n`, let `Pⱼ` be the `L²` Fourier multiplier with the Littlewood–Paley
cutoff `ψⱼ` built from `φ` as symbol, and let `(q, r)` be wave-admissible,
`2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞`, and `p` the Hölder conjugate
of `q`. With `γ = n / 2 - n / r - 1 / q` there is `C` such that for every `j ∈ ℤ` and every
`f ∈ L²(E)`,

`‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{jγ} ‖f‖₂`. -/
theorem exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f)) r
            volume) q volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) * ‖f‖ₑ := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ _ ↦ by simp [eLpNorm_exponent_zero, Lp.aestronglyMeasurable]⟩
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hE | hE
  · -- In dimension `0` the blocks vanish.
    exact ⟨0, fun j m hm f ↦ (eLpNorm_eLpNorm_eq_zero fun t ↦ by
      rw [φ.fourierMultiplierCLM_littlewoodPaley_eq_zero_of_finrank_eq_zero hm hE, zero_apply,
        map_zero]).trans_le zero_le⟩
  obtain ⟨-, -, hr2⟩ := two_le_finrank_of_waveAdmissible hq hr0 hqr hE
  -- Test against `L^{r'}` with `r'` the Hölder conjugate of `r`.
  have hrr := ENNReal.HolderConjugate.inv_one_sub_inv' (one_le_two.trans hr2)
  obtain ⟨C, hC⟩ := φ.exists_enorm_integral_inner_halfWavePropagator_littlewoodPaley_le
    (r' := (1 - r⁻¹)⁻¹) hq hpq hqr
  have := hpq.symm.coe_ennreal
  exact ⟨C, fun j m hm f ↦ (continuous_phasePropagator_apply _ _).aestronglyMeasurable
    |>.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℂ) (q' := p)
      (r' := (1 - r⁻¹)⁻¹) ENNReal.coe_ne_top hr2 fun G hG _ ↦
        hC j m hm f G hG.aestronglyMeasurable
          (integrable_phasePropagator_apply _ continuous_neg.aestronglyMeasurable
            ((Lp.fourierMultiplierCLM ℂ m).integrable_comp hG))⟩

/-- **The Strichartz estimate for the frequency-localized `cos(tD)`** in mixed norm. Under the
hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le`, there is `C` such
that for every `j ∈ ℤ` and every `f ∈ L²(E)`,

`‖cos(tD) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{jγ} ‖f‖₂`. -/
theorem exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f)) r
            volume) q volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) * ‖f‖ₑ := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le hq hpq hqr
  refine ⟨C * (ENNReal.LpAddConst r).toNNReal, fun j m hm f ↦ ?_⟩
  set u := fun t ↦ halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f)
  have hu : Continuous u := continuous_phasePropagator_apply _ _
  -- `cos(tD) = (W₊(t) + W₊(-t)) / 2`.
  have hpt (t : ℝ) : eLpNorm (waveCosPropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f)) r volume ≤
      ‖(2⁻¹ : ℂ)‖ₑ * ENNReal.LpAddConst r *
        (eLpNorm (u t) r volume + eLpNorm (u (-t)) r volume) := by
    rw [waveCosPropagator_eq_halfWavePropagator, smul_apply,
      eLpNorm_congr_ae (Lp.coeFn_smul _ _), eLpNorm_const_smul, add_apply,
      eLpNorm_congr_ae (Lp.coeFn_add _ _), mul_assoc]
    gcongr
    exact eLpNorm_add_le' r
  have h2 : ‖(2⁻¹ : ℂ)‖ₑ * 2 = 1 := by
    rw [← ofReal_norm, norm_inv, Complex.norm_two, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  calc _ ≤ ‖(2⁻¹ : ℂ)‖ₑ * ENNReal.LpAddConst r * 2 *
          eLpNorm (fun t ↦ eLpNorm (u t) r volume) q volume :=
        eLpNorm_eLpNorm_le_mul_two_mul (continuous_waveCosPropagator_apply _).aestronglyMeasurable
          hu.aestronglyMeasurable (by exact_mod_cast (one_le_two.trans hq.le)) hpt
    _ = ENNReal.LpAddConst r * eLpNorm (fun t ↦ eLpNorm (u t) r volume) q volume := by
        rw [mul_right_comm _ (ENNReal.LpAddConst r), h2, one_mul]
    _ ≤ _ := by
        grw [hC j m hm f, ENNReal.coe_mul, ENNReal.coe_toNNReal (ENNReal.LpAddConst_lt_top r).ne]
        exact le_of_eq (by ring)

/-- **The Strichartz estimate for the frequency-localized `D⁻¹ sin(tD)`** in mixed norm. Under the
hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le`, there is `C` such
that for every `j ∈ ℤ` and every `g ∈ L²(E)`,

`‖D⁻¹ sin(tD) Pⱼ g‖_{L^q_t L^r_x} ≤ C 2^{j(γ - 1)} ‖g‖₂`.

The extra factor `2^{-j}` is the size of `D⁻¹` at frequencies `‖ξ‖ ≈ 2^j`. -/
theorem exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ g : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveSinPropagator ℂ t (Lp.fourierMultiplierCLM ℂ m g)) r
            volume) q volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹ - 1)) * ‖g‖ₑ := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le hq hpq hqr
  set K := eLpNorm (𝓕⁻ ⇑(φ.invCutoffSchwartz 0)) 1 volume
  refine ⟨C * K.toNNReal * (ENNReal.LpAddConst r).toNNReal, fun j m hm g ↦ ?_⟩
  set γ := (Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹
  set c : ℂ := ((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹
  set u := fun t ↦ halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m (φ.invMultiplier j g))
  have hu : Continuous u := continuous_phasePropagator_apply _ _
  have hpt (t : ℝ) : eLpNorm (waveSinPropagator ℂ t (Lp.fourierMultiplierCLM ℂ m g)) r volume ≤
      ‖c‖ₑ * ENNReal.LpAddConst r * (eLpNorm (u t) r volume + eLpNorm (u (-t)) r volume) := by
    rw [φ.waveSinPropagator_littlewoodPaley_eq hm, eLpNorm_congr_ae (Lp.coeFn_smul _ _),
      eLpNorm_const_smul, eLpNorm_congr_ae (Lp.coeFn_sub _ _), mul_assoc]
    gcongr
    exact eLpNorm_sub_le' r
  have hMg : ‖φ.invMultiplier j g‖ₑ ≤ K * ‖g‖ₑ := by
    simpa only [Lp.eNorm_def] using φ.eLpNorm_invMultiplier_le j g one_le_two
  have hK : (K.toNNReal : ℝ≥0∞) = K := φ.coe_toNNReal_eLpNorm_fourierInv_invCutoffSchwartz
  have h2j : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  calc _ ≤ ‖c‖ₑ * ENNReal.LpAddConst r * 2 * eLpNorm (fun t ↦ eLpNorm (u t) r volume) q volume :=
        eLpNorm_eLpNorm_le_mul_two_mul (continuous_waveSinPropagator_apply _).aestronglyMeasurable
          hu.aestronglyMeasurable (by exact_mod_cast (one_le_two.trans hq.le)) hpt
    _ ≤ ‖c‖ₑ * 2 * ENNReal.LpAddConst r *
          (C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ γ) * (K * ‖g‖ₑ)) := by
        rw [mul_right_comm _ (ENNReal.LpAddConst r)]
        gcongr
        exact (hC j m hm _).trans (by gcongr)
    _ = _ := by
        rw [enorm_two_zpow_inv_mul_two_mul_I_inv_mul_two, ENNReal.coe_mul, ENNReal.coe_mul, hK,
          ENNReal.coe_toNNReal (ENNReal.LpAddConst_lt_top r).ne, Real.rpow_sub_one h2j.ne',
          div_eq_inv_mul, ENNReal.ofReal_mul (by positivity)]
        ring

/-- **The bilinear Strichartz estimate for the frequency-localized wave Duhamel operator.** Let
`E` have dimension `n`, let `Pⱼ` be the `L²` Fourier multiplier with the Littlewood–Paley cutoff
`ψⱼ` built from `φ` as symbol, let `(q, r)` be wave-admissible,
`2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates
of `q` and `r`, and let `γ = n / 2 - n / r - 1 / q`. There is `C` such that for every `j ∈ ℤ` and
all almost everywhere strongly measurable `F, G : ℝ → L²(E)`,

`∫∫ |⟪D⁻¹ sin((t - s)D) Pⱼ Pⱼ F(s), G(t)⟫| ds dt`
`  ≤ C 2^{j(2γ - 1)} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

This is the frequency-localized form of the Duhamel term of the wave equation
`∂ₜ²u - Δu = F`; the factor `2^{-j}` over the half-wave estimate is the size of `D⁻¹` at
frequencies `‖ξ‖ ≈ 2^j`. The bound controls the integral over any part of the `(s, t)` plane,
such as the retarded region `s < t`. -/
theorem exists_lintegral_lintegral_enorm_inner_waveSinPropagator_sub_littlewoodPaley_le
    (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F → AEStronglyMeasurable G →
        ∫⁻ t, ∫⁻ s, ‖⟪waveSinPropagator ℂ (t - s)
            (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹) - 1)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C, hC⟩ :=
    φ.exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_littlewoodPaley_le (r' := r')
      hq hpq hqr
  set K := eLpNorm (𝓕⁻ ⇑(φ.invCutoffSchwartz 0)) 1 volume
  refine ⟨C * K.toNNReal, fun j m hm F G hF hG ↦ ?_⟩
  set γ := (Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹
  set c : ℂ := ((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹
  set Y := fun s ↦ φ.invMultiplier j (F s)
  have hY : AEStronglyMeasurable Y := (φ.invMultiplier j).continuous.comp_aestronglyMeasurable hF
  -- `D⁻¹ sin(τD) Pⱼ Pⱼ = c (W₊(τ) - W₊(-τ)) Pⱼ Pⱼ Mⱼ`, and the half-wave estimate applies to
  -- both halves.
  have hsplit := lintegral_lintegral_enorm_inner_smul_halfWavePropagator_sub_le
    (Lp.fourierMultiplierCLM ℂ m ∘L Lp.fourierMultiplierCLM ℂ m) c
    (fun F G hF hG ↦ hC j m hm F G hF hG) hY hG
  simp only [ContinuousLinearMap.comp_apply] at hsplit
  simp_rw [φ.waveSinPropagator_littlewoodPaley_littlewoodPaley_eq hm]
  -- `Mⱼ` costs a constant factor in the mixed norm.
  have hYF : eLpNorm (fun s ↦ eLpNorm (Y s) r' volume) p volume ≤
      K * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume := by
    calc _ ≤ eLpNorm (fun s ↦ K * eLpNorm (F s) r' volume) p volume :=
          eLpNorm_mono_eNorm (hY.aemeasurable_eLpNorm_Lp .rfl r').aestronglyMeasurable fun s ↦ by
            simpa only [eNorm_eq_self] using
              φ.eLpNorm_invMultiplier_le j (F s) (ENNReal.HolderConjugate.one_le r' r)
      _ = _ := eLpNorm_const_mul_ennreal_of_pos (by exact_mod_cast hpq.pos)
  have hK : (K.toNNReal : ℝ≥0∞) = K := φ.coe_toNNReal_eLpNorm_fourierInv_invCutoffSchwartz
  have h2j : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  calc _ ≤ _ := hsplit
    _ ≤ ‖c‖ₑ * 2 * (C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * γ)) *
          (K * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume) *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume) := by
        gcongr
    _ = _ := by
        rw [enorm_two_zpow_inv_mul_two_mul_I_inv_mul_two, ENNReal.coe_mul, hK,
          Real.rpow_sub_one h2j.ne', div_eq_inv_mul, ENNReal.ofReal_mul (by positivity)]
        ring

/-- **The retarded Strichartz estimate for the frequency-localized wave Duhamel operator** in
mixed norm. Under the hypotheses of
`ContDiffBump.exists_lintegral_lintegral_enorm_inner_waveSinPropagator_sub_littlewoodPaley_le`,
there is `C` such that for every `j ∈ ℤ` and every forcing term `F : ℝ → L²(E)`
that is integrable in time,

`‖∫_{s < t} D⁻¹ sin((t - s)D) Pⱼ Pⱼ F(s) ds‖_{L^q_t L^r_x} ≤ C 2^{j(2γ - 1)} ‖F‖_{L^p_t L^{r'}_x}`.
-/
theorem exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le
    (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
            (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))) :
              Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹) - 1)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume := by
  obtain ⟨C, hC⟩ :=
    φ.exists_lintegral_lintegral_enorm_inner_waveSinPropagator_sub_littlewoodPaley_le (r' := r')
      hq hpq hqr
  refine ⟨C, fun j m hm F hF ↦ ?_⟩
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hE | hE
  · refine (eLpNorm_eLpNorm_eq_zero fun t ↦ ?_).trans_le zero_le
    simp_rw [φ.fourierMultiplierCLM_littlewoodPaley_eq_zero_of_finrank_eq_zero hm hE, zero_apply,
      map_zero, integral_zero]
  obtain ⟨-, -, hr2⟩ :=
    two_le_finrank_of_waveAdmissible hq (ENNReal.HolderConjugate.ne_zero r r') hqr hE
  set c : ℂ := ((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹
  set Z := fun s ↦ Lp.fourierMultiplierCLM ℂ m
    (Lp.fourierMultiplierCLM ℂ m (φ.invMultiplier j (F s)))
  have hZ : Integrable Z := (Lp.fourierMultiplierCLM ℂ m).integrable_comp
    ((Lp.fourierMultiplierCLM ℂ m).integrable_comp ((φ.invMultiplier j).integrable_comp hF))
  have hid (t s : ℝ) : waveSinPropagator ℂ (t - s)
      (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))) =
      c • (halfWavePropagator ℂ (t - s) (Z s) - halfWavePropagator ℂ (-(t - s)) (Z s)) :=
    φ.waveSinPropagator_littlewoodPaley_littlewoodPaley_eq hm _ _
  have hint (t : ℝ) : Integrable fun s ↦ waveSinPropagator ℂ (t - s)
      (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))) := by
    simp_rw [hid]
    exact integrable_smul_halfWavePropagator_sub hZ c t
  have hΦ : AEStronglyMeasurable fun t ↦ ∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
      (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))) := by
    simp_rw [hid]
    exact aestronglyMeasurable_setIntegral_Iio_smul_halfWavePropagator_sub hZ c
  have := hpq.symm.coe_ennreal
  refine hΦ.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℂ) (q' := p) (r' := r')
    ENNReal.coe_ne_top hr2 fun G hG _ ↦ ?_
  -- Move the pairing with `G t` inside the integral over `s < t`.
  have hpair (t : ℝ) : ⟪(∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
      (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))) :
        Lp ℂ 2 (volume : Measure E)), G t⟫_ℂ =
      ∫ s in Set.Iio t, ⟪waveSinPropagator ℂ (t - s)
        (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ := by
    rw [← inner_conj_symm, ← integral_inner (hint t).integrableOn, ← integral_conj]
    simp_rw [inner_conj_symm]
  simp_rw [hpair]
  exact (enorm_integral_setIntegral_Iio_le_lintegral_lintegral_enorm _).trans
    (hC j m hm F G hF.aestronglyMeasurable hG.aestronglyMeasurable)

end Admissible

end ContDiffBump

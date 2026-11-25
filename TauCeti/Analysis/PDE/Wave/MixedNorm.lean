/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.Propagator
public import TauCeti.Analysis.PDE.Wave.Strichartz
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Analysis.PDE.Strichartz.Retarded
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.Lp.MixedNorm
import TauCeti.MeasureTheory.Function.Lp.MixedNorm.Bounded
import TauCeti.MeasureTheory.Function.Lp.Star

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
* `‖∫_{s < t} D⁻¹ sin((t - s)D) Pⱼ Pⱼ F(s) ds‖_{L^q_t L^r_x} ≤ C 2^{j(γ + γ₁ - 1)}
  ‖F‖_{L^{p₁}_t L^{r₁'}_x}` for forcing terms `F : ℝ → L²(E)` integrable in time, measured along
  a second wave-admissible pair `(q₁, r₁)` with `2 < q₁ ≤ ∞`, Hölder conjugates `p₁` and `r₁'`,
  and `γ₁ = n / 2 - n / r₁ - 1 / q₁`.

For a single pair the Duhamel pairings also satisfy the bilinear estimate
`∫∫ |⟪D⁻¹ sin((t - s)D) Pⱼ Pⱼ F(s), G(t)⟫| ds dt ≤ C 2^{j(2γ - 1)} ‖F‖_{L^p_t L^{r'}_x}
‖G‖_{L^p_t L^{r'}_x}`. The factor `2^{-j}` gained over the
half-wave estimates is the size of `D⁻¹` at frequencies `‖ξ‖ ≈ 2^j`. These are the
frequency-localized estimates from which the Strichartz estimates for the inhomogeneous wave
equation, with data and forcing in homogeneous Besov classes, are assembled by Littlewood–Paley
summation.

## The argument

The symbol `1 / (2π ‖·‖)` is smooth away from the origin, so it agrees on the annulus
`φ.rIn / 2 ≤ ‖ξ‖ ≤ φ.rOut`, which contains the support of `ψ₀`, with a Schwartz function `θ`
(`ContDiffBump.exists_eqOn_inv_of_contDiffOn`). Let `Mⱼ` be the multiplier with symbol
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

With two different pairs the Duhamel pairings are no longer controlled in absolute value. Without
the restriction `s < t` the pairing of `W₊(t - s) Pⱼ Pⱼ F(s)` with `G(t)` factors as
`⟪∫ W₊(-s) Pⱼ F(s) ds, ∫ W₊(-t) Pⱼ G(t) dt⟫`, which the dual estimates for the two pairs bound,
and the Christ–Kiselev lemma passes the bound to the retarded region
(`TauCeti.enorm_integral_setIntegral_Iio_inner_adjoint_le`), since `q₁' < 2 < q`. The `W₊(-τ)`
halves use the same argument for the operators `W₊(-t) Pⱼ`, whose dual estimates follow by
reversing time (`TauCeti.enorm_integral_adjoint_neg_le`).

## Main declarations

All in the `ContDiffBump` namespace, with `φ` the bump function defining the cutoffs.

* `exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le`: the estimate for `W₊(t) Pⱼ`.
* `exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le`: the estimate for `cos(tD) Pⱼ`.
* `exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le`: the estimate for
  `D⁻¹ sin(tD) Pⱼ`.
* `exists_lintegral_lintegral_enorm_inner_waveSinPropagator_sub_littlewoodPaley_le`: the bilinear
  estimate for the Duhamel pairings.
* `exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le`: the retarded
  estimate for the Duhamel integral, with the forcing measured along a second admissible pair.

The file also proves `TauCeti.eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le`, which
combines mixed-norm bounds for `cos(tD) f` and `D⁻¹ sin(tD) g` into one for the free solution
`cos(tD) f + D⁻¹ sin(tD) g`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3 (Theorem 2.6 and its proof).
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
* M. Christ and A. Kiselev, *Maximal functions associated to filtrations*, J. Funct. Anal. 179
  (2001), 409–425.
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
  refine φ.exists_eqOn_inv_of_contDiffOn (fun η hη ↦ ?_) fun η hη ↦ ?_
  · rw [show ⇑(sqrtNegLaplacianSymbol (E := E)) = fun ξ ↦ 2 * Real.pi * ‖ξ‖ from
      funext sqrtNegLaplacianSymbol_apply]
    exact (contDiffAt_const.mul (contDiffAt_norm ℝ hη)).contDiffWithinAt
  · rw [sqrtNegLaplacianSymbol_apply]
    have := norm_pos_iff.2 hη
    positivity

/-- The Schwartz function `θ₀` of `exists_invCutoff`. Its dyadic dilates `θ(2^{-j} ·)`
(`ContDiffBump.dyadicDilate`) equal `2^j / (2π ‖·‖)` on the annulus
`2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut` containing the support of `ψⱼ`, and the dyadic multiplier `Mⱼ`
with symbol `θ(2^{-j} ·)` is `2^j D⁻¹` at frequencies `‖ξ‖ ≈ 2^j`. -/
private def invCutoff : 𝓢(E, ℂ) :=
  φ.exists_invCutoff.choose

/-- `θ₀` equals `1 / (2π ‖(φ.rIn / 2) • η‖)` on the annulus `1 ≤ ‖η‖ ≤ 2 φ.rOut / φ.rIn`. -/
private theorem eqOn_invCutoff : Set.EqOn φ.invCutoff
    (fun η ↦ (((sqrtNegLaplacianSymbol ((φ.rIn / 2) • η))⁻¹ : ℝ) : ℂ))
    {η | 1 ≤ ‖η‖ ∧ ‖η‖ ≤ 2 * φ.rOut / φ.rIn} :=
  φ.exists_invCutoff.choose_spec

/-- On the support of `ψⱼ`, `2^{-j} θ(2^{-j} ξ)` inverts the symbol `2π ‖ξ‖` of `D`. -/
private theorem inv_mul_dyadicDilate_invCutoff_mul {j : ℤ} {ξ : E}
    (hξ : φ.littlewoodPaley j ξ ≠ 0) :
    (((2 : ℝ) ^ j)⁻¹ : ℂ) * φ.dyadicDilate φ.invCutoff j ξ * (sqrtNegLaplacianSymbol ξ : ℂ) =
      1 := by
  have h2j : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  have hξ0 : (‖ξ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 fun h ↦
    hξ (h ▸ φ.littlewoodPaley_apply_zero j))
  rw [φ.dyadicDilate_apply_of_littlewoodPaley_ne_zero φ.eqOn_invCutoff hξ,
    sqrtNegLaplacianSymbol_apply,
    sqrtNegLaplacianSymbol_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 h2j.le)]
  push_cast
  field_simp

variable [MeasurableSpace E] [BorelSpace E]

/-! ### The decomposition of `D⁻¹ sin(τD)` -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise form of `D⁻¹ sin(τD) = (2i)⁻¹ (W₊(τ) - W₊(-τ)) 2^{-j} Mⱼ` on the support of
`ψⱼ`. -/
private theorem waveSinSymbol_mul_eq {j : ℤ} (τ : ℝ) (ξ : E) {a : ℂ}
    (ha : φ.littlewoodPaley j ξ = 0 → a = 0) :
    waveSinSymbol τ ξ * a = (((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹ : ℂ) *
      (phaseSymbol sqrtNegLaplacianSymbol τ ξ * (a * φ.dyadicDilate φ.invCutoff j ξ) -
        phaseSymbol sqrtNegLaplacianSymbol (-τ) ξ * (a * φ.dyadicDilate φ.invCutoff j ξ)) := by
  by_cases h : φ.littlewoodPaley j ξ = 0
  · simp [ha h]
  have hkey := φ.inv_mul_dyadicDilate_invCutoff_mul h
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
      φ.dyadicDilate φ.invCutoff j ξ) * hph -
    (((2 : ℂ) ^ j)⁻¹ * (Real.sin (τ * sqrtNegLaplacianSymbol ξ) : ℂ) * a *
      φ.dyadicDilate φ.invCutoff j ξ) * hc +
    (((2 : ℂ) ^ j)⁻¹ * a * φ.dyadicDilate φ.invCutoff j ξ) * hs -
    waveSinSymbol τ ξ * a * hkey

/-- `D⁻¹ sin(τD) T_k = 2^{-j} (2i)⁻¹ (W₊(τ) - W₊(-τ)) T_k Mⱼ` for every multiplier `T_k` whose
symbol vanishes off the support of `ψⱼ`. -/
private theorem waveSinPropagator_fourierMultiplierCLM_eq {j : ℤ} {k : Lp ℂ ∞ (volume : Measure E)}
    (hk : ∀ᵐ ξ ∂volume, φ.littlewoodPaley j ξ = 0 → k ξ = 0) (τ : ℝ)
    (f : Lp ℂ 2 (volume : Measure E)) :
    waveSinPropagator ℂ τ (Lp.fourierMultiplierCLM ℂ k f) =
      (((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹ : ℂ) •
        (halfWavePropagator ℂ τ
            (Lp.fourierMultiplierCLM ℂ k (φ.dyadicMultiplier ℂ φ.invCutoff j f)) -
          halfWavePropagator ℂ (-τ)
            (Lp.fourierMultiplierCLM ℂ k (φ.dyadicMultiplier ℂ φ.invCutoff j f))) := by
  simp only [waveSinPropagator_def, phasePropagator_def, dyadicMultiplier_def,
    Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply]
  rw [← sub_apply, ← Lp.fourierMultiplierCLM_sub,
    ← smul_apply, ← Lp.fourierMultiplierCLM_smul]
  congr 2
  set σ : Lp ℂ ∞ (volume : Measure E) := (φ.dyadicDilate φ.invCutoff j).toLp ∞ volume with hσ
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
    (φ.dyadicDilate φ.invCutoff j).coeFn_toLp ∞ volume, hk]
    with ξ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁
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
        (halfWavePropagator ℂ τ
            (Lp.fourierMultiplierCLM ℂ m (φ.dyadicMultiplier ℂ φ.invCutoff j g)) -
          halfWavePropagator ℂ (-τ)
            (Lp.fourierMultiplierCLM ℂ m (φ.dyadicMultiplier ℂ φ.invCutoff j g))) :=
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
            (Lp.fourierMultiplierCLM ℂ m (φ.dyadicMultiplier ℂ φ.invCutoff j g))) -
          halfWavePropagator ℂ (-τ) (Lp.fourierMultiplierCLM ℂ m
            (Lp.fourierMultiplierCLM ℂ m (φ.dyadicMultiplier ℂ φ.invCutoff j g)))) := by
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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The constant `2^{-j} (2i)⁻¹` of the decomposition of `D⁻¹ sin(τD)`, counted twice, lowers the
exponent of a power of `2^j` by `1`. -/
private theorem enorm_two_zpow_inv_mul_two_mul_I_inv_mul_two_mul_ofReal_rpow (j : ℤ) (a : ℝ) :
    ‖(((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹ : ℂ)‖ₑ * 2 * ENNReal.ofReal (((2 : ℝ) ^ j) ^ a) =
      ENNReal.ofReal (((2 : ℝ) ^ j) ^ (a - 1)) := by
  rw [enorm_two_zpow_inv_mul_two_mul_I_inv_mul_two, ← ENNReal.ofReal_mul (by positivity),
    Real.rpow_sub_one (zpow_pos two_pos j).ne', div_eq_inv_mul]

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
        rw [hu.eLpNorm_eLpNorm_comp_neg]
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
    _ = _ := by rw [hF.eLpNorm_eLpNorm_comp_neg, hG.eLpNorm_eLpNorm_comp_neg]

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

/-! ### Retarded pairings -/

/-- The retarded Duhamel integral of `D⁻¹ sin` splits along
`D⁻¹ sin(τD) Pⱼ Pⱼ = 2^{-j} (2i)⁻¹ (W₊(τ) - W₋(τ)) Pⱼ Pⱼ Mⱼ`, where `W₋(τ) = W₊(-τ)` is the
phase propagator with the phase `-2π ‖·‖`. -/
private theorem setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_eq {j : ℤ}
    {m : Lp ℂ ∞ (volume : Measure E)} (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    {F : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : Integrable F) (t : ℝ) :
    ∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
        (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))) =
      (((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹ : ℂ) •
        ((∫ s in Set.Iio t, halfWavePropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ m
            (Lp.fourierMultiplierCLM ℂ m (φ.dyadicMultiplier ℂ φ.invCutoff j (F s))))) -
          ∫ s in Set.Iio t, phasePropagator ℂ (-sqrtNegLaplacianSymbol) (t - s)
            (Lp.fourierMultiplierCLM ℂ m
              (Lp.fourierMultiplierCLM ℂ m (φ.dyadicMultiplier ℂ φ.invCutoff j (F s))))) := by
  have hZ := (Lp.fourierMultiplierCLM ℂ m).integrable_comp
    ((Lp.fourierMultiplierCLM ℂ m).integrable_comp
      ((φ.dyadicMultiplier ℂ φ.invCutoff j).integrable_comp hF))
  simp_rw [φ.waveSinPropagator_littlewoodPaley_littlewoodPaley_eq hm, halfWavePropagator_neg]
  rw [integral_smul, integral_sub
    (integrable_phasePropagator_apply _ (continuous_sub_left t).aestronglyMeasurable
      hZ).integrableOn
    (integrable_phasePropagator_apply _ (continuous_sub_left t).aestronglyMeasurable
      hZ).integrableOn]

/-- The pairing of the retarded Duhamel integral of `D⁻¹ sin` with an integrable `G` is
`conj (2^{-j} (2i)⁻¹)` times the difference of the retarded pairings of its two half-wave parts. -/
private theorem integral_inner_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_eq {j : ℤ}
    {m : Lp ℂ ∞ (volume : Measure E)} (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    {F G : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : Integrable F) (hG : Integrable G) :
    ∫ t, ⟪∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
        (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ =
      (starRingEnd ℂ) (((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹ : ℂ) *
        ((∫ t, ∫ s in Set.Iio t, ⟪halfWavePropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ m
            (Lp.fourierMultiplierCLM ℂ m (φ.dyadicMultiplier ℂ φ.invCutoff j (F s)))), G t⟫_ℂ) -
          ∫ t, ∫ s in Set.Iio t, ⟪halfWavePropagator ℂ (-(t - s)) (Lp.fourierMultiplierCLM ℂ m
            (Lp.fourierMultiplierCLM ℂ m (φ.dyadicMultiplier ℂ φ.invCutoff j (F s)))), G t⟫_ℂ) := by
  have hZ := (Lp.fourierMultiplierCLM ℂ m).integrable_comp
    ((Lp.fourierMultiplierCLM ℂ m).integrable_comp
      ((φ.dyadicMultiplier ℂ φ.invCutoff j).integrable_comp hF))
  simp_rw [φ.setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_eq hm hF, inner_smul_left,
    inner_sub_left]
  rw [integral_const_mul, integral_sub
    (integrable_inner_setIntegral_Iio_phasePropagator_sub _ hZ hG)
    (integrable_inner_setIntegral_Iio_phasePropagator_sub _ hZ hG)]
  simp_rw [inner_setIntegral_Iio_phasePropagator_sub _ hZ, halfWavePropagator_neg]

/-- For integrable `F : ℝ → L²(E)` and every time `t`, the frequency-localized Duhamel integrand
`s ↦ D⁻¹ sin((t - s)D) Pⱼ F(s)` of the wave equation is integrable: at frequencies
`‖ξ‖ ≈ 2^j` the operators `D⁻¹ sin(τD)` are bounded uniformly in `τ`. -/
theorem integrable_waveSinPropagator_sub_littlewoodPaley {j : ℤ}
    {m : Lp ℂ ∞ (volume : Measure E)} (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    {F : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : Integrable F) (t : ℝ) :
    Integrable fun s ↦ waveSinPropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ m (F s)) := by
  have hZ := (Lp.fourierMultiplierCLM ℂ m).integrable_comp
    ((φ.dyadicMultiplier ℂ φ.invCutoff j).integrable_comp hF)
  simp_rw [φ.waveSinPropagator_littlewoodPaley_eq hm, halfWavePropagator_neg]
  exact Integrable.smul (((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹ : ℂ)
    ((integrable_phasePropagator_apply sqrtNegLaplacianSymbol
      (continuous_sub_left t).aestronglyMeasurable hZ).sub (integrable_phasePropagator_apply
        (-sqrtNegLaplacianSymbol) (continuous_sub_left t).aestronglyMeasurable hZ))

/-! ### Two admissible pairs for the half-wave propagators

With the forcing measured along a second wave-admissible pair, the retarded estimates for the
half-wave propagators no longer follow from a bound on the absolute values of the Duhamel
pairings. The untruncated pairing factors through the dual estimates of the two pairs, and the
Christ–Kiselev lemma passes the bound to the retarded region `s < t`
(`TauCeti.enorm_integral_setIntegral_Iio_inner_adjoint_le`). The time exponents are extended
reals, so that the pairs `(∞, r)` are included. -/

section TwoPairs

/-- The dual estimate along a wave-admissible pair `(q, r)` with `2 < q ≤ ∞` and `r ≥ 2`, for the
Hölder conjugate `p` of `q`: the finite-`q` estimate
`ContDiffBump.exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le` and the estimate
at `q = ∞` in one statement. -/
private theorem exists_enorm_integral_halfWavePropagator_neg_le_of_two_lt {p q r r' : ℝ≥0∞}
    [p.HolderConjugate q] [r'.HolderConjugate r] (hq : 2 < q) (hr : 2 ≤ r)
    (hqr : 2 * (q⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
        ‖∫ s, halfWavePropagator ℂ (-s) (Lp.fourierMultiplierCLM ℂ m (F s))‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume := by
  rcases eq_or_ne q ⊤ with rfl | hqtop
  · -- At `q = ∞` the time exponent is `p = 1`.
    obtain rfl : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ p).1 rfl
    obtain ⟨C, hC⟩ :=
      φ.exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le_eLpNorm_one (r' := r') hr
    exact ⟨C, fun j m hm F hF ↦ by simpa using hC j m hm F hF⟩
  -- For `q < ∞` pass to the real exponents `q.toNNReal` and `p.toNNReal`.
  obtain ⟨hq2, hqr⟩ := waveAdmissible_toNNReal hq hqtop hqr
  have hptop : p ≠ ⊤ :=
    (ENNReal.HolderConjugate.ne_top_iff_ne_one p q).2 (ENNReal.one_lt_two.trans hq).ne'
  have hpq : p.toNNReal.HolderConjugate q.toNNReal :=
    (ENNReal.HolderConjugate.toNNReal (p := q) (q := p) (one_lt_two.trans hq2)).symm
  obtain ⟨C, hC⟩ :=
    φ.exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le (r' := r') hq2 hpq hqr
  refine ⟨C, fun j m hm F hF ↦ ?_⟩
  have h := hC j m hm F hF
  rw [ENNReal.coe_toNNReal hptop, ENNReal.coe_toNNReal_eq_toReal, ← ENNReal.toReal_inv] at h
  exact h

/-- The adjoint of `U(t) = W₊(t) Pⱼ` is `Pⱼ W₊(-t) = W₊(-t) Pⱼ`, since the symbol `ψⱼ` is real. -/
private theorem adjoint_halfWavePropagator_comp_apply {j : ℤ} {m : Lp ℂ ∞ (volume : Measure E)}
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (t : ℝ)
    (g : Lp ℂ 2 (volume : Measure E)) :
    ((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) g =
      halfWavePropagator ℂ (-t) (Lp.fourierMultiplierCLM ℂ m g) := by
  rw [adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply,
    Lp.star_eq_self_of_ae_eq_ofReal hm, fourierMultiplierCLM_halfWavePropagator_apply]

/-- The Duhamel pairing `⟪W₊(t - s) Pⱼ Pⱼ f, g⟫` is the pairing `⟪U(s)* f, U(t)* g⟫` of
`U(t) = W₊(t) Pⱼ`. -/
private theorem inner_halfWavePropagator_sub_eq_inner_adjoint {j : ℤ}
    {m : Lp ℂ ∞ (volume : Measure E)} (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    (s t : ℝ) (f g : Lp ℂ 2 (volume : Measure E)) :
    ⟪halfWavePropagator ℂ (t - s)
        (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m f)), g⟫_ℂ =
      ⟪((halfWavePropagator ℂ s ∘L Lp.fourierMultiplierCLM ℂ m)†) f,
        ((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) g⟫_ℂ := by
  rw [ContinuousLinearMap.adjoint_inner_right,
    halfWavePropagator_comp_fourierMultiplierCLM_apply_adjoint,
    Lp.star_eq_self_of_ae_eq_ofReal hm]

variable {p q p₁ q₁ r r' r₁ r₁' : ℝ≥0∞} [p.HolderConjugate q] [p₁.HolderConjugate q₁]
  [r'.HolderConjugate r] [r₁'.HolderConjugate r₁]

/-- The dual estimates of `U(t) = W₊(t) Pⱼ` along a wave-admissible pair, written with adjoints as
in the abstract retarded estimate `TauCeti.enorm_integral_setIntegral_Iio_inner_adjoint_le`. -/
private theorem exists_enorm_integral_adjoint_halfWavePropagator_comp_le (hq : 2 < q)
    (hr : 2 ≤ r)
    (hqr : 2 * (q⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
        ‖∫ s, ((halfWavePropagator ℂ s ∘L Lp.fourierMultiplierCLM ℂ m)†) (F s)‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume := by
  obtain ⟨C, hC⟩ :=
    φ.exists_enorm_integral_halfWavePropagator_neg_le_of_two_lt (p := p) (r' := r') hq hr hqr
  refine ⟨C, fun j m hm F hF ↦ ?_⟩
  simp only [φ.adjoint_halfWavePropagator_comp_apply hm]
  exact hC j m hm F hF

/-- **The Christ–Kiselev step for two admissible pairs.** If operators `U(t)` on `L²(E)` satisfy
the dual estimates along `(q₁, r₁)` and `(q, r)`, `2 < q, q₁`, with the constants `C₁ 2^{jγ₁}`
and `C 2^{jγ}`, then their retarded pairings are bounded with the constant `K C₁ C 2^{j(γ + γ₁)}`,
where `K` is the Christ–Kiselev constant of the time exponents
(`TauCeti.enorm_integral_setIntegral_Iio_inner_adjoint_le_of_holderConjugate`). -/
private theorem enorm_integral_setIntegral_Iio_inner_adjoint_le_of_two_lt (hq : 2 < q)
    (hq₁ : 2 < q₁) {U : ℝ → Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    {C₁ C : ℝ≥0} {j : ℤ} {γ γ₁ : ℝ}
    (hC₁ : ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      Integrable (fun s ↦ ((U s)†) (F s)) →
      ‖∫ s, ((U s)†) (F s)‖ₑ ≤ C₁ * ENNReal.ofReal (((2 : ℝ) ^ j) ^ γ₁) *
        eLpNorm (fun s ↦ eLpNorm (F s) r₁' volume) p₁ volume)
    (hC : ∀ G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable G →
      Integrable (fun t ↦ ((U t)†) (G t)) →
      ‖∫ t, ((U t)†) (G t)‖ₑ ≤ C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ γ) *
        eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume)
    {F G : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : AEStronglyMeasurable F)
    (hG : AEStronglyMeasurable G) (hUF : Integrable (fun s ↦ ((U s)†) (F s)))
    (hUG : Integrable (fun t ↦ ((U t)†) (G t))) :
    ‖∫ t, ∫ s in Set.Iio t, ⟪((U s)†) (F s), ((U t)†) (G t)⟫_ℂ‖ₑ ≤
      (((1 - (2 : ℝ≥0∞) ^ (-(p₁⁻¹ + p⁻¹ - 1).toReal))⁻¹).toNNReal * C₁ * C : ℝ≥0) *
        ENNReal.ofReal (((2 : ℝ) ^ j) ^ (γ + γ₁)) *
        eLpNorm (fun s ↦ eLpNorm (F s) r₁' volume) p₁ volume *
        eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  refine (enorm_integral_setIntegral_Iio_inner_adjoint_le_of_holderConjugate hq.le hq₁.le
    (Or.inl hq) hC₁ hC hF hG hUF hUG).trans_eq ?_
  rw [Real.rpow_add (zpow_pos two_pos j), ENNReal.ofReal_mul (by positivity), ENNReal.coe_mul,
    ENNReal.coe_mul]
  ring

/-- The retarded estimate for the frequency-localized half-wave propagator `W₊` with two
wave-admissible pairs `(q, r)` and `(q₁, r₁)`, `2 < q, q₁ ≤ ∞`, in weak form:
`|∫ ∫_{s < t} ⟪W₊(t - s) Pⱼ Pⱼ F(s), G(t)⟫ ds dt| ≤ C 2^{j(γ + γ₁)} ‖F‖_{L^{p₁} L^{r₁'}}
‖G‖_{L^p L^{r'}}` when `s ↦ W₊(-s) Pⱼ F(s)` and `t ↦ W₊(-t) Pⱼ G(t)` are integrable. -/
private theorem exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_le
    (hq : 2 < q) (hr : 2 ≤ r)
    (hqr : 2 * (q⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁ : 2 < q₁) (hr₁ : 2 ≤ r₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F → AEStronglyMeasurable G →
        Integrable (fun s ↦ halfWavePropagator ℂ (-s) (Lp.fourierMultiplierCLM ℂ m (F s))) →
        Integrable (fun t ↦ halfWavePropagator ℂ (-t) (Lp.fourierMultiplierCLM ℂ m (G t))) →
        ‖∫ t, ∫ s in Set.Iio t, ⟪halfWavePropagator ℂ (t - s)
            (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal))) *
            eLpNorm (fun s ↦ eLpNorm (F s) r₁' volume) p₁ volume *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C₁, hC₁⟩ := φ.exists_enorm_integral_adjoint_halfWavePropagator_comp_le (p := p₁)
    (r' := r₁') hq₁ hr₁ hqr₁
  obtain ⟨C, hC⟩ := φ.exists_enorm_integral_adjoint_halfWavePropagator_comp_le (p := p)
    (r' := r') hq hr hqr
  refine ⟨((1 - (2 : ℝ≥0∞) ^ (-(p₁⁻¹ + p⁻¹ - 1).toReal))⁻¹).toNNReal * C₁ * C,
    fun j m hm F G hF hG hWF hWG ↦ ?_⟩
  simp_rw [φ.inner_halfWavePropagator_sub_eq_inner_adjoint hm]
  refine enorm_integral_setIntegral_Iio_inner_adjoint_le_of_two_lt hq hq₁
    (fun F hF _ ↦ hC₁ j m hm F hF) (fun G hG _ ↦ hC j m hm G hG) hF hG ?_ ?_
  all_goals simpa only [φ.adjoint_halfWavePropagator_comp_apply hm]

/-- The retarded estimate of
`ContDiffBump.exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_le` for the
backward half-wave propagator `W₋(τ) = W₊(-τ)`, when `s ↦ W₊(s) Pⱼ F(s)` and `t ↦ W₊(t) Pⱼ G(t)`
are integrable: the operators `W₊(-t) Pⱼ` satisfy the same dual estimates as `W₊(t) Pⱼ`, by
reversing time (`TauCeti.enorm_integral_adjoint_neg_le`). -/
private theorem exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_neg_sub_le
    (hq : 2 < q) (hr : 2 ≤ r)
    (hqr : 2 * (q⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁ : 2 < q₁) (hr₁ : 2 ≤ r₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F → AEStronglyMeasurable G →
        Integrable (fun s ↦ halfWavePropagator ℂ s (Lp.fourierMultiplierCLM ℂ m (F s))) →
        Integrable (fun t ↦ halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m (G t))) →
        ‖∫ t, ∫ s in Set.Iio t, ⟪halfWavePropagator ℂ (-(t - s))
            (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal))) *
            eLpNorm (fun s ↦ eLpNorm (F s) r₁' volume) p₁ volume *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C₁, hC₁⟩ := φ.exists_enorm_integral_adjoint_halfWavePropagator_comp_le (p := p₁)
    (r' := r₁') hq₁ hr₁ hqr₁
  obtain ⟨C, hC⟩ := φ.exists_enorm_integral_adjoint_halfWavePropagator_comp_le (p := p)
    (r' := r') hq hr hqr
  refine ⟨((1 - (2 : ℝ≥0∞) ^ (-(p₁⁻¹ + p⁻¹ - 1).toReal))⁻¹).toNNReal * C₁ * C,
    fun j m hm F G hF hG hWF hWG ↦ ?_⟩
  -- The pairing is that of the reversed operators `U(-t) = W₊(-t) Pⱼ`.
  have hpair (s t : ℝ) : ⟪halfWavePropagator ℂ (-(t - s))
      (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ =
      ⟪((halfWavePropagator ℂ (-s) ∘L Lp.fourierMultiplierCLM ℂ m)†) (F s),
        ((halfWavePropagator ℂ (-t) ∘L Lp.fourierMultiplierCLM ℂ m)†) (G t)⟫_ℂ := by
    rw [← φ.inner_halfWavePropagator_sub_eq_inner_adjoint hm, neg_sub_neg, neg_sub]
  have hadj (t : ℝ) (g : Lp ℂ 2 (volume : Measure E)) :
      ((halfWavePropagator ℂ (-t) ∘L Lp.fourierMultiplierCLM ℂ m)†) g =
        halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m g) := by
    rw [φ.adjoint_halfWavePropagator_comp_apply hm, neg_neg]
  simp_rw [hpair]
  refine enorm_integral_setIntegral_Iio_inner_adjoint_le_of_two_lt
    (U := fun t ↦ halfWavePropagator ℂ (-t) ∘L Lp.fourierMultiplierCLM ℂ m) hq hq₁
    (fun F hF hUF ↦ enorm_integral_adjoint_neg_le (fun F hF _ ↦ hC₁ j m hm F hF) hF hUF)
    (fun G hG hUG ↦ enorm_integral_adjoint_neg_le (fun G hG _ ↦ hC j m hm G hG) hG hUG) hF hG ?_ ?_
  all_goals simpa only [hadj]

/-- The retarded estimate for the frequency-localized wave Duhamel operator with two
wave-admissible pairs `(q, r)` and `(q₁, r₁)`, `2 < q, q₁ ≤ ∞`, in weak form: for integrable
`F` and `G`,
`|∫ ⟪∫_{s < t} D⁻¹ sin((t - s)D) Pⱼ Pⱼ F(s) ds, G(t)⟫ dt|
  ≤ C 2^{j(γ + γ₁ - 1)} ‖F‖_{L^{p₁} L^{r₁'}} ‖G‖_{L^p L^{r'}}`. -/
private theorem exists_enorm_integral_inner_setIntegral_Iio_waveSinPropagator_sub_le
    (hq : 2 < q) (hr : 2 ≤ r)
    (hqr : 2 * (q⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁ : 2 < q₁) (hr₁ : 2 ≤ r₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F → Integrable G →
        ‖∫ t, ⟪∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
            (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r₁' volume) p₁ volume *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨Cp, hCp⟩ := φ.exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_le
    (p := p) (r' := r') (p₁ := p₁) (r₁' := r₁') hq hr hqr hq₁ hr₁ hqr₁
  obtain ⟨Cm, hCm⟩ := φ.exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_neg_sub_le
    (p := p) (r' := r') (p₁ := p₁) (r₁' := r₁') hq hr hqr hq₁ hr₁ hqr₁
  set K := eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate φ.invCutoff 0)) 1 volume
  have hK : (K.toNNReal : ℝ≥0∞) = K := ENNReal.coe_toNNReal
    (φ.memLp_fourierInv_dyadicDilate φ.invCutoff 0 1).eLpNorm_ne_top
  refine ⟨(Cp + Cm) * K.toNNReal, fun j m hm F G hF hG ↦ ?_⟩
  set γ := ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal) +
    ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal)
  set c : ℂ := ((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹
  set X := eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume
  set Y := fun s ↦ φ.dyadicMultiplier ℂ φ.invCutoff j (F s)
  have hY : Integrable Y := (φ.dyadicMultiplier ℂ φ.invCutoff j).integrable_comp hF
  -- The integrability hypotheses of the two half-wave estimates, applied to `Y = Mⱼ F` and `G`.
  have hW (H : ℝ → Lp ℂ 2 (volume : Measure E)) (hH : Integrable H) (σ : ℝ → ℝ)
      (hσ : Continuous σ) :
      Integrable fun s ↦ halfWavePropagator ℂ (σ s) (Lp.fourierMultiplierCLM ℂ m (H s)) :=
    integrable_phasePropagator_apply _ hσ.aestronglyMeasurable
      ((Lp.fourierMultiplierCLM ℂ m).integrable_comp hH)
  have hp' := hCp j m hm Y G hY.aestronglyMeasurable hG.aestronglyMeasurable
    (hW Y hY _ continuous_neg) (hW G hG _ continuous_neg)
  have hm' := hCm j m hm Y G hY.aestronglyMeasurable hG.aestronglyMeasurable
    (hW Y hY _ continuous_id) (hW G hG _ continuous_id)
  rw [φ.integral_inner_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_eq hm hF hG,
    eNorm_mul, RCLike.eNorm_conj]
  calc _ ≤ ‖c‖ₑ * (Cp * ENNReal.ofReal (((2 : ℝ) ^ j) ^ γ) *
          eLpNorm (fun s ↦ eLpNorm (Y s) r₁' volume) p₁ volume * X +
          Cm * ENNReal.ofReal (((2 : ℝ) ^ j) ^ γ) *
          eLpNorm (fun s ↦ eLpNorm (Y s) r₁' volume) p₁ volume * X) := by
        gcongr
        exact eNorm_sub_le.trans (add_le_add hp' hm')
    _ ≤ ‖c‖ₑ * 2 * ((Cp + Cm) * ENNReal.ofReal (((2 : ℝ) ^ j) ^ γ) *
          (K * eLpNorm (fun s ↦ eLpNorm (F s) r₁' volume) p₁ volume) * X) := by
        rw [← add_mul, ← add_mul, ← add_mul, ← ENNReal.coe_add]
        gcongr ?_ * (_ * _ * ?_ * _)
        · exact le_mul_of_one_le_right' one_le_two
        · exact φ.eLpNorm_eLpNorm_dyadicMultiplier_le φ.invCutoff j hF.aestronglyMeasurable
            (ENNReal.HolderConjugate.one_le r₁' r₁)
    _ = _ := by
        rw [← enorm_two_zpow_inv_mul_two_mul_I_inv_mul_two_mul_ofReal_rpow j γ, ENNReal.coe_mul,
          ENNReal.coe_add, hK]
        ring

end TwoPairs

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
    have : Subsingleton E := Module.finrank_zero_iff.1 hE
    exact ⟨0, fun j m hm f ↦ (eLpNorm_eLpNorm_eq_zero fun t ↦ by
      rw [ContDiffBump.fourierMultiplierCLM_littlewoodPaley_eq_zero hm, zero_apply,
        map_zero]).trans_le zero_le⟩
  obtain ⟨-, -, hr2⟩ := two_le_finrank_of_waveAdmissible hq hr0 hqr hE
  -- Test against `L^{r'}` with `r'` the Hölder conjugate of `r`.
  have hrr := ENNReal.HolderConjugate.inv_one_sub_inv' (one_le_two.trans hr2)
  obtain ⟨C, hC⟩ := φ.exists_enorm_integral_inner_halfWavePropagator_littlewoodPaley_le
    (r' := (1 - r⁻¹)⁻¹) hq hpq hqr
  have := hpq.symm.coe_ennreal
  exact ⟨C, fun j m hm f ↦ (continuous_phasePropagator_apply _ _).aestronglyMeasurable
    |>.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℂ) (p' := p)
      (q' := (1 - r⁻¹)⁻¹) fun G hG _ ↦
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
  set K := eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate φ.invCutoff 0)) 1 volume
  refine ⟨C * K.toNNReal * (ENNReal.LpAddConst r).toNNReal, fun j m hm g ↦ ?_⟩
  set γ := (Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹
  set c : ℂ := ((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹
  set u := fun t ↦
    halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m (φ.dyadicMultiplier ℂ φ.invCutoff j g))
  have hu : Continuous u := continuous_phasePropagator_apply _ _
  have hpt (t : ℝ) : eLpNorm (waveSinPropagator ℂ t (Lp.fourierMultiplierCLM ℂ m g)) r volume ≤
      ‖c‖ₑ * ENNReal.LpAddConst r * (eLpNorm (u t) r volume + eLpNorm (u (-t)) r volume) := by
    rw [φ.waveSinPropagator_littlewoodPaley_eq hm, eLpNorm_congr_ae (Lp.coeFn_smul _ _),
      eLpNorm_const_smul, eLpNorm_congr_ae (Lp.coeFn_sub _ _), mul_assoc]
    gcongr
    exact eLpNorm_sub_le' r
  have hMg : ‖φ.dyadicMultiplier ℂ φ.invCutoff j g‖ₑ ≤ K * ‖g‖ₑ := by
    simpa only [Lp.eNorm_def] using φ.eLpNorm_dyadicMultiplier_le φ.invCutoff j g one_le_two
  have hK : (K.toNNReal : ℝ≥0∞) = K := ENNReal.coe_toNNReal
    (φ.memLp_fourierInv_dyadicDilate φ.invCutoff 0 1).eLpNorm_ne_top
  calc _ ≤ ‖c‖ₑ * ENNReal.LpAddConst r * 2 * eLpNorm (fun t ↦ eLpNorm (u t) r volume) q volume :=
        eLpNorm_eLpNorm_le_mul_two_mul (continuous_waveSinPropagator_apply _).aestronglyMeasurable
          hu.aestronglyMeasurable (by exact_mod_cast (one_le_two.trans hq.le)) hpt
    _ ≤ ‖c‖ₑ * 2 * ENNReal.LpAddConst r *
          (C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ γ) * (K * ‖g‖ₑ)) := by
        rw [mul_right_comm _ (ENNReal.LpAddConst r)]
        gcongr
        exact (hC j m hm _).trans (by gcongr)
    _ = _ := by
        rw [← enorm_two_zpow_inv_mul_two_mul_I_inv_mul_two_mul_ofReal_rpow j γ, ENNReal.coe_mul,
          ENNReal.coe_mul, hK, ENNReal.coe_toNNReal (ENNReal.LpAddConst_lt_top r).ne]
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
  set K := eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate φ.invCutoff 0)) 1 volume
  set KP := eLpNorm (𝓕⁻ (fun ξ ↦ (φ.littlewoodPaley 0 ξ : ℂ))) 1 volume
  refine ⟨C * KP.toNNReal * K.toNNReal, fun j m hm F G hF hG ↦ ?_⟩
  set γ := (Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹
  set c : ℂ := ((2 : ℝ) ^ j)⁻¹ * (2 * Complex.I)⁻¹
  have hMF : AEStronglyMeasurable fun s ↦ φ.dyadicMultiplier ℂ φ.invCutoff j (F s) :=
    (φ.dyadicMultiplier ℂ φ.invCutoff j).continuous.comp_aestronglyMeasurable hF
  set Y := fun s ↦ Lp.fourierMultiplierCLM ℂ m (φ.dyadicMultiplier ℂ φ.invCutoff j (F s))
  have hY : AEStronglyMeasurable Y :=
    (Lp.fourierMultiplierCLM ℂ m).continuous.comp_aestronglyMeasurable hMF
  -- `D⁻¹ sin(τD) Pⱼ Pⱼ = c (W₊(τ) - W₊(-τ)) Pⱼ Pⱼ Mⱼ`, and the single-block half-wave estimate
  -- applies to both halves, with `Pⱼ Mⱼ F` as forcing.
  have hsplit := lintegral_lintegral_enorm_inner_smul_halfWavePropagator_sub_le
    (Lp.fourierMultiplierCLM ℂ m) c (fun F G hF hG ↦ hC j m hm F G hF hG) hY hG
  simp_rw [φ.waveSinPropagator_littlewoodPaley_littlewoodPaley_eq hm]
  -- `Pⱼ` and `Mⱼ` cost constant factors in the mixed norm.
  have hr : 1 ≤ r' := ENNReal.HolderConjugate.one_le r' r
  have hYF : eLpNorm (fun s ↦ eLpNorm (Y s) r' volume) p volume ≤
      KP * (K * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume) :=
    (eLpNorm_eLpNorm_apply_le (Lp.fourierMultiplierCLM ℂ m).continuous
      (fun f ↦ φ.eLpNorm_fourierMultiplierCLM_littlewoodPaley_le hm f hr) hMF).trans
      (by gcongr; exact φ.eLpNorm_eLpNorm_dyadicMultiplier_le φ.invCutoff j hF hr)
  have hK : (K.toNNReal : ℝ≥0∞) = K := ENNReal.coe_toNNReal
    (φ.memLp_fourierInv_dyadicDilate φ.invCutoff 0 1).eLpNorm_ne_top
  have hKP : (KP.toNNReal : ℝ≥0∞) = KP :=
    ENNReal.coe_toNNReal (φ.memLp_fourierInv_littlewoodPaley 0 1).eLpNorm_ne_top
  calc _ ≤ _ := hsplit
    _ ≤ ‖c‖ₑ * 2 * (C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * γ)) *
          (KP * (K * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume)) *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume) := by
        gcongr
    _ = _ := by
        rw [← enorm_two_zpow_inv_mul_two_mul_I_inv_mul_two_mul_ofReal_rpow j (2 * γ),
          ENNReal.coe_mul, ENNReal.coe_mul, hKP, hK]
        ring

end Admissible

/-- **The retarded Strichartz estimate for the frequency-localized wave Duhamel operator** in
mixed norm, with the forcing measured along a second admissible pair. Let `E` have dimension `n`,
let `Pⱼ` be the `L²` Fourier multiplier with the Littlewood–Paley cutoff `ψⱼ` built from `φ` as
symbol, let `(q, r)` be wave-admissible, `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞`,
and let `(q₁, r₁)` be wave-admissible with `2 < q₁ ≤ ∞`, with Hölder conjugates `p₁` and `r₁'`.
Put `γ = n / 2 - n / r - 1 / q` and `γ₁ = n / 2 - n / r₁ - 1 / q₁`. There is `C` such that for
every `j ∈ ℤ` and every forcing term `F : ℝ → L²(E)` that is integrable in time,

`‖∫_{s < t} D⁻¹ sin((t - s)D) Pⱼ Pⱼ F(s) ds‖_{L^q_t L^r_x}`
`  ≤ C 2^{j(γ + γ₁ - 1)} ‖F‖_{L^{p₁}_t L^{r₁'}_x}`.

The pair `(q₁, r₁) = (q, r)` gives the exponent `2γ - 1`, and the pairs `(∞, r₁)` measure the
forcing in `L¹_t L^{r₁'}_x`, the energy pair `(∞, 2)` among them. -/
theorem exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le
    {q r : ℝ≥0∞} (hq : 2 < q) (hq_top : q ≠ ∞)
    (hqr : 2 * (q⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁] [r₁'.HolderConjugate r₁] (hq₁ : 2 < q₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
            (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))) :
              Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r₁' volume) p₁ volume := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ _ _ ↦ by simp [eLpNorm_exponent_zero, Lp.aestronglyMeasurable]⟩
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hE | hE
  · have : Subsingleton E := Module.finrank_zero_iff.1 hE
    refine ⟨0, fun j m hm F _ ↦ (eLpNorm_eLpNorm_eq_zero fun t ↦ ?_).trans_le zero_le⟩
    simp_rw [ContDiffBump.fourierMultiplierCLM_littlewoodPaley_eq_zero hm, zero_apply,
      map_zero, integral_zero]
  obtain ⟨hq2, hqr'⟩ := waveAdmissible_toNNReal hq hq_top hqr
  obtain ⟨hn, -, hr2⟩ := two_le_finrank_of_waveAdmissible hq2 hr0 hqr' hE
  -- In dimension `n ≥ 2` admissibility of `(q₁, r₁)` forces `r₁ ≥ 2`, also for `q₁ = ∞`.
  have hr₁ := two_le_of_waveAdmissible (ENNReal.HolderConjugate.ne_zero r₁ r₁') hqr₁ hn
  -- Test against `L^{p}_t L^{r'}_x` with `p` and `r'` the Hölder conjugates of `q` and `r`.
  have := ENNReal.HolderConjugate.inv_one_sub_inv' (one_le_two.trans hq.le)
  have := ENNReal.HolderConjugate.inv_one_sub_inv' (one_le_two.trans hr2)
  obtain ⟨C, hC⟩ := φ.exists_enorm_integral_inner_setIntegral_Iio_waveSinPropagator_sub_le
    (p := (1 - q⁻¹)⁻¹) (r' := (1 - r⁻¹)⁻¹) (p₁ := p₁) (r₁' := r₁') hq hr2 hqr hq₁ hr₁ hqr₁
  refine ⟨C, fun j m hm F hF ↦ ?_⟩
  have hPPF := (Lp.fourierMultiplierCLM ℂ m).integrable_comp
    ((Lp.fourierMultiplierCLM ℂ m).integrable_comp hF)
  exact (aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub
    hPPF.aestronglyMeasurable).eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℂ)
    (p' := (1 - q⁻¹)⁻¹) (q' := (1 - r⁻¹)⁻¹) fun G hG _ ↦ hC j m hm F G hF hG

end ContDiffBump

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {q : ℝ≥0} {r : ℝ≥0∞}

/-- Let `(q, r)` be wave-admissible, `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q`. If
`‖cos(tD) f‖_{L^q_t L^r_x} ≤ C₁ A` and `‖D⁻¹ sin(tD) g‖_{L^q_t L^r_x} ≤ C₂ B`, then the free
solution satisfies `‖cos(tD) f + D⁻¹ sin(tD) g‖_{L^q_t L^r_x} ≤ (C₁ + C₂) (A + B)`. At `r = 0`
every mixed norm vanishes; otherwise wave-admissibility gives `2 ≤ r`, and Minkowski's inequality
`MeasureTheory.eLpNorm_eLpNorm_add_le` applies. -/
theorem eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    {f g : Lp F 2 (volume : Measure E)} {C₁ C₂ : ℝ≥0} {A B : ℝ≥0∞}
    (hf : eLpNorm (fun t ↦ eLpNorm (waveCosPropagator F t f) r volume) q volume ≤ C₁ * A)
    (hg : eLpNorm (fun t ↦ eLpNorm (waveSinPropagator F t g) r volume) q volume ≤ C₂ * B) :
    eLpNorm (fun t ↦ eLpNorm (waveCosPropagator F t f + waveSinPropagator F t g) r volume) q
      volume ≤ ((C₁ + C₂ : ℝ≥0) : ℝ≥0∞) * (A + B) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp_rw [eLpNorm_exponent_zero (Lp.aestronglyMeasurable _)]
    simp
  obtain ⟨-, -, hr2⟩ := two_le_finrank_of_waveAdmissible hq hr0 hqr Module.finrank_pos
  grw [eLpNorm_eLpNorm_add_le (continuous_waveCosPropagator_apply f).aestronglyMeasurable
    (continuous_waveSinPropagator_apply g).aestronglyMeasurable
    (by exact_mod_cast one_le_two.trans hq.le) (one_le_two.trans hr2), hf, hg, ENNReal.coe_add,
    add_mul, mul_add, mul_add]
  gcongr
  · exact le_self_add
  · exact le_add_self

end TauCeti

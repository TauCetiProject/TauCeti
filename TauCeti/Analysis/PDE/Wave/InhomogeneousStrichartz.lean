/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.MixedNorm
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Analysis.SpecificLimits.DyadicSum
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# The retarded Strichartz estimate for the wave equation with Besov forcing

On a nontrivial real inner product space `E` of dimension `n`, let `D = √(-Δ)` and let `Pⱼ`,
`j ∈ ℤ`, be the `L²` Fourier multipliers with the homogeneous Littlewood–Paley cutoffs `ψⱼ`
(`ContDiffBump.littlewoodPaley`) as symbols. The solution of the wave equation `∂ₜ²u - Δu = F`
with zero data at `t = -∞` is the retarded Duhamel integral

`u(t) = ∫_{s < t} D⁻¹ sin((t - s)D) F(s) ds`

(`TauCeti.waveSinPropagator`). Let `(q, r)` be wave-admissible, `2 / q + (n - 1) / r ≤ (n - 1) / 2`,
with `2 < q < ∞`, and let `(q₁, r₁)` be wave-admissible with `2 < q₁ ≤ ∞`, with Hölder conjugates
`p₁` and `r₁'`. Put `γ = n / 2 - n / r - 1 / q` and `γ₁ = n / 2 - n / r₁ - 1 / q₁`. This file proves
the **retarded Strichartz estimate** for every integrable forcing term `F : ℝ → L²(E)`:

`‖u‖_{L^q_t L^r_x} ≤ C ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Pⱼ F‖_{L^{p₁}_t L^{r₁'}_x}`

(`ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum`), with `C`
independent of `F`. The right-hand side is a dyadic `ℓ¹` sum over the blocks of `F`, each measured
along the second pair. For the energy pair `(q₁, r₁) = (∞, 2)` it is
`∑ⱼ 2^{j(γ - 1)} ‖Pⱼ F‖_{L¹_t L²_x}`. The integral `u(t)` is a Bochner integral, which exists for
instance when `F` vanishes outside a bounded interval of times, since `‖D⁻¹ sin(τD)‖ ≤ |τ|`;
where it does not exist it is `0`, and the estimate is stated for this value.

## The argument

The frequency-localized estimate
(`ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le`)
controls the retarded integral of `Pⱼ Pⱼ G` by `2^{j(γ + γ₁ - 1)} ‖G‖_{L^{p₁}_t L^{r₁'}_x}` for
every integrable `G`, with the square `Pⱼ Pⱼ` of a block rather than the block itself. It is summed
over the blocks as follows.

* **Reassembling a block from squared blocks.** The function `Ψ = ∑ⱼ ψⱼ²` is positive and smooth
  on `E \ {0}`, and invariant under `ξ ↦ 2 ξ`. Let `Qₗ` be the multiplier whose symbol is a
  Schwartz function equal to `1 / Ψ` on the support of `ψₗ`, the dilate by `2^l` of a fixed one.
  Its kernel is the `L¹`-normalised dilate of a fixed Schwartz function, so `Qₗ` is bounded on
  `L^{r₁'}` uniformly in `l` (`ContDiffBump.eLpNorm_eLpNorm_dyadicMultiplier_le`). Since only the
  `ψⱼ` with `|j - l| < L` meet the support of `ψₗ`, `Pₗ = ∑_{|j - l| < L} Pⱼ Pⱼ Qₗ Pₗ`
  (`ContDiffBump.sum_fourierMultiplierCLM_fourierMultiplierCLM_dyadicMultiplier_invSumSq`).
* **Summation.** At each time, `‖u(t)‖_r ≤ ∑ₗ ‖Pₗ u(t)‖_r`
  (`ContDiffBump.eLpNorm_apply_le_tsum_eLpNorm_apply_fourierMultiplierCLM`), and `Pₗ u(t)` is the
  sum over `|j - l| < L` of the retarded integrals of `Pⱼ Pⱼ (Qₗ Pₗ F)`. Minkowski's inequality in
  `L^q_t`, the frequency-localized estimate and the bound for `Qₗ` give
  `‖u‖_{L^q_t L^r_x} ≤ C ∑ₗ ∑_{|j - l| < L} 2^{j(γ + γ₁ - 1)} ‖Pₗ F‖_{L^{p₁}_t L^{r₁'}_x}`, and
  `2^{j(γ + γ₁ - 1)}` is comparable to `2^{l(γ + γ₁ - 1)}` for `|j - l| < L`.

## Main declarations

* `ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum`: the
  retarded Strichartz estimate for the wave equation with forcing in the dyadic `ℓ¹` class.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.6 and its proof.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
-/

public section

noncomputable section

open scoped ENNReal NNReal FourierTransform SchwartzMap Topology
open MeasureTheory TauCeti

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (φ : ContDiffBump (0 : E))

/-! ### The retarded estimate -/

variable [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- At each time, the retarded Duhamel integral `u(t)` satisfies
`‖u(t)‖_r ≤ ∑ₗ ∑_{|d| < L} ‖Φ_{d + l, l}(t)‖_r`, where `Φⱼₗ` is the retarded integral of
`Pⱼ Pⱼ Qₗ Pₗ F`: by `‖u(t)‖_r ≤ ∑ₗ ‖Pₗ u(t)‖_r` and `Pₗ = ∑_{|d| < L} P_{d + l} P_{d + l} Qₗ Pₗ`. -/
private theorem eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_sum {L : ℕ}
    (hL : ∀ j k : ℤ, j + L ≤ k → ∀ ξ : E, φ.littlewoodPaley j ξ * φ.littlewoodPaley k ξ = 0)
    {m : ℤ → Lp ℂ ∞ (volume : Measure E)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    {F : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : Integrable F) {r : ℝ≥0∞} (hr : 1 ≤ r) (t : ℝ) :
    eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
        Lp ℂ 2 (volume : Measure E))) r volume ≤
      ∑' l, ∑ d ∈ Finset.Ioo (-(L : ℤ)) L, eLpNorm ((∫ s in Set.Iio t,
        waveSinPropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ (m (d + l))
          (Lp.fourierMultiplierCLM ℂ (m (d + l))
            (φ.dyadicMultiplier ℂ φ.invSumSq l (Lp.fourierMultiplierCLM ℂ (m l) (F s))))) :
          Lp ℂ 2 (volume : Measure E))) r volume := by
  by_cases hint : IntegrableOn (fun s ↦ waveSinPropagator ℂ (t - s) (F s)) (Set.Iio t)
  · refine (φ.eLpNorm_apply_le_tsum_eLpNorm_apply_fourierMultiplierCLM hm
      (ContinuousLinearMap.id ℂ _) _ hr).trans (tsum_le_tsum fun l ↦ ?_)
    rw [ContinuousLinearMap.id_apply, ← ContinuousLinearMap.integral_comp_comm _ hint]
    have hdec (s : ℝ) :
        Lp.fourierMultiplierCLM ℂ (m l) (waveSinPropagator ℂ (t - s) (F s)) =
          ∑ d ∈ Finset.Ioo (-(L : ℤ)) L, waveSinPropagator ℂ (t - s)
            (Lp.fourierMultiplierCLM ℂ (m (d + l)) (Lp.fourierMultiplierCLM ℂ (m (d + l))
              (φ.dyadicMultiplier ℂ φ.invSumSq l (Lp.fourierMultiplierCLM ℂ (m l) (F s))))) := by
      rw [fourierMultiplierCLM_waveSinPropagator_apply, ← map_sum,
        φ.sum_fourierMultiplierCLM_fourierMultiplierCLM_dyadicMultiplier_invSumSq hL hm l (F s)]
    simp_rw [hdec]
    have hH := (φ.dyadicMultiplier ℂ φ.invSumSq l).integrable_comp
      ((Lp.fourierMultiplierCLM ℂ (m l)).integrable_comp hF)
    rw [integral_finsetSum _ fun d _ ↦
        (φ.integrable_waveSinPropagator_sub_littlewoodPaley (hm (d + l))
          ((Lp.fourierMultiplierCLM ℂ (m (d + l))).integrable_comp hH) t).integrableOn,
      eLpNorm_congr_ae (Lp.coeFn_finsetSum _ _)]
    exact eLpNorm_sum_le hr
  · rw [integral_undef hint, eLpNorm_congr_ae (Lp.coeFn_zero _ _ _), eLpNorm_zero]
    exact zero_le

/-- **The retarded Strichartz estimate for the wave equation with Besov forcing.** Let `E` be
nontrivial of dimension `n`, let `Pⱼ` be the `L²` Fourier multiplier with the Littlewood–Paley
cutoff `ψⱼ` built from `φ` as symbol, let `(q, r)` be wave-admissible,
`2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞`, and let `(q₁, r₁)` be wave-admissible with
`2 < q₁ ≤ ∞`, with Hölder conjugates `p₁` and `r₁'`. Put `γ = n / 2 - n / r - 1 / q` and
`γ₁ = n / 2 - n / r₁ - 1 / q₁`. There is `C` such that for every integrable forcing term
`F : ℝ → L²(E)`, the retarded Duhamel integral `u(t) = ∫_{s < t} D⁻¹ sin((t - s)D) F(s) ds`,
the solution of `∂ₜ²u - Δu = F` with zero data at `t = -∞`, satisfies

`‖u‖_{L^q_t L^r_x} ≤ C ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Pⱼ F‖_{L^{p₁}_t L^{r₁'}_x}`.

Here `u(t)` is a Bochner integral, taken to be `0` where it does not exist. -/
theorem exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum
    {q r : ℝ≥0∞} (hq : 2 < q) (hq_top : q ≠ ∞)
    (hqr : 2 * (q⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁] [r₁'.HolderConjugate r₁] (hq₁ : 2 < q₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
            Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
            eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (F s)) r₁' volume) p₁
              volume := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ _ ↦ by simp [eLpNorm_exponent_zero, Lp.aestronglyMeasurable]⟩
  obtain ⟨hq2, hqr'⟩ := waveAdmissible_toNNReal hq hq_top hqr
  obtain ⟨-, -, hr2⟩ := two_le_finrank_of_waveAdmissible hq2 hr0 hqr' Module.finrank_pos
  obtain ⟨L, hL⟩ := φ.exists_littlewoodPaley_mul_eq_zero φ
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le
      (p₁ := p₁) (r₁' := r₁') hq hq_top hqr hq₁ hqr₁
  have hK := ENNReal.coe_toNNReal (φ.memLp_fourierInv_dyadicDilate φ.invSumSq 0 1).eLpNorm_ne_top
  set K := eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate φ.invSumSq 0)) 1 volume
  set S := Finset.Ioo (-(L : ℤ)) L
  set σ := ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal) +
    ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1
  refine ⟨C * K.toNNReal * ∑ d ∈ S, (((2 : ℝ) ^ d) ^ σ).toNNReal, fun m hm F hF ↦ ?_⟩
  -- `Hₗ = Qₗ Pₗ F` and `a j l t = ‖Φⱼₗ(t)‖_r`, with `Φⱼₗ` the retarded integral of `Pⱼ Pⱼ Hₗ`.
  have hPF (l : ℤ) := (Lp.fourierMultiplierCLM ℂ (m l)).integrable_comp hF
  have hH (l : ℤ) := (φ.dyadicMultiplier ℂ φ.invSumSq l).integrable_comp (hPF l)
  set a : ℤ → ℤ → ℝ → ℝ≥0∞ := fun j l t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
    (Lp.fourierMultiplierCLM ℂ (m j) (Lp.fourierMultiplierCLM ℂ (m j)
      (φ.dyadicMultiplier ℂ φ.invSumSq l (Lp.fourierMultiplierCLM ℂ (m l) (F s))))) :
        Lp ℂ 2 (volume : Measure E))) r volume
  have hpt := φ.eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_sum hL hm hF
    (one_le_two.trans hr2)
  calc eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
          Lp ℂ 2 (volume : Measure E))) r volume) q volume
      ≤ eLpNorm (fun t ↦ ∑' l, ∑ d ∈ S, a (d + l) l t) q volume :=
        eLpNorm_mono_eNorm ((aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub
          hF.aestronglyMeasurable).aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable
          fun t ↦ by simpa only [eNorm_eq_self] using hpt t
    _ ≤ ∑' l, ∑ d ∈ S, eLpNorm (a (d + l) l) q volume :=
        (eLpNorm_tsum_le (fun l ↦ Finset.aemeasurable_fun_sum _ fun d _ ↦
          (aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub ((Lp.fourierMultiplierCLM ℂ
            _ ∘L Lp.fourierMultiplierCLM ℂ _).integrable_comp (hH l)).aestronglyMeasurable
              ).aemeasurable_eLpNorm_Lp .rfl r) (one_le_two.trans hq.le)).trans
          (tsum_le_tsum fun l ↦ by
            rw [← Finset.sum_fn]
            exact eLpNorm_sum_le (one_le_two.trans hq.le))
    -- The frequency-localized estimate and the bound for `Qₗ`.
    _ ≤ ∑' l, ∑ d ∈ S, C * K * (ENNReal.ofReal (((2 : ℝ) ^ (d + l)) ^ σ) * eLpNorm (fun s ↦
          eLpNorm (Lp.fourierMultiplierCLM ℂ (m l) (F s)) r₁' volume) p₁ volume) :=
        tsum_le_tsum fun l ↦ Finset.sum_le_sum fun d _ ↦
          (hC (d + l) (m (d + l)) (hm (d + l)) _ (hH l)).trans <| by
            rw [mul_assoc, mul_assoc, mul_left_comm K]
            gcongr
            exact φ.eLpNorm_eLpNorm_dyadicMultiplier_le φ.invSumSq l (hPF l).aestronglyMeasurable
              (ENNReal.HolderConjugate.pos p₁ q₁) (ENNReal.HolderConjugate.one_le r₁' r₁)
    _ = _ := by
        simp_rw [← Finset.mul_sum]
        rw [ENNReal.tsum_mul_left, tsum_sum_ofReal_two_zpow_add_rpow_mul, ENNReal.coe_mul,
          ENNReal.coe_mul, hK]
        ring

end ContDiffBump

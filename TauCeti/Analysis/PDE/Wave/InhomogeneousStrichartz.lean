/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.MixedNorm
import TauCeti.Analysis.Fourier.Bernstein
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Analysis.PDE.Strichartz.LittlewoodPaley
import TauCeti.Analysis.PDE.Wave.Endpoint
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Analysis.SpecificLimits.DyadicSum
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.Lp.MixedNorm
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Function.LpSeminorm.SquareSum

/-!
# The retarded Strichartz estimate for the wave equation with Besov forcing

On a nontrivial real inner product space `E` of dimension `n`, let `D = √(-Δ)` and let `Pⱼ`,
`j ∈ ℤ`, be the `L²` Fourier multipliers with the homogeneous Littlewood–Paley cutoffs `ψⱼ`
(`ContDiffBump.littlewoodPaley`) as symbols. The solution of the wave equation `∂ₜ²u - Δu = F`
with zero data at `t = -∞` is the retarded Duhamel integral

`u(t) = ∫_{s < t} D⁻¹ sin((t - s)D) F(s) ds`

(`TauCeti.waveSinPropagator`). Let `(q, r)` be wave-admissible, `2 / q + (n - 1) / r ≤ (n - 1) / 2`,
with `2 ≤ q < ∞`, and let `(q₁, r₁)` be wave-admissible with `2 ≤ q₁ ≤ ∞`, with Hölder conjugates
`p₁` and `r₁'`, where the time exponent `2` is allowed, on either side or on both, in dimension
`n ≥ 4`: the pairs `(2, r)` with `r` at least the endpoint exponent `2 (n - 1) / (n - 3)`,
`r = ∞` included. Put `γ = n / 2 - n / r - 1 / q` and `γ₁ = n / 2 - n / r₁ - 1 / q₁`. This file
proves the **retarded Strichartz estimate** for every integrable forcing term `F : ℝ → L²(E)`:

`‖u‖_{L^q_t L^r_x} ≤ C ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Pⱼ F‖_{L^{p₁}_t L^{r₁'}_x}`

(`ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum`), with `C`
independent of `F`. The right-hand side is a dyadic `ℓ¹` sum over the blocks of `F`, each measured
along the second pair. For the energy pair `(q₁, r₁) = (∞, 2)` it is
`∑ⱼ 2^{j(γ - 1)} ‖Pⱼ F‖_{L¹_t L²_x}`. The integral `u(t)` is a Bochner integral, which exists for
instance when `F` vanishes outside a bounded interval of times, since `‖D⁻¹ sin(τD)‖ ≤ |τ|`;
where it does not exist it is `0`, and the estimate is stated for this value.

The same estimate holds at the pairs `(∞, r)`, `2 ≤ r ≤ ∞`, with `γ = n / 2 - n / r` and a second
pair as above with `r₁ ≥ 2`, where `q₁ = 2` only at the endpoint
(`ContDiffBump.exists_eLpNorm_top_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum`); at
`(∞, ∞)` it bounds `u` uniformly in space and time.

For `r < ∞` the dyadic `ℓ¹` sum improves to the square sum

`‖u‖_{L^q_t L^r_x} ≤ C (∑ⱼ 2^{2j(γ + γ₁ - 1)} ‖Pⱼ F‖²_{L^{p₁}_t L^{r₁'}_x})^{1/2}`

(`ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_sq_rpow`), at
the same pairs as above with `r < ∞`, and at the pairs `(∞, r)` with `2 ≤ r < ∞`
(`ContDiffBump.exists_eLpNorm_top_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_sq_rpow`).
These are the finite-`r` square-function forms of the retarded estimates of Tao, Theorem 2.6. At
`r = ∞` the Littlewood–Paley inequality is not available, and the `ℓ¹` estimates remain the
statement there.

## The argument

At the pairs with `q > 2` and at the endpoint the frequency-localized estimate is, in the
`ContDiffBump` namespace,
`exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le_of_sharp`.
The pairs `(2, r)` beyond the endpoint reduce to the endpoint pair `(2, r₀)` by Bernstein's
inequality, on the side of the solution and on the side of the forcing: some dyadic multiplier
`Qⱼ` reproduces the block, `Pⱼ Qⱼ = Pⱼ`
(`ContDiffBump.exists_fourierMultiplierCLM_dyadicMultiplier_eq`), and it is bounded from `L^{r₀}`
to `L^r`, and from `L^{r'}` to `L^{r₀'}`, with norm a constant times `2^{jn (1/r₀ - 1/r)}`
(`ContDiffBump.eLpNorm_dyadicMultiplier_le_of_le`), the difference of the two scaling exponents.

The frequency-localized estimate
(`ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le`)
controls the retarded integral of `Pⱼ Pⱼ G` by `2^{j(γ + γ₁ - 1)} ‖G‖_{L^{p₁}_t L^{r₁'}_x}` for
every integrable `G`, with the square `Pⱼ Pⱼ` of a block rather than the block itself; at the pairs
`(∞, r)` this is
`ContDiffBump.exists_eLpNorm_top_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le`.
It is summed over the blocks as follows, along any time exponent `q ≥ 1`.

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
* **Square sums.** For `2 ≤ r < ∞`, the reverse Littlewood–Paley inequality
  (`TauCeti.exists_eLpNorm_le_mul_eLpNorm_tsum_enorm_fourierMultiplierCLM_littlewoodPaley_sq_rpow`)
  bounds `‖u(t)‖_r` by the `L^r` norm of `(∑ₗ |Pₗ u(t)|²)^{1/2}`, and since `q, r ≥ 2`,
  Minkowski's inequality for square sums (`MeasureTheory.eLpNorm_tsum_sq_rpow_le`), first in
  `L^r_x` and then in `L^q_t`, leaves `(∑ₗ ‖Pₗ u‖²_{L^q_t L^r_x})^{1/2}`
  (`ContDiffBump.exists_eLpNorm_eLpNorm_le_mul_tsum_eLpNorm_eLpNorm_fourierMultiplierCLM_sq_rpow`).
  Each block `Pₗ u` is bounded as above by `C 2^{l(γ + γ₁ - 1)} ‖Pₗ F‖_{L^{p₁}_t L^{r₁'}_x}`. No
  Littlewood–Paley inequality is needed on the side of the forcing, so `r₁ = ∞` is allowed there.

## Main declarations

* `ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le`:
  the frequency-localized retarded estimate, at every pair `(q, r)` and `(q₁, r₁)` as above.
* `ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum`: the
  retarded Strichartz estimate for the wave equation with forcing in the dyadic `ℓ¹` class.
* `ContDiffBump.exists_eLpNorm_top_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum`: the
  same estimate at the pairs `(∞, r)`.
* `ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_sq_rpow` and
  `ContDiffBump.exists_eLpNorm_top_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_sq_rpow`:
  the retarded Strichartz estimates with forcing in square-sum form, for `r < ∞`.

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

variable [MeasurableSpace E] [BorelSpace E]

/-! ### The frequency-localized estimate at the pairs `(2, r)` -/

/-- The retarded estimate with the forcing measured along any pair `(2, r₁)` in dimension `n ≥ 4`,
from the one along the endpoint pair `(2, r₀)`, `r₀ ≤ r₁`: some dyadic multiplier `Qⱼ` has
`Pⱼ Qⱼ = Pⱼ`, so `F` may be replaced by `Qⱼ F`, and by Bernstein's inequality `Qⱼ` is bounded from
`L^{r₁'}` to `L^{r₀'}` with norm a constant times `2^{jn (1/r₀ - 1/r₁)}`. -/
private theorem exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_of_sharp_output
    {q r : ℝ≥0∞} (hq : 2 ≤ q) (hq_top : q ≠ ∞)
    (hqr : 2 * (q⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq2 : q = 2 → 3 < Module.finrank ℝ E ∧
      1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2)
    {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁] [r₁'.HolderConjugate r₁] (hq₁ : 2 ≤ q₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁2 : q₁ = 2 → 3 < Module.finrank ℝ E) :
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
  rcases ne_or_eq q₁ 2 with hq₁2' | rfl
  · exact φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le_of_sharp
      hq hq_top hqr hq2 hq₁ hqr₁ fun h ↦ absurd h hq₁2'
  have hn := hq₁2 rfl
  have h2 : ((2 : ℝ≥0∞)⁻¹).toReal = 2⁻¹ := by simp
  rw [h2] at hqr₁
  -- The endpoint exponent `r₀ ≤ r₁`, with Hölder conjugate `r₀' ≥ r₁'`.
  obtain ⟨r₀, hr₀, hr₀r₁⟩ := exists_waveEndpoint_le_of_le (by exact_mod_cast hn)
    (ENNReal.HolderConjugate.ne_zero r₁ r₁') (le_of_eq_of_le (by ring) hqr₁)
  have hr₀2 := (two_le_and_ne_top_of_waveEndpoint (by exact_mod_cast hn) hr₀).1
  have := ENNReal.HolderConjugate.inv_one_sub_inv' (one_le_two.trans hr₀2)
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le_of_sharp
      (p₁ := p₁) (r₁' := (1 - r₀⁻¹)⁻¹) hq hq_top hqr hq2 le_rfl (by rw [h2]; linarith)
      fun _ ↦ ⟨hn, hr₀⟩
  obtain ⟨σ, hσ⟩ := φ.exists_fourierMultiplierCLM_dyadicMultiplier_eq (F := ℂ)
  have hB := ENNReal.coe_toNNReal
    (φ.memLp_fourierInv_dyadicDilate σ 0 (1 + (1 - r₀⁻¹)⁻¹⁻¹ - r₁'⁻¹)⁻¹).eLpNorm_ne_top
  -- Passing from `L^{r₁'}` to `L^{r₀'}` moves the forcing's scaling exponent from `r₀` to `r₁`.
  have hγ (x c : ℝ) :
      x + ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r₁⁻¹).toReal - c) - 1 =
        x + ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r₀⁻¹).toReal - c) - 1 +
          Module.finrank ℝ E * ((r₀⁻¹).toReal - (r₁⁻¹).toReal) := by ring
  refine ⟨C * (eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate σ 0)) (1 + (1 - r₀⁻¹)⁻¹⁻¹ - r₁'⁻¹)⁻¹ volume).toNNReal,
    fun j m hm F hF ↦ ?_⟩
  -- `Pⱼ Pⱼ Qⱼ F(s) = Pⱼ Pⱼ F(s)`: the estimate along `(2, r₀)` applies to `Qⱼ F`, and Bernstein's
  -- inequality from `L^{r₁'}` to `L^{r₀'}` bounds `Qⱼ F` at each time.
  have h := hC j m hm _ ((φ.dyadicMultiplier ℂ σ j).integrable_comp hF)
  simp only [hσ j m hm] at h
  refine h.trans ((mul_le_mul_right (eLpNorm_eLpNorm_apply_le (φ.dyadicMultiplier ℂ σ j).continuous
    (fun g ↦ φ.eLpNorm_dyadicMultiplier_le_of_le σ j g (ENNReal.HolderConjugate.one_le r₁' r₁)
      (ENNReal.HolderConjugate.le_inv_one_sub_inv (q' := r₁') hr₀r₁))
    hF.aestronglyMeasurable) _).trans_eq ?_)
  rw [ENNReal.HolderConjugate.inv_toReal_sub_inv_toReal_inv_one_sub_inv (q := r₁) (q' := r₁')
      (one_le_two.trans hr₀2),
    ENNReal.coe_mul, hB, hγ, ENNReal.ofReal_rpow_add (zpow_pos two_pos j)]
  ring

/-- **The retarded Strichartz estimate for the frequency-localized wave Duhamel operator** in
mixed norm, with the forcing measured along a second admissible pair. Let `E` have dimension `n`,
let `Pⱼ` be the `L²` Fourier multiplier with the Littlewood–Paley cutoff `ψⱼ` built from `φ` as
symbol, let `(q, r)` be wave-admissible, `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 ≤ q < ∞`,
and let `(q₁, r₁)` be wave-admissible with `2 ≤ q₁ ≤ ∞`, with Hölder conjugates `p₁` and `r₁'`.
The time exponent `2` is allowed, on either side or on both, in dimension `n ≥ 4`; the pairs
`(2, r)` are those with `r` at least the endpoint exponent `2 (n - 1) / (n - 3)`, `r = ∞` included.
Put `γ = n / 2 - n / r - 1 / q` and `γ₁ = n / 2 - n / r₁ - 1 / q₁`. There is `C` such that for
every `j ∈ ℤ` and every forcing term `F : ℝ → L²(E)` that is integrable in time,

`‖∫_{s < t} D⁻¹ sin((t - s)D) Pⱼ Pⱼ F(s) ds‖_{L^q_t L^r_x}`
`  ≤ C 2^{j(γ + γ₁ - 1)} ‖F‖_{L^{p₁}_t L^{r₁'}_x}`.

The pair `(q₁, r₁) = (q, r)` gives the exponent `2γ - 1`, and the pairs `(∞, r₁)` measure the
forcing in `L¹_t L^{r₁'}_x`, the energy pair `(∞, 2)` among them. -/
theorem exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le
    {q r : ℝ≥0∞} (hq : 2 ≤ q) (hq_top : q ≠ ∞)
    (hqr : 2 * (q⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq2 : q = 2 → 3 < Module.finrank ℝ E)
    {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁] [r₁'.HolderConjugate r₁] (hq₁ : 2 ≤ q₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁2 : q₁ = 2 → 3 < Module.finrank ℝ E) :
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
  rcases ne_or_eq q 2 with hq2' | rfl
  · exact φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_of_sharp_output hq
      hq_top hqr (fun h ↦ absurd h hq2') hq₁ hqr₁ hq₁2
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ _ _ ↦ by simp [eLpNorm_exponent_zero, Lp.aestronglyMeasurable]⟩
  have hn := hq2 rfl
  have h2 : ((2 : ℝ≥0∞)⁻¹).toReal = 2⁻¹ := by simp
  rw [h2] at hqr
  -- The endpoint exponent `r₀ ≤ r`.
  obtain ⟨r₀, hr₀, hr₀r⟩ :=
    exists_waveEndpoint_le_of_le (by exact_mod_cast hn) hr0 (le_of_eq_of_le (by ring) hqr)
  have hr₀2 := (two_le_and_ne_top_of_waveEndpoint (by exact_mod_cast hn) hr₀).1
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_of_sharp_output (p₁ := p₁)
      (r₁' := r₁') le_rfl (by simp) (by rw [h2]; linarith) (fun _ ↦ ⟨hn, hr₀⟩) hq₁ hqr₁ hq₁2
  obtain ⟨σ, hσ⟩ := φ.exists_fourierMultiplierCLM_dyadicMultiplier_eq (F := ℂ)
  have hB := ENNReal.coe_toNNReal
    (φ.memLp_fourierInv_dyadicDilate σ 0 (1 + r⁻¹ - r₀⁻¹)⁻¹).eLpNorm_ne_top
  -- Passing from `L^{r₀}` to `L^r` moves the scaling exponent of the solution from `r₀` to `r`.
  have hγ (x c : ℝ) :
      (Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r⁻¹).toReal - c + x - 1 =
        Module.finrank ℝ E * ((r₀⁻¹).toReal - (r⁻¹).toReal) +
        ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r₀⁻¹).toReal - c + x - 1) := by ring
  refine ⟨(eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate σ 0)) (1 + r⁻¹ - r₀⁻¹)⁻¹ volume).toNNReal * C,
    fun j m hm F hF ↦ ?_⟩
  -- `Qⱼ` fixes the retarded integral, whose integrand lies in the range of `Pⱼ`.
  have hQ (t : ℝ) : φ.dyadicMultiplier ℂ σ j (∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
      (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s)))) =
        ∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
          (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))) := by
    rw [← ContinuousLinearMap.integral_comp_comm _
      (φ.integrable_waveSinPropagator_sub_littlewoodPaley hm
        ((Lp.fourierMultiplierCLM ℂ m).integrable_comp hF) t).integrableOn]
    refine setIntegral_congr_fun measurableSet_Iio fun s _ ↦ ?_
    rw [dyadicMultiplier_def, fourierMultiplierCLM_waveSinPropagator_apply,
      Lp.fourierMultiplierCLM_fourierMultiplierCLM_comm, ← dyadicMultiplier_def, hσ j m hm]
  -- Bernstein's inequality from `L^{r₀}` to `L^r` at each time, then the estimate at `(2, r₀)`.
  have h := eLpNorm_eLpNorm_apply_le (φ.dyadicMultiplier ℂ σ j).continuous
    (fun g ↦ φ.eLpNorm_dyadicMultiplier_le_of_le σ j g (one_le_two.trans hr₀2) hr₀r)
    (aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub
      ((Lp.fourierMultiplierCLM ℂ m).integrable_comp
        ((Lp.fourierMultiplierCLM ℂ m).integrable_comp hF)).aestronglyMeasurable) (q := 2)
  simp only [hQ] at h
  refine h.trans ((mul_le_mul_right (hC j m hm F hF) _).trans_eq ?_)
  rw [ENNReal.coe_mul, hB, ← ENNReal.toReal_inv, ← ENNReal.toReal_inv, hγ,
    ENNReal.ofReal_rpow_add (zpow_pos two_pos j)]
  ring

/-! ### The retarded estimate -/

variable [Nontrivial E]

omit [Nontrivial E] in
/-- At each time, the block `Pₗ u(t)` of the retarded Duhamel integral `u(t)` satisfies
`‖Pₗ u(t)‖_r ≤ ∑_{|d| < L} ‖Φ_{d + l, l}(t)‖_r`, where `Φⱼₗ` is the retarded integral of
`Pⱼ Pⱼ Qₗ Pₗ F`: the block commutes with the integral and with the propagator, and
`Pₗ = ∑_{|d| < L} P_{d + l} P_{d + l} Qₗ Pₗ`. -/
private theorem eLpNorm_fourierMultiplierCLM_setIntegral_Iio_waveSinPropagator_sub_le_sum
    {L : ℕ}
    (hL : ∀ j k : ℤ, j + L ≤ k → ∀ ξ : E, φ.littlewoodPaley j ξ * φ.littlewoodPaley k ξ = 0)
    {m : ℤ → Lp ℂ ∞ (volume : Measure E)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    {F : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : Integrable F) {r : ℝ≥0∞} (hr : 1 ≤ r) (l : ℤ)
    (t : ℝ) :
    eLpNorm (Lp.fourierMultiplierCLM ℂ (m l) (∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
        Lp ℂ 2 (volume : Measure E))) r volume ≤
      ∑ d ∈ Finset.Ioo (-(L : ℤ)) L, eLpNorm ((∫ s in Set.Iio t,
        waveSinPropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ (m (d + l))
          (Lp.fourierMultiplierCLM ℂ (m (d + l))
            (φ.dyadicMultiplier ℂ φ.invSumSq l (Lp.fourierMultiplierCLM ℂ (m l) (F s))))) :
          Lp ℂ 2 (volume : Measure E))) r volume := by
  by_cases hint : IntegrableOn (fun s ↦ waveSinPropagator ℂ (t - s) (F s)) (Set.Iio t)
  · rw [← ContinuousLinearMap.integral_comp_comm _ hint]
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
  · rw [integral_undef hint, map_zero, eLpNorm_congr_ae (Lp.coeFn_zero _ _ _), eLpNorm_zero]
    exact zero_le

/-- At each time, the retarded Duhamel integral `u(t)` satisfies
`‖u(t)‖_r ≤ ∑ₗ ∑_{|d| < L} ‖Φ_{d + l, l}(t)‖_r`, where `Φⱼₗ` is the retarded integral of
`Pⱼ Pⱼ Qₗ Pₗ F`: by `‖u(t)‖_r ≤ ∑ₗ ‖Pₗ u(t)‖_r` and the bound on each block. -/
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
          Lp ℂ 2 (volume : Measure E))) r volume :=
  (φ.eLpNorm_apply_le_tsum_eLpNorm_apply_fourierMultiplierCLM hm (ContinuousLinearMap.id ℂ _) _
    hr).trans (tsum_le_tsum fun l ↦
      φ.eLpNorm_fourierMultiplierCLM_setIntegral_Iio_waveSinPropagator_sub_le_sum hL hm hF hr l t)

omit [Nontrivial E] in
/-- The retarded integral `Φⱼₗ` of `Pⱼ Pⱼ Qₗ Pₗ F` has an almost everywhere measurable `L^r` norm
in time. -/
private theorem aemeasurable_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_dyadicMultiplier
    {m : ℤ → Lp ℂ ∞ (volume : Measure E)} {F : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hF : Integrable F) (r : ℝ≥0∞) (j l : ℤ) :
    AEMeasurable (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
      (Lp.fourierMultiplierCLM ℂ (m j) (Lp.fourierMultiplierCLM ℂ (m j)
        (φ.dyadicMultiplier ℂ φ.invSumSq l (Lp.fourierMultiplierCLM ℂ (m l) (F s))))) :
          Lp ℂ 2 (volume : Measure E))) r volume) volume :=
  (aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub
    ((Lp.fourierMultiplierCLM ℂ (m j) ∘L Lp.fourierMultiplierCLM ℂ (m j)).integrable_comp
      ((φ.dyadicMultiplier ℂ φ.invSumSq l).integrable_comp
        ((Lp.fourierMultiplierCLM ℂ (m l)).integrable_comp hF))).aestronglyMeasurable
    ).aemeasurable_eLpNorm_Lp .rfl r

omit [Nontrivial E] in
/-- The `L^q_t` norm of `∑_{|d| < L} ‖Φ_{d + l, l}(t)‖_r`, where `Φⱼₗ` is the retarded integral of
`Pⱼ Pⱼ Qₗ Pₗ F`, is at most `C K K₀ 2^{lσ} ‖Pₗ F‖_{L^{p₁}_t L^{r₁'}_x}`, given the
frequency-localized estimate with constant `C` and exponent `σ`, where `K` bounds `Qₗ` on `L^{r₁'}`
and `K₀ = ∑_{|d| < L} 2^{dσ}`. -/
private theorem eLpNorm_sum_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le
    {q r p₁ r₁' : ℝ≥0∞} (hq : 1 ≤ q) (hr₁' : 1 ≤ r₁') {σ : ℝ} {C : ℝ≥0}
    (hC : ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ G : ℝ → Lp ℂ 2 (volume : Measure E), Integrable G →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
            (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (G s))) :
              Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            eLpNorm (fun s ↦ eLpNorm (G s) r₁' volume) p₁ volume)
    (L : ℕ) {m : ℤ → Lp ℂ ∞ (volume : Measure E)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    {F : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : Integrable F) (l : ℤ) :
    eLpNorm (fun t ↦ ∑ d ∈ Finset.Ioo (-(L : ℤ)) L, eLpNorm ((∫ s in Set.Iio t,
        waveSinPropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ (m (d + l))
          (Lp.fourierMultiplierCLM ℂ (m (d + l))
            (φ.dyadicMultiplier ℂ φ.invSumSq l (Lp.fourierMultiplierCLM ℂ (m l) (F s))))) :
          Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
      C * eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate φ.invSumSq 0)) 1 volume *
        ((∑ d ∈ Finset.Ioo (-(L : ℤ)) L, (((2 : ℝ) ^ d) ^ σ).toNNReal : ℝ≥0) : ℝ≥0∞) *
        (ENNReal.ofReal (((2 : ℝ) ^ l) ^ σ) *
          eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m l) (F s)) r₁' volume) p₁
            volume) := by
  have hPF := (Lp.fourierMultiplierCLM ℂ (m l)).integrable_comp hF
  calc _ ≤ ∑ d ∈ Finset.Ioo (-(L : ℤ)) L, eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t,
        waveSinPropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ (m (d + l))
          (Lp.fourierMultiplierCLM ℂ (m (d + l))
            (φ.dyadicMultiplier ℂ φ.invSumSq l (Lp.fourierMultiplierCLM ℂ (m l) (F s))))) :
          Lp ℂ 2 (volume : Measure E))) r volume) q volume := by
        rw [← Finset.sum_fn]
        exact eLpNorm_sum_le hq
    _ ≤ ∑ d ∈ Finset.Ioo (-(L : ℤ)) L,
          C * eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate φ.invSumSq 0)) 1 volume *
            (ENNReal.ofReal (((2 : ℝ) ^ (d + l)) ^ σ) *
              eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m l) (F s)) r₁' volume) p₁
                volume) :=
        Finset.sum_le_sum fun d _ ↦ (hC (d + l) (m (d + l)) (hm (d + l)) _
          ((φ.dyadicMultiplier ℂ φ.invSumSq l).integrable_comp hPF)).trans <| by
            rw [mul_assoc, mul_assoc, mul_left_comm (eLpNorm _ 1 volume)]
            gcongr
            exact φ.eLpNorm_eLpNorm_dyadicMultiplier_le φ.invSumSq l hPF.aestronglyMeasurable hr₁'
    _ = _ := by
        rw [← Finset.mul_sum, sum_ofReal_two_zpow_add_rpow_mul]
        ring

/-- **Littlewood–Paley summation of the retarded estimates.** Let `1 ≤ q` and `1 ≤ r`. If the
retarded Duhamel integrals of the squared blocks `Pⱼ Pⱼ G` satisfy
`‖∫_{s < t} D⁻¹ sin((t - s)D) Pⱼ Pⱼ G(s) ds‖_{L^q_t L^r_x} ≤ C 2^{jσ} ‖G‖_{L^{p₁}_t L^{r₁'}_x}`
uniformly in `j`, then the retarded Duhamel integral `u` of every integrable `F` satisfies
`‖u‖_{L^q_t L^r_x} ≤ C' ∑ⱼ 2^{jσ} ‖Pⱼ F‖_{L^{p₁}_t L^{r₁'}_x}`. -/
private theorem exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_of_le
    {q r p₁ r₁' : ℝ≥0∞} (hq : 1 ≤ q) (hr : 1 ≤ r) (hr₁' : 1 ≤ r₁') {σ : ℝ} {C : ℝ≥0}
    (hC : ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ G : ℝ → Lp ℂ 2 (volume : Measure E), Integrable G →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
            (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (G s))) :
              Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            eLpNorm (fun s ↦ eLpNorm (G s) r₁' volume) p₁ volume) :
    ∃ C' : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
            Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
          C' * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (F s)) r₁' volume) p₁
              volume := by
  obtain ⟨L, hL⟩ := φ.exists_littlewoodPaley_mul_eq_zero φ
  have hK := ENNReal.coe_toNNReal (φ.memLp_fourierInv_dyadicDilate φ.invSumSq 0 1).eLpNorm_ne_top
  set K := eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate φ.invSumSq 0)) 1 volume
  set S := Finset.Ioo (-(L : ℤ)) L
  refine ⟨C * K.toNNReal * ∑ d ∈ S, (((2 : ℝ) ^ d) ^ σ).toNNReal, fun m hm F hF ↦ ?_⟩
  -- `‖u(t)‖_r ≤ ∑ₗ bₗ(t)` with `bₗ(t) = ∑_{|d| < L} ‖Φ_{d + l, l}(t)‖_r`; then Minkowski's
  -- inequality in `L^q_t` and the bound on each `‖bₗ‖_{L^q_t}`.
  have hpt := φ.eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_sum hL hm hF hr
  calc eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
          Lp ℂ 2 (volume : Measure E))) r volume) q volume
      ≤ eLpNorm (fun t ↦ ∑' l, ∑ d ∈ S, eLpNorm ((∫ s in Set.Iio t,
        waveSinPropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ (m (d + l))
          (Lp.fourierMultiplierCLM ℂ (m (d + l))
            (φ.dyadicMultiplier ℂ φ.invSumSq l (Lp.fourierMultiplierCLM ℂ (m l) (F s))))) :
          Lp ℂ 2 (volume : Measure E))) r volume) q volume :=
        eLpNorm_mono_eNorm ((aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub
          hF.aestronglyMeasurable).aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable
          fun t ↦ by simpa only [eNorm_eq_self] using hpt t
    _ ≤ ∑' l, eLpNorm (fun t ↦ ∑ d ∈ S, eLpNorm ((∫ s in Set.Iio t,
        waveSinPropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ (m (d + l))
          (Lp.fourierMultiplierCLM ℂ (m (d + l))
            (φ.dyadicMultiplier ℂ φ.invSumSq l (Lp.fourierMultiplierCLM ℂ (m l) (F s))))) :
          Lp ℂ 2 (volume : Measure E))) r volume) q volume :=
        eLpNorm_tsum_le (fun l ↦ Finset.aemeasurable_fun_sum _ fun d _ ↦
          φ.aemeasurable_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_dyadicMultiplier hF r
            (d + l) l) hq
    _ ≤ ∑' l, C * K * ((∑ d ∈ S, (((2 : ℝ) ^ d) ^ σ).toNNReal : ℝ≥0) : ℝ≥0∞) *
          (ENNReal.ofReal (((2 : ℝ) ^ l) ^ σ) * eLpNorm (fun s ↦
            eLpNorm (Lp.fourierMultiplierCLM ℂ (m l) (F s)) r₁' volume) p₁ volume) :=
        tsum_le_tsum fun l ↦
          φ.eLpNorm_sum_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le hq hr₁' hC L hm hF l
    _ = _ := by
        rw [ENNReal.tsum_mul_left, ENNReal.coe_mul, ENNReal.coe_mul, hK]

/-- **The retarded Strichartz estimate for the wave equation with Besov forcing.** Let `E` be
nontrivial of dimension `n`, let `Pⱼ` be the `L²` Fourier multiplier with the Littlewood–Paley
cutoff `ψⱼ` built from `φ` as symbol, let `(q, r)` be wave-admissible,
`2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 ≤ q < ∞`, and let `(q₁, r₁)` be wave-admissible with
`2 ≤ q₁ ≤ ∞`, with Hölder conjugates `p₁` and `r₁'`, where the time exponent `2` is allowed, on
either side or on both, in dimension `n ≥ 4`: the pairs `(2, r)` with `r` at least the endpoint
exponent `2 (n - 1) / (n - 3)`, `r = ∞` included. Put
`γ = n / 2 - n / r - 1 / q` and `γ₁ = n / 2 - n / r₁ - 1 / q₁`. There is `C` such that for every
integrable forcing term `F : ℝ → L²(E)`, the retarded Duhamel integral
`u(t) = ∫_{s < t} D⁻¹ sin((t - s)D) F(s) ds`, the solution of `∂ₜ²u - Δu = F` with zero data at
`t = -∞`, satisfies

`‖u‖_{L^q_t L^r_x} ≤ C ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Pⱼ F‖_{L^{p₁}_t L^{r₁'}_x}`.

Here `u(t)` is a Bochner integral, taken to be `0` where it does not exist. -/
theorem exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum
    {q r : ℝ≥0∞} (hq : 2 ≤ q) (hq_top : q ≠ ∞)
    (hqr : 2 * (q⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq2 : q = 2 → 3 < Module.finrank ℝ E)
    {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁] [r₁'.HolderConjugate r₁] (hq₁ : 2 ≤ q₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁2 : q₁ = 2 → 3 < Module.finrank ℝ E) :
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
  obtain ⟨-, hr2⟩ :=
    two_le_finrank_of_waveAdmissible_of_two_le hq hq_top hr0 hqr Module.finrank_pos
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le
      (p₁ := p₁) (r₁' := r₁') hq hq_top hqr hq2 hq₁ hqr₁ hq₁2
  exact φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_of_le
    (one_le_two.trans hq) (one_le_two.trans hr2) (ENNReal.HolderConjugate.one_le r₁' r₁) hC

/-- **The retarded Strichartz estimate for the wave equation at the pairs `(∞, r)` with Besov
forcing.** Let `E` be nontrivial of dimension `n`, let `Pⱼ` be the `L²` Fourier multiplier with
the Littlewood–Paley cutoff `ψⱼ` built from `φ` as symbol, let `2 ≤ r ≤ ∞` and let
`γ = n / 2 - n / r`. Let `(q₁, r₁)` be wave-admissible with `2 ≤ q₁ ≤ ∞` and `2 ≤ r₁`, with Hölder
conjugates `p₁` and `r₁'`, where `q₁ = 2` only if `1 + (n - 1) / r₁ = (n - 1) / 2` in dimension
`n ≥ 4`, and put `γ₁ = n / 2 - n / r₁ - 1 / q₁`. There is `C` such that for every integrable
forcing term `F : ℝ → L²(E)`, the retarded Duhamel integral
`u(t) = ∫_{s < t} D⁻¹ sin((t - s)D) F(s) ds` satisfies

`‖u‖_{L^∞_t L^r_x} ≤ C ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Pⱼ F‖_{L^{p₁}_t L^{r₁'}_x}`.

At `r = ∞` this bounds `u` uniformly in space and time. In dimension `n ≥ 2` the bound `2 ≤ r₁`
follows from wave-admissibility (`TauCeti.two_le_of_waveAdmissible`). -/
theorem exists_eLpNorm_top_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum
    {r : ℝ≥0∞} (hr : 2 ≤ r) {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁]
    [r₁'.HolderConjugate r₁] (hq₁ : 2 ≤ q₁) (hr₁ : 2 ≤ r₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁2 : q₁ = 2 → 3 < Module.finrank ℝ E ∧
      1 + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
            Lp ℂ 2 (volume : Measure E))) r volume) ∞ volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
            eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (F s)) r₁' volume) p₁
              volume := by
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_top_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le
      (p₁ := p₁) (r₁' := r₁') hr hq₁ hr₁ hqr₁ hq₁2
  exact φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_of_le le_top
    (one_le_two.trans hr) (ENNReal.HolderConjugate.one_le r₁' r₁) hC

/-! ### The retarded estimate in square-sum form -/

/-- **Littlewood–Paley summation of the retarded estimates in square-sum form.** Let `2 ≤ q`,
`2 ≤ r < ∞` and `1 ≤ r₁'`. If the retarded Duhamel integrals of the squared blocks `Pⱼ Pⱼ G`
satisfy
`‖∫_{s < t} D⁻¹ sin((t - s)D) Pⱼ Pⱼ G(s) ds‖_{L^q_t L^r_x} ≤ C 2^{jσ} ‖G‖_{L^{p₁}_t L^{r₁'}_x}`
uniformly in `j`, then the retarded Duhamel integral `u` of every integrable `F` satisfies
`‖u‖_{L^q_t L^r_x} ≤ C' (∑ⱼ 2^{2jσ} ‖Pⱼ F‖²_{L^{p₁}_t L^{r₁'}_x})^{1/2}`. -/
private theorem exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_sq_rpow_of_le
    {q r p₁ r₁' : ℝ≥0∞} (hq : 2 ≤ q) (hr : 2 ≤ r) (hr_top : r ≠ ∞) (hr₁' : 1 ≤ r₁') {σ : ℝ}
    {C : ℝ≥0}
    (hC : ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ G : ℝ → Lp ℂ 2 (volume : Measure E), Integrable G →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s)
            (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (G s))) :
              Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            eLpNorm (fun s ↦ eLpNorm (G s) r₁' volume) p₁ volume) :
    ∃ C' : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
            Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
          C' * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (F s)) r₁' volume) p₁
              volume) ^ 2) ^ (2⁻¹ : ℝ) := by
  obtain ⟨A, hA⟩ :=
    φ.exists_eLpNorm_eLpNorm_le_mul_tsum_eLpNorm_eLpNorm_fourierMultiplierCLM_sq_rpow
      (F := ℂ) (ρ := (volume : Measure ℝ)) hq hr hr_top
  obtain ⟨L, hL⟩ := φ.exists_littlewoodPaley_mul_eq_zero φ
  have hK := ENNReal.coe_toNNReal (φ.memLp_fourierInv_dyadicDilate φ.invSumSq 0 1).eLpNorm_ne_top
  set K := eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate φ.invSumSq 0)) 1 volume
  set S := Finset.Ioo (-(L : ℤ)) L
  set K₀ : ℝ≥0 := ∑ d ∈ S, (((2 : ℝ) ^ d) ^ σ).toNNReal
  refine ⟨A * (C * K.toNNReal * K₀), fun m hm F hF ↦ ?_⟩
  -- `bₗ(t) = ∑_{|d| < L} ‖Φ_{d + l, l}(t)‖_r` bounds `‖Pₗ u(t)‖_r`, where `Φⱼₗ` is the retarded
  -- integral of `Pⱼ Pⱼ Qₗ Pₗ F`.
  set b : ℤ → ℝ → ℝ≥0∞ := fun l t ↦ ∑ d ∈ S, eLpNorm ((∫ s in Set.Iio t,
        waveSinPropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ (m (d + l))
          (Lp.fourierMultiplierCLM ℂ (m (d + l))
            (φ.dyadicMultiplier ℂ φ.invSumSq l (Lp.fourierMultiplierCLM ℂ (m l) (F s))))) :
          Lp ℂ 2 (volume : Measure E))) r volume
  -- The square-function bound, the decomposition of each block and the bound on each
  -- `‖bₗ‖_{L^q_t}`.
  calc eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
          Lp ℂ 2 (volume : Measure E))) r volume) q volume
      ≤ A * (∑' l, eLpNorm (fun t ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m l)
          (∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) : Lp ℂ 2 (volume : Measure E)))
            r volume) q volume ^ 2) ^ (2⁻¹ : ℝ) :=
        hA m hm _ (aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub
          hF.aestronglyMeasurable)
    _ ≤ A * (∑' l, eLpNorm (b l) q volume ^ 2) ^ (2⁻¹ : ℝ) := by
        gcongr with l
        exact eLpNorm_mono_eNorm (((Lp.fourierMultiplierCLM ℂ (m l)).continuous
          |>.comp_aestronglyMeasurable (aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub
            hF.aestronglyMeasurable)).aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable
          fun t ↦ by
            simpa only [eNorm_eq_self] using
              φ.eLpNorm_fourierMultiplierCLM_setIntegral_Iio_waveSinPropagator_sub_le_sum hL hm hF
                (one_le_two.trans hr) l t
    _ ≤ A * (∑' l, (C * K * K₀ * (ENNReal.ofReal (((2 : ℝ) ^ l) ^ σ) * eLpNorm (fun s ↦
          eLpNorm (Lp.fourierMultiplierCLM ℂ (m l) (F s)) r₁' volume) p₁ volume)) ^ 2) ^
            (2⁻¹ : ℝ) := by
        gcongr with l
        exact φ.eLpNorm_sum_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le
          (one_le_two.trans hq) hr₁' hC L hm hF l
    _ = _ := by
        rw [ENNReal.tsum_mul_sq_rpow_inv_two, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_mul,
          hK]
        ring

/-- **The retarded Strichartz estimate for the wave equation with forcing in square-sum form.**
Let `E` be nontrivial of dimension `n`, let `Pⱼ` be the `L²` Fourier multiplier with the
Littlewood–Paley cutoff `ψⱼ` built from `φ` as symbol, let `(q, r)` be wave-admissible,
`2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 ≤ q < ∞` and `r < ∞`, and let `(q₁, r₁)` be
wave-admissible with `2 ≤ q₁ ≤ ∞`, with Hölder conjugates `p₁` and `r₁'`, where the time exponent
`2` is allowed, on either side or on both, in dimension `n ≥ 4`. Put `γ = n / 2 - n / r - 1 / q` and
`γ₁ = n / 2 - n / r₁ - 1 / q₁`. There is `C` such that for every integrable forcing term
`F : ℝ → L²(E)`, the retarded Duhamel integral `u(t) = ∫_{s < t} D⁻¹ sin((t - s)D) F(s) ds`
satisfies

`‖u‖_{L^q_t L^r_x} ≤ C (∑ⱼ 2^{2j(γ + γ₁ - 1)} ‖Pⱼ F‖²_{L^{p₁}_t L^{r₁'}_x})^{1/2}`.

The square sum is at most the `ℓ¹` sum of
`ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum`, so for `r < ∞`
this estimate is the stronger one. Here `u(t)` is a Bochner integral, taken to be `0` where it does
not exist. -/
theorem exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_sq_rpow
    {q r : ℝ≥0∞} (hq : 2 ≤ q) (hq_top : q ≠ ∞) (hr_top : r ≠ ∞)
    (hqr : 2 * (q⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq2 : q = 2 → 3 < Module.finrank ℝ E)
    {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁] [r₁'.HolderConjugate r₁] (hq₁ : 2 ≤ q₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁2 : q₁ = 2 → 3 < Module.finrank ℝ E) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
            Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
            eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (F s)) r₁' volume) p₁
              volume) ^ 2) ^ (2⁻¹ : ℝ) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ _ ↦ by simp [eLpNorm_exponent_zero, Lp.aestronglyMeasurable]⟩
  obtain ⟨-, hr2⟩ :=
    two_le_finrank_of_waveAdmissible_of_two_le hq hq_top hr0 hqr Module.finrank_pos
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le
      (p₁ := p₁) (r₁' := r₁') hq hq_top hqr hq2 hq₁ hqr₁ hq₁2
  exact φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_sq_rpow_of_le hq
    hr2 hr_top (ENNReal.HolderConjugate.one_le r₁' r₁) hC

/-- **The retarded Strichartz estimate for the wave equation at the pairs `(∞, r)` with forcing in
square-sum form.** Let `E` be nontrivial of dimension `n`, let `Pⱼ` be the `L²` Fourier multiplier
with the Littlewood–Paley cutoff `ψⱼ` built from `φ` as symbol, let `2 ≤ r < ∞` and let
`γ = n / 2 - n / r`. Let `(q₁, r₁)` be wave-admissible with `2 ≤ q₁ ≤ ∞` and `2 ≤ r₁`, with Hölder
conjugates `p₁` and `r₁'`, where `q₁ = 2` only if `1 + (n - 1) / r₁ = (n - 1) / 2` in dimension
`n ≥ 4`, and put `γ₁ = n / 2 - n / r₁ - 1 / q₁`. There is `C` such that for every integrable
forcing term `F : ℝ → L²(E)`, the retarded Duhamel integral
`u(t) = ∫_{s < t} D⁻¹ sin((t - s)D) F(s) ds` satisfies

`‖u‖_{L^∞_t L^r_x} ≤ C (∑ⱼ 2^{2j(γ + γ₁ - 1)} ‖Pⱼ F‖²_{L^{p₁}_t L^{r₁'}_x})^{1/2}`. -/
theorem exists_eLpNorm_top_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_sq_rpow
    {r : ℝ≥0∞} (hr : 2 ≤ r) (hr_top : r ≠ ∞) {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁]
    [r₁'.HolderConjugate r₁] (hq₁ : 2 ≤ q₁) (hr₁ : 2 ≤ r₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁2 : q₁ = 2 → 3 < Module.finrank ℝ E ∧
      1 + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
            Lp ℂ 2 (volume : Measure E))) r volume) ∞ volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
            eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (F s)) r₁' volume) p₁
              volume) ^ 2) ^ (2⁻¹ : ℝ) := by
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_top_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_littlewoodPaley_le
      (p₁ := p₁) (r₁' := r₁') hr hq₁ hr₁ hqr₁ hq₁2
  exact φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum_sq_rpow_of_le le_top
    hr hr_top (ENNReal.HolderConjugate.one_le r₁' r₁) hC

end ContDiffBump

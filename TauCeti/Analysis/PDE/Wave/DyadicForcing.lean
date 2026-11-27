/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.HomogeneousLittlewoodPaley
public import TauCeti.Analysis.PDE.Wave.InhomogeneousStrichartz
import Mathlib.Order.Filter.AtTopBot.Interval
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Analysis.SpecificLimits.DyadicSum
import TauCeti.MeasureTheory.Function.Lp.InfiniteSum
import TauCeti.MeasureTheory.Function.Lp.MixedNorm.Series

/-!
# The retarded wave integral of a forcing term given by its dyadic blocks

On a nontrivial real inner product space `E` of dimension `n`, let `D = √(-Δ)` and let `Pⱼ`,
`j ∈ ℤ`, be the homogeneous Littlewood–Paley blocks built from a bump function `φ`. For an
integrable forcing term `F : ℝ → L²(E)` the solution of `∂ₜ²u - Δu = F` with zero data at
`t = -∞` is the retarded Duhamel integral `u(t) = ∫_{s < t} D⁻¹ sin((t - s)D) F(s) ds`
(`TauCeti.waveSinPropagator`), and for wave-admissible pairs `(q, r)` and `(q₁, r₁)`, with Hölder
conjugates `p₁` and `r₁'` of `q₁` and `r₁`, it satisfies the retarded Strichartz estimate

`‖u‖_{L^q_t L^r_x} ≤ C ∑ⱼ 2^{jσ} ‖Pⱼ F‖_{L^{p₁}_t L^{r₁'}_x}`, `σ = γ + γ₁ - 1`,

where `γ` and `γ₁` are the scaling-critical regularities of the two pairs
(`ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum`). The right
side only involves the blocks of `F`, and it is finite for forcing terms that are not functions with
values in `L²`.

This file treats such forcing terms: `F(s)` is a tempered distribution for every time `s`, and it
is known only through its blocks `Gⱼ(s) = Pⱼ F(s)`, which are assumed to be functions in `L²(E)`,
integrable in time, with

`∑ⱼ 2^{jσ} ‖Gⱼ‖_{L^{p₁}_t L^{r₁'}_x} < ∞`.

The retarded integral of `F` itself has no a priori meaning, but each block has one, and the file
shows that the dyadic series of the retarded integrals of the blocks

`∑ⱼ ∫_{s < t} D⁻¹ sin((t - s)D) Gⱼ(s) ds`

converges: there is `U : ℝ → L^r`, determined for almost every `t`, such that the partial sums
converge to `U(t)` in `L^r` for almost every time `t` and to `U` in `L^q_t L^r_x`, with the
retarded Strichartz estimate

`‖U‖_{L^q_t L^r_x} ≤ C ∑ⱼ 2^{jσ} ‖Gⱼ‖_{L^{p₁}_t L^{r₁'}_x}`

and `C` independent of `F`. This holds at the wave-admissible pairs `(q, r)` with `2 ≤ q < ∞`, the
time exponent `2` in dimension `n ≥ 4` only
(`ContDiffBump.exists_tendsto_eLpNorm_eLpNorm_sub_sum_setIntegral_Iio_waveSinPropagator_sub`), and
at the pairs `(∞, r)`, `2 ≤ r ≤ ∞`, with `γ = n / 2 - n / r`
(`ContDiffBump.exists_tendsto_eLpNorm_top_eLpNorm_sub_sum_setIntegral_Iio_waveSinPropagator_sub`);
at `(∞, ∞)` the limit is bounded uniformly in space and time. The file does not show that `U`
solves the wave equation.

When the forcing is a function `f : ℝ → L²(E)` whose retarded integral exists at almost every
time, any such limit agrees with that retarded integral for almost every `t`
(`ContDiffBump.ae_ae_eq_setIntegral_Iio_waveSinPropagator_sub_of_tendsto`), so the dyadic series
extends the retarded integral of `L²` forcing terms. This is the counterpart, for the forcing, of
the evolutions of data in the homogeneous Besov spaces (`TauCeti.Analysis.PDE.Wave.BesovData`).

## The argument

Almost orthogonality of the blocks on `L²`
(`TemperedDistribution.exists_fourierMultiplierCLM_eq_zero_of_eq_homogeneousLittlewoodPaleyBlock`)
gives `L` such that `Pₖ Gⱼ(s) = Pₖ Pⱼ F(s) = 0` unless `|k - j| < L`. So the retarded Strichartz
estimate for the `L²` forcing term `Gⱼ` has at most `2L - 1` nonzero terms, and since the blocks
are bounded on `L^{r₁'}` uniformly in the scale
(`ContDiffBump.eLpNorm_fourierMultiplierCLM_littlewoodPaley_le`) it bounds the retarded integral
of `Gⱼ` by a constant times `2^{jσ} ‖Gⱼ‖_{L^{p₁}_t L^{r₁'}_x}`.
These bounds are summable, and a series with summable mixed norms converges
(`MeasureTheory.exists_tendsto_eLpNorm_eLpNorm_sub_sum_of_tsum_ne_top`).

For the comparison with `L²` forcing terms, `Pⱼ` commutes with `D⁻¹ sin((t - s)D)` and with the
integral, so the partial sums of the series are the partial sums `∑ⱼ Pⱼ u(t)`, which converge to
`u(t)` in `L²` (`ContDiffBump.tendsto_sum_fourierMultiplierCLM_littlewoodPaley`). Limits in `L²`
and in `L^r` are both limits in measure, so they agree almost everywhere
(`MeasureTheory.ae_eq_of_tendsto_eLpNorm_sub_sum_of_tendsto_sum`).

## Main declarations

* `ContDiffBump.exists_tendsto_eLpNorm_eLpNorm_sub_sum_setIntegral_Iio_waveSinPropagator_sub`: the
  dyadic series of the retarded integrals of the blocks converges, with the retarded Strichartz
  estimate, at the pairs with `2 ≤ q < ∞`.
* `ContDiffBump.exists_tendsto_eLpNorm_top_eLpNorm_sub_sum_setIntegral_Iio_waveSinPropagator_sub`:
  the same at the pairs `(∞, r)`.
* `ContDiffBump.ae_ae_eq_setIntegral_Iio_waveSinPropagator_sub_of_tendsto`: for an `L²` forcing
  term the sum is its retarded integral.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.6 and its proof.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
-/

public section

noncomputable section

open Filter MeasureTheory Topology TauCeti TemperedDistribution
open scoped ENNReal NNReal FourierTransform SchwartzMap

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (φ : ContDiffBump (0 : E))

/-- **The retarded estimate for a forcing term made of `j`-th blocks.** If the retarded Duhamel
integrals of integrable `L²` forcing terms `F` satisfy
`‖u‖_{L^q_t L^r_x} ≤ C ∑ₖ 2^{kσ} ‖Pₖ F‖_{L^{p₁}_t L^{r₁'}_x}`, then a forcing term `G` whose
values are `j`-th blocks of tempered distributions satisfies
`‖u‖_{L^q_t L^r_x} ≤ C' 2^{jσ} ‖G‖_{L^{p₁}_t L^{r₁'}_x}`, with `C'` independent of `j`. -/
private theorem exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_of_eq_block
    {q r p₁ r₁' : ℝ≥0∞} (hr₁' : 1 ≤ r₁') {σ : ℝ} {C : ℝ≥0}
    (hC : ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
            Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (F s)) r₁' volume) p₁
              volume) :
    ∃ C' : ℝ≥0, ∀ (j : ℤ) (G : ℝ → Lp ℂ 2 (volume : Measure E)), Integrable G →
      (∀ s, ∃ v : 𝓢'(E, ℂ), (G s : 𝓢'(E, ℂ)) = homogeneousLittlewoodPaleyBlock ℂ φ j v) →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (G s) :
            Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
          C' * (ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            eLpNorm (fun s ↦ eLpNorm (G s) r₁' volume) p₁ volume) := by
  obtain ⟨L, K, hLK⟩ :=
    exists_eLpNorm_eLpNorm_fourierMultiplierCLM_of_eq_homogeneousLittlewoodPaleyBlock (G := ℂ) φ
  set m : ℤ → Lp ℂ ∞ (volume : Measure E) := fun j ↦ (φ.memLp_ofReal_littlewoodPaley j ∞).toLp _
  have hm (j : ℤ) : m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ) :=
    (φ.memLp_ofReal_littlewoodPaley j ∞).coeFn_toLp
  refine ⟨C * K * ∑ d ∈ Finset.Ioo (-(L : ℤ)) L, (((2 : ℝ) ^ d) ^ σ).toNNReal,
    fun j G hG hblock ↦ ?_⟩
  -- Only the blocks `Pₖ` with `|k - j| < L` see `G`, and each costs at most the factor `K`.
  have h (k : ℤ) := hLK (p := p₁) hr₁' hG.aestronglyMeasurable (ae_of_all _ hblock) (hm k)
  refine (hC m hm G hG).trans ?_
  grw [tsum_ofReal_two_zpow_rpow_mul_le_of_eq_zero σ (fun k hk ↦ (h k).1 hk) fun k _ ↦ (h k).2]
  rw [ENNReal.coe_mul, ENNReal.coe_mul]
  exact le_of_eq (by ring)

/-- **Summation of the retarded estimates over the blocks of a forcing term.** If the retarded
Duhamel integrals of integrable `L²` forcing terms satisfy
`‖u‖_{L^q_t L^r_x} ≤ C ∑ₖ 2^{kσ} ‖Pₖ F‖_{L^{p₁}_t L^{r₁'}_x}`, then for a forcing term `F` given by
blocks `Gⱼ(s) = Pⱼ F(s)` in `L²`, integrable in time, with
`∑ⱼ 2^{jσ} ‖Gⱼ‖_{L^{p₁}_t L^{r₁'}_x} < ∞`, the series of the retarded integrals of the `Gⱼ`
converges, with the same estimate up to a constant. -/
private theorem exists_tendsto_of_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le
    {q r p₁ r₁' : ℝ≥0∞} [Fact (1 ≤ r)] (hq : 1 ≤ q) (hr₁' : 1 ≤ r₁') {σ : ℝ} {C : ℝ≥0}
    (hC : ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
            Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (F s)) r₁' volume) p₁
              volume) :
    ∃ C' : ℝ≥0, ∀ (F : ℝ → 𝓢'(E, ℂ)) (G : ℤ → ℝ → Lp ℂ 2 (volume : Measure E)),
      (∀ j s, (G j s : 𝓢'(E, ℂ)) = homogeneousLittlewoodPaleyBlock ℂ φ j (F s)) →
      (∀ j, Integrable (G j)) →
      ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
          eLpNorm (fun s ↦ eLpNorm (G j s) r₁' volume) p₁ volume ≠ ∞ →
      ∃ U : ℝ → Lp ℂ r (volume : Measure E),
        (∀ᵐ t, Tendsto (fun s : Finset ℤ ↦ eLpNorm (⇑(U t) - ⇑(∑ j ∈ s,
          ∫ τ in Set.Iio t, waveSinPropagator ℂ (t - τ) (G j τ))) r volume) atTop (𝓝 0)) ∧
        Tendsto (fun s : Finset ℤ ↦ eLpNorm (fun t ↦ eLpNorm (⇑(U t) - ⇑(∑ j ∈ s,
          ∫ τ in Set.Iio t, waveSinPropagator ℂ (t - τ) (G j τ))) r volume) q volume) atTop
            (𝓝 0) ∧
        eLpNorm (fun t ↦ ‖U t‖ₑ) q volume ≤ C' * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
          eLpNorm (fun s ↦ eLpNorm (G j s) r₁' volume) p₁ volume := by
  obtain ⟨C', hC'⟩ :=
    φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_of_eq_block hr₁' hC
  refine ⟨C', fun F G hG hint hS ↦ ?_⟩
  have hsum : ∑' j, eLpNorm (fun t ↦ eLpNorm ((∫ τ in Set.Iio t,
      waveSinPropagator ℂ (t - τ) (G j τ) : Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
        C' * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
          eLpNorm (fun s ↦ eLpNorm (G j s) r₁' volume) p₁ volume := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_le_tsum fun j ↦ hC' j (G j) (hint j) fun s ↦ ⟨F s, hG j s⟩
  obtain ⟨U, hae, hmix, hle⟩ := exists_tendsto_eLpNorm_eLpNorm_sub_sum_of_tsum_ne_top hq
    (g := fun j t ↦ ∫ τ in Set.Iio t, waveSinPropagator ℂ (t - τ) (G j τ))
    (fun j ↦ aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub
      (hint j).aestronglyMeasurable)
    (hsum.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hS.lt_top)).ne
  exact ⟨U, hae, hmix, hle.trans hsum⟩

variable [Nontrivial E]

/-- **The retarded wave integral of a forcing term given by its blocks.** Let `E` be nontrivial of
dimension `n`, let `Pⱼ` be the homogeneous Littlewood–Paley blocks built from `φ`, let `(q, r)` be
wave-admissible, `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 ≤ q < ∞`, and let `(q₁, r₁)` be
wave-admissible with `2 ≤ q₁ ≤ ∞`, with Hölder conjugates `p₁` and `r₁'`, where the time exponent
`2` is allowed, on either side or on both, in dimension `n ≥ 4`. Put `γ = n / 2 - n / r - 1 / q`
and `γ₁ = n / 2 - n / r₁ - 1 / q₁`. There is `C` such that the following holds for every family
`F(s)` of tempered distributions whose blocks `Gⱼ(s) = Pⱼ F(s)` are `L²` functions, integrable in
time, with `∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Gⱼ‖_{L^{p₁}_t L^{r₁'}_x} < ∞`: the dyadic series
`∑ⱼ ∫_{s < t} D⁻¹ sin((t - s)D) Gⱼ(s) ds` converges, to some `U : ℝ → L^r` in `L^r` for almost
every `t` and in `L^q_t L^r_x`, with

`‖U‖_{L^q_t L^r_x} ≤ C ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Gⱼ‖_{L^{p₁}_t L^{r₁'}_x}`. -/
theorem exists_tendsto_eLpNorm_eLpNorm_sub_sum_setIntegral_Iio_waveSinPropagator_sub
    {q r : ℝ≥0∞} [Fact (1 ≤ r)] (hq : 2 ≤ q) (hq_top : q ≠ ∞)
    (hqr : 2 * (q⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq2 : q = 2 → 3 < Module.finrank ℝ E)
    {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁] [r₁'.HolderConjugate r₁] (hq₁ : 2 ≤ q₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁2 : q₁ = 2 → 3 < Module.finrank ℝ E) :
    ∃ C : ℝ≥0, ∀ (F : ℝ → 𝓢'(E, ℂ)) (G : ℤ → ℝ → Lp ℂ 2 (volume : Measure E)),
      (∀ j s, (G j s : 𝓢'(E, ℂ)) = homogeneousLittlewoodPaleyBlock ℂ φ j (F s)) →
      (∀ j, Integrable (G j)) →
      ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
          eLpNorm (fun s ↦ eLpNorm (G j s) r₁' volume) p₁ volume ≠ ∞ →
      ∃ U : ℝ → Lp ℂ r (volume : Measure E),
        (∀ᵐ t, Tendsto (fun s : Finset ℤ ↦ eLpNorm (⇑(U t) - ⇑(∑ j ∈ s,
          ∫ τ in Set.Iio t, waveSinPropagator ℂ (t - τ) (G j τ))) r volume) atTop (𝓝 0)) ∧
        Tendsto (fun s : Finset ℤ ↦ eLpNorm (fun t ↦ eLpNorm (⇑(U t) - ⇑(∑ j ∈ s,
          ∫ τ in Set.Iio t, waveSinPropagator ℂ (t - τ) (G j τ))) r volume) q volume) atTop
            (𝓝 0) ∧
        eLpNorm (fun t ↦ ‖U t‖ₑ) q volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
            eLpNorm (fun s ↦ eLpNorm (G j s) r₁' volume) p₁ volume := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum
    (p₁ := p₁) (r₁' := r₁') hq hq_top hqr hq2 hq₁ hqr₁ hq₁2
  exact φ.exists_tendsto_of_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le
    (one_le_two.trans hq) (ENNReal.HolderConjugate.one_le r₁' r₁) hC

/-- **The retarded wave integral of a forcing term given by its blocks, at the pairs `(∞, r)`.**
Let `E` be nontrivial of dimension `n`, let `Pⱼ` be the homogeneous Littlewood–Paley blocks built
from `φ`, let `2 ≤ r ≤ ∞` and `γ = n / 2 - n / r`. Let `(q₁, r₁)` be wave-admissible with
`2 ≤ q₁ ≤ ∞` and `2 ≤ r₁`, with Hölder conjugates `p₁` and `r₁'`, where `q₁ = 2` only if
`1 + (n - 1) / r₁ = (n - 1) / 2` in dimension `n ≥ 4`, and put `γ₁ = n / 2 - n / r₁ - 1 / q₁`.
There is `C` such that the following holds for every family `F(s)` of tempered distributions whose
blocks `Gⱼ(s) = Pⱼ F(s)` are `L²` functions, integrable in time, with
`∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Gⱼ‖_{L^{p₁}_t L^{r₁'}_x} < ∞`: the dyadic series
`∑ⱼ ∫_{s < t} D⁻¹ sin((t - s)D) Gⱼ(s) ds` converges, to some `U : ℝ → L^r` in `L^r` for almost
every `t` and in `L^∞_t L^r_x`, with

`‖U‖_{L^∞_t L^r_x} ≤ C ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Gⱼ‖_{L^{p₁}_t L^{r₁'}_x}`.

At `r = ∞` this bounds the limit uniformly in space and time. -/
theorem exists_tendsto_eLpNorm_top_eLpNorm_sub_sum_setIntegral_Iio_waveSinPropagator_sub
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 2 ≤ r) {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁]
    [r₁'.HolderConjugate r₁] (hq₁ : 2 ≤ q₁) (hr₁ : 2 ≤ r₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁2 : q₁ = 2 → 3 < Module.finrank ℝ E ∧
      1 + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (F : ℝ → 𝓢'(E, ℂ)) (G : ℤ → ℝ → Lp ℂ 2 (volume : Measure E)),
      (∀ j s, (G j s : 𝓢'(E, ℂ)) = homogeneousLittlewoodPaleyBlock ℂ φ j (F s)) →
      (∀ j, Integrable (G j)) →
      ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
          eLpNorm (fun s ↦ eLpNorm (G j s) r₁' volume) p₁ volume ≠ ∞ →
      ∃ U : ℝ → Lp ℂ r (volume : Measure E),
        (∀ᵐ t, Tendsto (fun s : Finset ℤ ↦ eLpNorm (⇑(U t) - ⇑(∑ j ∈ s,
          ∫ τ in Set.Iio t, waveSinPropagator ℂ (t - τ) (G j τ))) r volume) atTop (𝓝 0)) ∧
        Tendsto (fun s : Finset ℤ ↦ eLpNorm (fun t ↦ eLpNorm (⇑(U t) - ⇑(∑ j ∈ s,
          ∫ τ in Set.Iio t, waveSinPropagator ℂ (t - τ) (G j τ))) r volume) ∞ volume) atTop
            (𝓝 0) ∧
        eLpNorm (fun t ↦ ‖U t‖ₑ) ∞ volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
            eLpNorm (fun s ↦ eLpNorm (G j s) r₁' volume) p₁ volume := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_top_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum
    (p₁ := p₁) (r₁' := r₁') hr hq₁ hr₁ hqr₁ hq₁2
  exact φ.exists_tendsto_of_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le le_top
    (ENNReal.HolderConjugate.one_le r₁' r₁) hC

/-- **The dyadic series extends the retarded integral of `L²` forcing terms.** Let
`f : ℝ → L²(E)` be a forcing term whose retarded integral
`u(t) = ∫_{s < t} D⁻¹ sin((t - s)D) f(s) ds` exists for almost every `t`. If the dyadic series
`∑ⱼ ∫_{s < t} D⁻¹ sin((t - s)D) Pⱼ f(s) ds` converges in `L^r` to `U(t)` for almost every `t`, then
`U(t) = u(t)` for almost every `t`. -/
theorem ae_ae_eq_setIntegral_Iio_waveSinPropagator_sub_of_tendsto {r : ℝ≥0∞} [Fact (1 ≤ r)]
    {m : ℤ → Lp ℂ ∞ (volume : Measure E)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    {f : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hf : ∀ᵐ t, IntegrableOn (fun s ↦ waveSinPropagator ℂ (t - s) (f s)) (Set.Iio t))
    {U : ℝ → Lp ℂ r (volume : Measure E)}
    (hU : ∀ᵐ t, Tendsto (fun s : Finset ℤ ↦ eLpNorm (⇑(U t) - ⇑(∑ j ∈ s,
      ∫ τ in Set.Iio t, waveSinPropagator ℂ (t - τ) (Lp.fourierMultiplierCLM ℂ (m j) (f τ))))
        r volume) atTop (𝓝 0)) :
    ∀ᵐ t, ⇑(U t) =ᵐ[volume] ⇑(∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (f s)) := by
  filter_upwards [hf, hU] with t hft ht
  -- Along the partial sums over `(-N, N]`, the series tends to `U(t)` in `L^r` and to `u(t)` in
  -- `L²`, since its partial sums are `∑ⱼ Pⱼ u(t)`.
  refine ae_eq_of_tendsto_eLpNorm_sub_sum_of_tendsto_sum ht (Finset.tendsto_Ioc_neg (R := ℤ))
    ((φ.tendsto_sum_fourierMultiplierCLM_littlewoodPaley hm _).congr fun N ↦ ?_)
  -- `Pⱼ` commutes with the propagator and the integral.
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← ContinuousLinearMap.integral_comp_comm _ hft]
  simp only [fourierMultiplierCLM_waveSinPropagator_apply]

end ContDiffBump

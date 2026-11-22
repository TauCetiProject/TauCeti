/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.Energy
public import TauCeti.Analysis.PDE.Wave.Strichartz
import TauCeti.Analysis.PDE.Strichartz.LittlewoodPaley
import TauCeti.Analysis.PDE.Wave.Endpoint
import TauCeti.Analysis.PDE.Wave.MixedNorm
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.Lp.LinftyAlgebra

/-!
# Strichartz estimates for the wave equation with homogeneous Sobolev data

On a nontrivial real inner product space `E` of dimension `n`, let `D = √(-Δ)`, let
`W₊(t) = exp(itD)` be the half-wave propagator (`TauCeti.halfWavePropagator`), and let `Pⱼ`,
`j ∈ ℤ`, be the `L²` Fourier multipliers with the homogeneous Littlewood–Paley cutoffs `ψⱼ`
(`ContDiffBump.littlewoodPaley`), supported where `‖ξ‖ ≈ 2^j`, as symbols. Let `(q, r)` be
wave-admissible, `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞` and `r < ∞`, and let
`γ = n / 2 - n / r - 1 / q` be its scaling-critical regularity. This file proves the
**Strichartz estimates on the whole time line** with data in the homogeneous Sobolev spaces
`\dot H^γ`, whose norm enters in its Littlewood–Paley form `(∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2}`:

* `‖W₊(t) f‖_{L^q_t L^r_x} ≤ C (∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2}`, and the same estimate for the backward
  propagator `W₋(t) = W₊(-t)`;
* `‖cos(tD) f + D⁻¹ sin(tD) g‖_{L^q_t L^r_x}`
  `  ≤ C ((∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2} + (∑ⱼ 2^{2j(γ - 1)} ‖Pⱼ g‖₂²)^{1/2})`
  for the solution of the free wave equation `∂ₜ²u = Δu` with data `u(0) = f` and `∂ₜu(0) = g`,
  together with the estimates for `cos(tD)` and `D⁻¹ sin(tD)` separately. Every strong solution
  of the free equation on an interval of times containing `0` agrees there with this solution
  for `f = u(0)` and `g = ∂ₜu(0)`, so it satisfies the estimate on that interval, with a
  constant independent of the interval.

For `W₊(t)` and `W₋(t)` the same estimates hold at the endpoint pair `q = 2`,
`r = 2 (n - 1) / (n - 3)` in dimension `n ≥ 4`, from the frequency-localized endpoint estimate of
`TauCeti.Analysis.PDE.Wave.Endpoint`. These are the estimates of Tao, Theorem 2.6, for finite `r`
and finite `q`, except that at the endpoint pair only `W₊(t)` and `W₋(t)` are treated. The square
sums are at most the `\dot B^γ_{2,1}` and `\dot B^{γ - 1}_{2,1}` norms of
`TauCeti.Analysis.PDE.Wave.HomogeneousStrichartz`, so for `r < ∞` these estimates are stronger.
At `r = ∞` the Littlewood–Paley inequality is not available, and the Besov estimates remain the
statement there; in particular the false embedding `\dot H^{n/2} ⊆ L^∞` is not asserted.

## The argument

The frequency-localized estimates
(`ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le`,
`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le` and
`ContDiffBump.exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le`) are summed over the
blocks by `ContDiffBump.exists_eLpNorm_eLpNorm_le_mul_tsum_sq_rpow`, and so is the endpoint
estimate `ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_endpoint`.
At each time, the Littlewood–Paley inequality in `L^r` bounds `‖W₊(t) f‖_r` by the `L^r` norm of
the square function `(∑ⱼ |W₊(t) Pⱼ f|²)^{1/2}`, since the propagators are Fourier multipliers and
commute with the blocks. Because `q, r ≥ 2`, Minkowski's inequality moves the square sum outside
the `L^r_x` norm and then outside the `L^q_t` norm, leaving the square sum of the
frequency-localized estimates. Strong solutions are identified with
`cos(tD) u(0) + D⁻¹ sin(tD) ∂ₜu(0)` by Duhamel's formula
(`TauCeti.IsWaveSolutionOn.eq_waveCosPropagator_add_waveSinPropagator_add_integral`).

## Main declarations

* `ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow`: the Strichartz
  estimate for `W₊(t)` with data in `\dot H^γ`.
* `ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_neg_le_tsum_sq_rpow`: the same estimate
  for `W₋(t) = W₊(-t)`.
* `ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow_of_endpoint` and
  `ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_neg_le_tsum_sq_rpow_of_endpoint`: the
  estimates for `W₊(t)` and `W₋(t)` at the endpoint pair `(2, 2 (n - 1) / (n - 3))`, `n ≥ 4`.
* `ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_sq_rpow` and
  `ContDiffBump.exists_eLpNorm_eLpNorm_waveSinPropagator_le_tsum_sq_rpow`: the estimates for
  `cos(tD) f` with `f ∈ \dot H^γ` and for `D⁻¹ sin(tD) g` with `g ∈ \dot H^{γ - 1}`.
* `ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum_sq_rpow`:
  the Strichartz estimate for the free wave equation with data `(f, g)`.
* `ContDiffBump.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_isWaveSolutionOn`: the same estimate
  for every strong solution of the free wave equation on an interval of times containing `0`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.6 and its proof.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), Section 6.
-/

public section

open scoped ENNReal NNReal
open MeasureTheory TauCeti

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (φ : ContDiffBump (0 : E))
  {q : ℝ≥0} {r : ℝ≥0∞}

/-- Sum frequency-localized mixed-norm estimates with weights `2^{jσ}` in square-sum form, for a
strongly continuous family `T(t)` of operators on `L²(E)` commuting with the Fourier multipliers,
over the Littlewood–Paley blocks, for a wave-admissible pair `(q, r)` with `r < ∞`. This is the
common step of the estimates for `W₊(t)`, `cos(tD)` and `D⁻¹ sin(tD)`. -/
private theorem exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_littlewoodPaley_le (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) (hr : r ≠ ∞) (σ : ℝ)
    (T : ℝ → Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hT : ∀ x, Continuous fun t ↦ T t x)
    (hcomm : ∀ t (n : Lp ℂ ∞ (volume : Measure E)) x,
      T t (Lp.fourierMultiplierCLM ℂ n x) = Lp.fourierMultiplierCLM ℂ n (T t x))
    (hloc : ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (T t (Lp.fourierMultiplierCLM ℂ m f)) r volume) q volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * ‖f‖ₑ) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (T t f) r volume) q volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ ↦ by simp [eLpNorm_exponent_zero, Lp.aestronglyMeasurable]⟩
  obtain ⟨-, -, hr2⟩ := two_le_finrank_of_waveAdmissible hq hr0 hqr Module.finrank_pos
  obtain ⟨C, hC⟩ := hloc
  obtain ⟨K, hK⟩ := φ.exists_eLpNorm_eLpNorm_le_mul_tsum_sq_rpow (F := ℂ) (β := ℝ)
    (ρ := volume) σ (q := q) (by exact_mod_cast hq.le) hr2 hr
  refine ⟨K * C, fun m hm f ↦ (hK m hm T (fun x ↦ (hT x).aestronglyMeasurable)
    (fun t k x ↦ hcomm t (m k) x) C (fun k x ↦ hC k (m k) (hm k) x) f).trans_eq ?_⟩
  push_cast
  ring

/-- **The Strichartz estimate for the half-wave propagator with data in `\dot H^γ`.** Let `E` be
nontrivial of dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, and let `Pⱼ`
be the `L²` Fourier multiplier with symbol `ψⱼ`. Let `(q, r)` be wave-admissible,
`2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞` and `r < ∞`, and let
`γ = n / 2 - n / r - 1 / q`. There is `C` such that for every `f ∈ L²(E)`,

`‖W₊(t) f‖_{L^q_t L^r_x} ≤ C (∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ t f) r volume) q volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) :=
  φ.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_littlewoodPaley_le hq hqr hr _ _
    (continuous_phasePropagator_apply _)
    (fun t n x ↦ (fourierMultiplierCLM_halfWavePropagator_apply t n x).symm) <|
      φ.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le hq
        (NNReal.HolderConjugate.conjExponent (one_lt_two.trans hq)).symm hqr

omit [Nontrivial E] in
/-- Reversing time does not change the mixed norm of `t ↦ W₊(t) f`, since `t ↦ -t` preserves
Lebesgue measure. -/
private theorem eLpNorm_eLpNorm_halfWavePropagator_neg (q : ℝ≥0∞)
    (f : Lp ℂ 2 (volume : Measure E)) :
    eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ (-t) f) r volume) q volume =
      eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ t f) r volume) q volume := by
  have hW : Continuous fun t ↦ halfWavePropagator ℂ t f := continuous_phasePropagator_apply _ _
  simpa only [Function.comp_def] using eLpNorm_comp_measurePreserving (p := q)
    (g := fun t ↦ eLpNorm (halfWavePropagator ℂ t f) r volume)
    (hW.aestronglyMeasurable.aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable
    (Measure.measurePreserving_neg (volume : Measure ℝ))

/-- **The Strichartz estimate for the backward half-wave propagator with data in `\dot H^γ`.**
Under the hypotheses of `ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow`,
for `W₋(t) = W₊(-t)` there is `C` such that for every `f ∈ L²(E)`,

`‖W₊(-t) f‖_{L^q_t L^r_x} ≤ C (∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_eLpNorm_halfWavePropagator_neg_le_tsum_sq_rpow (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ (-t) f) r volume) q volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow hq hqr hr
  exact ⟨C, fun m hm f ↦ (eLpNorm_eLpNorm_halfWavePropagator_neg _ f).trans_le (hC m hm f)⟩

/-- **The endpoint Strichartz estimate for the half-wave propagator with data in `\dot H^γ`.** Let
`E` have dimension `n ≥ 4`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, and let `Pⱼ`
be the `L²` Fourier multiplier with symbol `ψⱼ`. Let `r` be the endpoint exponent,
`1 + (n - 1) / r = (n - 1) / 2`, and let `γ = n / 2 - n / r - 1 / 2`. There is `C` such that for
every `f ∈ L²(E)`,

`‖W₊(t) f‖_{L²_t L^r_x} ≤ C (∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow_of_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ t f) r volume) 2 volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) := by
  obtain ⟨hr2, hr⟩ := two_le_and_ne_top_of_waveEndpoint (by exact_mod_cast hn) hr
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_endpoint hn ‹_›
  obtain ⟨K, hK⟩ := φ.exists_eLpNorm_eLpNorm_le_mul_tsum_sq_rpow (F := ℂ) (β := ℝ)
    (ρ := volume) ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)
    le_rfl hr2 hr
  refine ⟨K * C, fun m hm f ↦ (hK m hm _
    (fun x ↦ (continuous_phasePropagator_apply _ x).aestronglyMeasurable)
    (fun t k x ↦ (fourierMultiplierCLM_halfWavePropagator_apply t (m k) x).symm) C
    (fun k x ↦ hC k (m k) (hm k) x) f).trans_eq ?_⟩
  push_cast
  ring

/-- **The endpoint Strichartz estimate for the backward half-wave propagator with data in
`\dot H^γ`.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow_of_endpoint`, for
`W₋(t) = W₊(-t)` there is `C` such that for every `f ∈ L²(E)`,

`‖W₊(-t) f‖_{L²_t L^r_x} ≤ C (∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_eLpNorm_halfWavePropagator_neg_le_tsum_sq_rpow_of_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ (-t) f) r volume) 2 volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow_of_endpoint hn hr
  exact ⟨C, fun m hm f ↦ (eLpNorm_eLpNorm_halfWavePropagator_neg _ f).trans_le (hC m hm f)⟩

/-- **The Strichartz estimate for `cos(tD)` with data in `\dot H^γ`.** Let `E` be nontrivial of
dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, and let `Pⱼ` be the `L²`
Fourier multiplier with symbol `ψⱼ`. Let `(q, r)` be wave-admissible,
`2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞` and `r < ∞`, and let
`γ = n / 2 - n / r - 1 / q`. There is `C` such that for every `f ∈ L²(E)`,

`‖cos(tD) f‖_{L^q_t L^r_x} ≤ C (∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_sq_rpow (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t f) r volume) q volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) :=
  φ.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_littlewoodPaley_le hq hqr hr _ _
    continuous_waveCosPropagator_apply
    -- Fourier multipliers commute, since their symbols do.
    (fun t n x ↦ by
      rw [waveCosPropagator_def, Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply,
        Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply, Lp.smul_eq_mul, Lp.smul_eq_mul,
        mul_comm]) <|
      φ.exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le hq
        (NNReal.HolderConjugate.conjExponent (one_lt_two.trans hq)).symm hqr

/-- **The Strichartz estimate for `D⁻¹ sin(tD)` with data in `\dot H^{γ - 1}`.** Under the
hypotheses of `ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_sq_rpow`, there is `C`
such that for every `g ∈ L²(E)`,

`‖D⁻¹ sin(tD) g‖_{L^q_t L^r_x} ≤ C (∑ⱼ 2^{2j(γ - 1)} ‖Pⱼ g‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_eLpNorm_waveSinPropagator_le_tsum_sq_rpow (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ g : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveSinPropagator ℂ t g) r volume) q volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹ - 1)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) g‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) :=
  φ.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_littlewoodPaley_le hq hqr hr _ _
    continuous_waveSinPropagator_apply
    -- Fourier multipliers commute, since their symbols do.
    (fun t n x ↦ by
      rw [waveSinPropagator_def, Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply,
        Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply, Lp.smul_eq_mul, Lp.smul_eq_mul,
        mul_comm]) <|
      φ.exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le hq
        (NNReal.HolderConjugate.conjExponent (one_lt_two.trans hq)).symm hqr

/-- **The Strichartz estimate for the free wave equation with data in
`\dot H^γ × \dot H^{γ - 1}`.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_sq_rpow`, there is `C` such that for
all `f, g ∈ L²(E)`, the solution `u(t) = cos(tD) f + D⁻¹ sin(tD) g` of `∂ₜ²u = Δu` with
`u(0) = f` and `∂ₜu(0) = g` satisfies

`‖u‖_{L^q_t L^r_x} ≤ C ((∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2} + (∑ⱼ 2^{2j(γ - 1)} ‖Pⱼ g‖₂²)^{1/2})`. -/
theorem exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum_sq_rpow
    (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f g : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t f + waveSinPropagator ℂ t g) r volume) q
            volume ≤
          C * ((∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) +
            (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹ - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) g‖ₑ) ^ 2) ^ (2⁻¹ : ℝ)) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ _ ↦ by simp_rw [eLpNorm_exponent_zero (Lp.aestronglyMeasurable _)]; simp⟩
  obtain ⟨-, -, hr2⟩ := two_le_finrank_of_waveAdmissible hq hr0 hqr Module.finrank_pos
  obtain ⟨C₁, h₁⟩ := φ.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_sq_rpow hq hqr hr
  obtain ⟨C₂, h₂⟩ := φ.exists_eLpNorm_eLpNorm_waveSinPropagator_le_tsum_sq_rpow hq hqr hr
  refine ⟨C₁ + C₂, fun m hm f g ↦ ?_⟩
  have hu : Continuous fun t ↦ waveCosPropagator ℂ t f + waveSinPropagator ℂ t g :=
    (continuous_waveCosPropagator_apply f).add (continuous_waveSinPropagator_apply g)
  calc _ ≤ eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t f) r volume +
          eLpNorm (waveSinPropagator ℂ t g) r volume) q volume :=
        eLpNorm_mono_eNorm
          (hu.aestronglyMeasurable.aemeasurable_eLpNorm_Lp .rfl r).aestronglyMeasurable fun t ↦ by
            simp only [eNorm_eq_self]
            rw [eLpNorm_congr_ae (Lp.coeFn_add _ _)]
            exact eLpNorm_add_le (one_le_two.trans hr2)
    _ ≤ eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t f) r volume) q volume +
          eLpNorm (fun t ↦ eLpNorm (waveSinPropagator ℂ t g) r volume) q volume :=
        eLpNorm_add_le (by exact_mod_cast one_le_two.trans hq.le)
    _ ≤ _ := by
        grw [h₁ m hm f, h₂ m hm g, ENNReal.coe_add, add_mul, mul_add, mul_add]
        gcongr
        · exact le_self_add
        · exact le_add_self

/-- **The Strichartz estimate for strong solutions of the free wave equation with homogeneous
Sobolev data.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_sq_rpow`, there is `C` such that for
every interval `I` containing `0`, every strong solution `u` of `∂ₜ²u = Δu` on `I`, with velocity
`u'`, satisfies

`‖u‖_{L^q(I; L^r_x)} ≤ C ((∑ⱼ 2^{2jγ} ‖Pⱼ u(0)‖₂²)^{1/2} + (∑ⱼ 2^{2j(γ - 1)} ‖Pⱼ u'(0)‖₂²)^{1/2})`.
-/
theorem exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_isWaveSolutionOn (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (s : Set ℝ) [s.OrdConnected], 0 ∈ s →
      ∀ u u' u'' : ℝ → Lp ℂ 2 (volume : Measure E), IsWaveSolutionOn u u' u'' 0 s →
        eLpNorm (fun t ↦ eLpNorm (u t) r volume) q (volume.restrict s) ≤
          C * ((∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) (u 0)‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) +
            (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹ - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) (u' 0)‖ₑ) ^ 2) ^ (2⁻¹ : ℝ)) := by
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum_sq_rpow hq hqr hr
  refine ⟨C, fun m hm s _ h0 u u' u'' hu ↦ ?_⟩
  -- By Duhamel's formula with no forcing, `u(t) = cos(tD) u(0) + D⁻¹ sin(tD) u'(0)` on `s`.
  have hrep : ∀ᵐ t ∂volume.restrict s, eLpNorm (u t) r volume =
      eLpNorm (waveCosPropagator ℂ t (u 0) + waveSinPropagator ℂ t (u' 0)) r volume :=
    ae_restrict_of_forall_mem (Set.OrdConnected.measurableSet ‹_›) fun t ht ↦ by
      rw [hu.eq_waveCosPropagator_add_waveSinPropagator_add_integral h0 ht
        intervalIntegrable_const]
      simp
  rw [eLpNorm_congr_ae hrep]
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC m hm _ _)

end ContDiffBump

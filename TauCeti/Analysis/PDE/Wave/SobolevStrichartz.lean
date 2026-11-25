/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.Energy
public import TauCeti.Analysis.PDE.Wave.Strichartz
import TauCeti.Analysis.PDE.Strichartz.LittlewoodPaley
import TauCeti.Analysis.PDE.Wave.MixedNorm
import TauCeti.MeasureTheory.Function.Lp.MixedNorm

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

For `W₊(t)` and `W₋(t)` the same estimates hold at the pairs `q = 2`,
`2 (n - 1) / (n - 3) ≤ r < ∞` in dimension `n ≥ 4`; they are proved in
`TauCeti.Analysis.PDE.Wave.TimeExponentTwo`. All five estimates also hold in mixed norm at the
pairs `(∞, r)` with `2 ≤ r < ∞`, with `γ = n / 2 - n / r`; there they bound the `L^r` norms of the
free waves uniformly in time, as the Sobolev embedding `\dot H^γ ⊆ L^r` predicts. These are the
estimates of Tao, Theorem 2.6, for finite `r`, except that at `q = 2` only `W₊(t)` and `W₋(t)` are
treated. The square
sums are at most the `\dot B^γ_{2,1}` and `\dot B^{γ - 1}_{2,1}` norms of
`TauCeti.Analysis.PDE.Wave.HomogeneousStrichartz`, so for `r < ∞` these estimates are stronger.
At `r = ∞` the Littlewood–Paley inequality is not available, and the Besov estimates remain the
statement there; in particular the false embedding `\dot H^{n/2} ⊆ L^∞` is not asserted.

## The argument

The frequency-localized estimates
(`ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le`,
`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le` and
`ContDiffBump.exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le`) are summed over the
blocks by `ContDiffBump.exists_eLpNorm_eLpNorm_le_mul_tsum_sq_rpow`, and so are the estimates at
the pairs `(∞, r)`.
At each time, the Littlewood–Paley inequality in `L^r` bounds `‖W₊(t) f‖_r` by the `L^r` norm of
the square function `(∑ⱼ |W₊(t) Pⱼ f|²)^{1/2}`, since the propagators are Fourier multipliers and
commute with the blocks. Because `q, r ≥ 2`, Minkowski's inequality moves the square sum outside
the `L^r_x` norm and then outside the `L^q_t` norm, leaving the square sum of the
frequency-localized estimates. Strong solutions are identified with
`cos(tD) u(0) + D⁻¹ sin(tD) ∂ₜu(0)` by Duhamel's formula, which bounds their mixed norms by those of
this free solution (`TauCeti.IsWaveSolutionOn.eLpNorm_eLpNorm_restrict_le`).

## Main declarations

* `ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow`: the Strichartz
  estimate for `W₊(t)` with data in `\dot H^γ`.
* `ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_neg_le_tsum_sq_rpow`: the same estimate
  for `W₋(t) = W₊(-t)`.
* `ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_sq_rpow` and
  `ContDiffBump.exists_eLpNorm_eLpNorm_waveSinPropagator_le_tsum_sq_rpow`: the estimates for
  `cos(tD) f` with `f ∈ \dot H^γ` and for `D⁻¹ sin(tD) g` with `g ∈ \dot H^{γ - 1}`.
* `ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum_sq_rpow`:
  the Strichartz estimate for the free wave equation with data `(f, g)`.
* `ContDiffBump.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_isWaveSolutionOn`: the same estimate
  for every strong solution of the free wave equation on an interval of times containing `0`.
* `ContDiffBump.exists_eLpNorm_top_eLpNorm_halfWavePropagator_le_tsum_sq_rpow`,
  `ContDiffBump.exists_eLpNorm_top_eLpNorm_halfWavePropagator_neg_le_tsum_sq_rpow`,
  `ContDiffBump.exists_eLpNorm_top_eLpNorm_waveCosPropagator_le_tsum_sq_rpow`,
  `ContDiffBump.exists_eLpNorm_top_eLpNorm_waveSinPropagator_le_tsum_sq_rpow`,
  `ContDiffBump.exists_eLpNorm_top_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum_sq_rpow`
  and `ContDiffBump.exists_eLpNorm_top_eLpNorm_le_tsum_sq_rpow_of_isWaveSolutionOn`: the
  estimates at the pairs `(∞, r)`, `2 ≤ r < ∞`.

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
family `T(t)` of operators on `L²(E)` commuting with the Fourier multipliers, over the
Littlewood–Paley blocks, for `2 ≤ q` and `2 ≤ r < ∞`. This is the common step of the estimates
for `W₊(t)`, `cos(tD)` and `D⁻¹ sin(tD)`. -/
private theorem exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_littlewoodPaley_le {q : ℝ≥0∞}
    (hq : 2 ≤ q) (hr2 : 2 ≤ r) (hr : r ≠ ∞) (σ : ℝ)
    (T : ℝ → Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hT : ∀ x, AEStronglyMeasurable (fun t ↦ T t x))
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
  obtain ⟨C, hC⟩ := hloc
  obtain ⟨K, hK⟩ := φ.exists_eLpNorm_eLpNorm_le_mul_tsum_sq_rpow (F := ℂ) (β := ℝ)
    (ρ := volume) σ hq hr2 hr
  refine ⟨K * C, fun m hm f ↦ (hK m hm T hT (fun t k x ↦ hcomm t (m k) x) C
    (fun k x ↦ hC k (m k) (hm k) x) f).trans_eq ?_⟩
  push_cast
  ring

/-- `ContDiffBump.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_littlewoodPaley_le` for a strongly
continuous family `T(t)` and a wave-admissible pair `(q, r)` with `2 < q` and `r < ∞`. At `r = 0`
every mixed norm vanishes; otherwise wave-admissibility gives `2 ≤ r`. -/
private theorem exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_waveAdmissible (hq : 2 < q)
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
  exact φ.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_littlewoodPaley_le
    (by exact_mod_cast hq.le) hr2 hr σ T (fun x ↦ (hT x).aestronglyMeasurable) hcomm hloc

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
  φ.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_waveAdmissible hq hqr hr _ _
    (continuous_phasePropagator_apply _)
    (fun t n x ↦ (fourierMultiplierCLM_halfWavePropagator_apply t n x).symm) <|
      φ.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le hq
        (NNReal.HolderConjugate.conjExponent (one_lt_two.trans hq)).symm hqr

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
  exact ⟨C, fun m hm f ↦ ((continuous_phasePropagator_apply _ f).aestronglyMeasurable
    |>.eLpNorm_eLpNorm_comp_neg).trans_le (hC m hm f)⟩

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
  φ.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_waveAdmissible hq hqr hr _ _
    continuous_waveCosPropagator_apply
    (fun t n x ↦ (fourierMultiplierCLM_waveCosPropagator_apply t n x).symm) <|
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
  φ.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_waveAdmissible hq hqr hr _ _
    continuous_waveSinPropagator_apply
    (fun t n x ↦ (fourierMultiplierCLM_waveSinPropagator_apply t n x).symm) <|
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
  obtain ⟨C₁, h₁⟩ := φ.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_sq_rpow hq hqr hr
  obtain ⟨C₂, h₂⟩ := φ.exists_eLpNorm_eLpNorm_waveSinPropagator_le_tsum_sq_rpow hq hqr hr
  exact ⟨C₁ + C₂, fun m hm f g ↦
    eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le hq hqr (h₁ m hm f) (h₂ m hm g)⟩

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
  exact ⟨C, fun m hm s _ h0 u u' u'' hu ↦
    (hu.eLpNorm_eLpNorm_restrict_le h0).trans (hC m hm _ _)⟩

/-! ### The pairs `(∞, r)` with `r < ∞` -/

section TimeExponentTop

/-- **The Strichartz estimate for the half-wave propagator at the pairs `(∞, r)` with data in
`\dot H^γ`.** Let `E` be nontrivial of dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs
built from `φ`, and let `Pⱼ` be the `L²` Fourier multiplier with symbol `ψⱼ`. Let `2 ≤ r < ∞` and
let `γ = n / 2 - n / r`. There is `C` such that for every `f ∈ L²(E)`,

`‖W₊(t) f‖_{L^∞_t L^r_x} ≤ C (∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_top_eLpNorm_halfWavePropagator_le_tsum_sq_rpow (hr2 : 2 ≤ r)
    (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ t f) r volume) ∞ volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) :=
  φ.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_littlewoodPaley_le le_top hr2 hr _ _
    (fun x ↦ (continuous_phasePropagator_apply _ x).aestronglyMeasurable)
    (fun t n x ↦ (fourierMultiplierCLM_halfWavePropagator_apply t n x).symm) <|
      φ.exists_eLpNorm_top_eLpNorm_halfWavePropagator_littlewoodPaley_le hr2

/-- **The Strichartz estimate for the backward half-wave propagator at the pairs `(∞, r)` with data
in `\dot H^γ`.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_top_eLpNorm_halfWavePropagator_le_tsum_sq_rpow`, for
`W₋(t) = W₊(-t)` there is `C` such that for every `f ∈ L²(E)`,

`‖W₊(-t) f‖_{L^∞_t L^r_x} ≤ C (∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_top_eLpNorm_halfWavePropagator_neg_le_tsum_sq_rpow (hr2 : 2 ≤ r)
    (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ (-t) f) r volume) ∞ volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_top_eLpNorm_halfWavePropagator_le_tsum_sq_rpow hr2 hr
  exact ⟨C, fun m hm f ↦ ((continuous_phasePropagator_apply _ f).aestronglyMeasurable
    |>.eLpNorm_eLpNorm_comp_neg).trans_le (hC m hm f)⟩

/-- **The Strichartz estimate for `cos(tD)` at the pairs `(∞, r)` with data in `\dot H^γ`.** Under
the hypotheses of `ContDiffBump.exists_eLpNorm_top_eLpNorm_halfWavePropagator_le_tsum_sq_rpow`,
there is `C` such that for every `f ∈ L²(E)`,

`‖cos(tD) f‖_{L^∞_t L^r_x} ≤ C (∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_top_eLpNorm_waveCosPropagator_le_tsum_sq_rpow (hr2 : 2 ≤ r)
    (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t f) r volume) ∞ volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) :=
  φ.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_littlewoodPaley_le le_top hr2 hr _ _
    (fun x ↦ (continuous_waveCosPropagator_apply x).aestronglyMeasurable)
    (fun t n x ↦ (fourierMultiplierCLM_waveCosPropagator_apply t n x).symm) <|
      φ.exists_eLpNorm_top_eLpNorm_waveCosPropagator_littlewoodPaley_le hr2

/-- **The Strichartz estimate for `D⁻¹ sin(tD)` at the pairs `(∞, r)` with data in
`\dot H^{γ - 1}`.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_top_eLpNorm_halfWavePropagator_le_tsum_sq_rpow`, there is `C` such
that for every `g ∈ L²(E)`,

`‖D⁻¹ sin(tD) g‖_{L^∞_t L^r_x} ≤ C (∑ⱼ 2^{2j(γ - 1)} ‖Pⱼ g‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_top_eLpNorm_waveSinPropagator_le_tsum_sq_rpow (hr2 : 2 ≤ r)
    (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ g : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveSinPropagator ℂ t g) r volume) ∞ volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 1)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) g‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) :=
  φ.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_littlewoodPaley_le le_top hr2 hr _ _
    (fun x ↦ (continuous_waveSinPropagator_apply x).aestronglyMeasurable)
    (fun t n x ↦ (fourierMultiplierCLM_waveSinPropagator_apply t n x).symm) <|
      φ.exists_eLpNorm_top_eLpNorm_waveSinPropagator_littlewoodPaley_le hr2

/-- **The Strichartz estimate for the free wave equation at the pairs `(∞, r)` with data in
`\dot H^γ × \dot H^{γ - 1}`.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_top_eLpNorm_halfWavePropagator_le_tsum_sq_rpow`, there is `C` such
that for all `f, g ∈ L²(E)`, the solution `u(t) = cos(tD) f + D⁻¹ sin(tD) g` of `∂ₜ²u = Δu` with
`u(0) = f` and `∂ₜu(0) = g` satisfies

`‖u‖_{L^∞_t L^r_x} ≤ C ((∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2} + (∑ⱼ 2^{2j(γ - 1)} ‖Pⱼ g‖₂²)^{1/2})`. -/
theorem exists_eLpNorm_top_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum_sq_rpow
    (hr2 : 2 ≤ r) (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f g : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t f + waveSinPropagator ℂ t g) r volume) ∞
            volume ≤
          C * ((∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) +
            (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) g‖ₑ) ^ 2) ^ (2⁻¹ : ℝ)) := by
  obtain ⟨C₁, h₁⟩ := φ.exists_eLpNorm_top_eLpNorm_waveCosPropagator_le_tsum_sq_rpow hr2 hr
  obtain ⟨C₂, h₂⟩ := φ.exists_eLpNorm_top_eLpNorm_waveSinPropagator_le_tsum_sq_rpow hr2 hr
  exact ⟨C₁ + C₂, fun m hm f g ↦
    eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_of_one_le le_top
      (one_le_two.trans hr2) (h₁ m hm f) (h₂ m hm g)⟩

/-- **The Strichartz estimate at the pairs `(∞, r)` for strong solutions of the free wave equation
with homogeneous Sobolev data.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_top_eLpNorm_halfWavePropagator_le_tsum_sq_rpow`, there is `C` such
that for every interval `I` containing `0`, every strong solution `u` of `∂ₜ²u = Δu` on `I`, with
velocity `u'`, satisfies

`‖u‖_{L^∞(I; L^r_x)} ≤ C ((∑ⱼ 2^{2jγ} ‖Pⱼ u(0)‖₂²)^{1/2} + (∑ⱼ 2^{2j(γ - 1)} ‖Pⱼ u'(0)‖₂²)^{1/2})`.
-/
theorem exists_eLpNorm_top_eLpNorm_le_tsum_sq_rpow_of_isWaveSolutionOn (hr2 : 2 ≤ r)
    (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (s : Set ℝ) [s.OrdConnected], 0 ∈ s →
      ∀ u u' u'' : ℝ → Lp ℂ 2 (volume : Measure E), IsWaveSolutionOn u u' u'' 0 s →
        eLpNorm (fun t ↦ eLpNorm (u t) r volume) ∞ (volume.restrict s) ≤
          C * ((∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) (u 0)‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) +
            (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) (u' 0)‖ₑ) ^ 2) ^ (2⁻¹ : ℝ)) := by
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_top_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum_sq_rpow hr2 hr
  exact ⟨C, fun m hm s _ h0 u u' u'' hu ↦
    (hu.eLpNorm_eLpNorm_restrict_le h0).trans (hC m hm _ _)⟩

end TimeExponentTop

end ContDiffBump

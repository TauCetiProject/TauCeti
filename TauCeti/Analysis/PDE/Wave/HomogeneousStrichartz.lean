/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.Energy
public import TauCeti.Analysis.PDE.Wave.Strichartz
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Analysis.PDE.Strichartz.LittlewoodPaley
import TauCeti.Analysis.PDE.Wave.MixedNorm
import TauCeti.MeasureTheory.Function.Lp.MixedNorm

/-!
# Strichartz estimates for the wave equation with Besov data

On a nontrivial real inner product space `E` of dimension `n`, let `D = √(-Δ)`, let
`W₊(t) = exp(itD)` be the half-wave propagator (`TauCeti.halfWavePropagator`), and let `Pⱼ`,
`j ∈ ℤ`, be the `L²` Fourier multipliers with the homogeneous Littlewood–Paley cutoffs `ψⱼ`
(`ContDiffBump.littlewoodPaley`), supported where `‖ξ‖ ≈ 2^j`, as symbols. Let `(q, r)` be
wave-admissible, `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞`, and let
`γ = n / 2 - n / r - 1 / q` be its scaling-critical regularity. This file proves the
**Strichartz estimates on the whole time line** with data in homogeneous Besov spaces, written
through the blocks of the data:

* `‖W₊(t) f‖_{L^q_t L^r_x} ≤ C ∑ⱼ 2^{jγ} ‖Pⱼ f‖₂` in weak form, that is tested against
  `G ∈ L^{q'}_t L^{r'}_x`, and the same estimate for the backward propagator `W₋(t) = W₊(-t)`;
* `‖cos(tD) f + D⁻¹ sin(tD) g‖_{L^q_t L^r_x} ≤ C (∑ⱼ 2^{jγ} ‖Pⱼ f‖₂ + ∑ⱼ 2^{j(γ - 1)} ‖Pⱼ g‖₂)`
  for the solution of the free wave equation `∂ₜ²u = Δu` with data `u(0) = f` and `∂ₜu(0) = g`,
  together with the estimates for `cos(tD)` and `D⁻¹ sin(tD)` separately. Every strong solution
  of the free equation on an interval of times containing `0` agrees there with this solution
  for `f = u(0)` and `g = ∂ₜu(0)`, so it satisfies the estimate on that interval, with a
  constant independent of the interval.

The right-hand sides are the norms of the data in `\dot B^γ_{2,1}` and `\dot B^{γ - 1}_{2,1}`.
Since these are `ℓ¹` sums over the blocks rather than square functions, the pairs with `r = ∞` are
covered.

## The argument

For the half-wave propagator, the frequency-localized dual estimate
(`ContDiffBump.exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le`) bounds the blocks
of `g = ∫ W₊(-t) G(t) dt`: since the blocks commute with the propagator,
`Pₖ g = ∫ W₊(-t) Pₖ G(t) dt`, and `‖Pₖ g‖₂ ≤ C 2^{kγ} ‖G‖_{L^{q'}_t L^{r'}_x}` uniformly in `k`.
That is, `g ∈ \dot B^{-γ}_{2,∞}`. The pairing `∫ ⟪W₊(t) f, G(t)⟫ dt = ⟪f, g⟫` of `f` with `g` is
then bounded by the duality of the dyadic `ℓ¹` and `ℓ^∞` norms
(`ContDiffBump.exists_enorm_inner_le_mul_tsum`).

For `cos(tD)` and `D⁻¹ sin(tD)`, the frequency-localized mixed-norm estimates
(`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le` and
`ContDiffBump.exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le`) are summed over the
blocks by `ContDiffBump.exists_eLpNorm_eLpNorm_le_mul_tsum`. The duality argument does not apply
to `D⁻¹ sin(tD)` directly: its norm grows like `|t|`, so `∫ D⁻¹ sin(tD) G(t) dt` need not exist for
integrable `G`. Strong solutions are identified with `cos(tD) u(0) + D⁻¹ sin(tD) ∂ₜu(0)` by
Duhamel's formula
(`TauCeti.IsWaveSolutionOn.eq_waveCosPropagator_add_waveSinPropagator_add_integral`).

## Main declarations

* `ContDiffBump.exists_enorm_integral_inner_halfWavePropagator_le_tsum`: the Strichartz estimate
  for `W₊(t)` with data in `\dot B^γ_{2,1}`, in weak form.
* `ContDiffBump.exists_enorm_integral_inner_halfWavePropagator_neg_le_tsum`: the same estimate for
  `W₋(t) = W₊(-t)`.
* `ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum` and
  `ContDiffBump.exists_eLpNorm_eLpNorm_waveSinPropagator_le_tsum`: the estimates for `cos(tD) f`
  with `f ∈ \dot B^γ_{2,1}` and for `D⁻¹ sin(tD) g` with `g ∈ \dot B^{γ - 1}_{2,1}`.
* `ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum`: the
  Strichartz estimate for the free wave equation with data `(f, g)`.
* `ContDiffBump.exists_eLpNorm_eLpNorm_le_tsum_of_isWaveSolutionOn`: the same estimate for every
  strong solution of the free wave equation on an interval of times containing `0`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.6 and its proof.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), Section 6.
-/

public section

open scoped ENNReal NNReal InnerProductSpace
open MeasureTheory TauCeti

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (φ : ContDiffBump (0 : E))
  {p q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- **The Strichartz estimate for the half-wave propagator with data in `\dot B^γ_{2,1}`**, in weak
form. Let `E` be nontrivial of dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from
`φ`, and let `Pⱼ` be the `L²` Fourier multiplier with symbol `ψⱼ`. Let `(q, r)` be
wave-admissible, `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞`, let `p` and `r'` be the
Hölder conjugates of `q` and `r`, and let `γ = n / 2 - n / r - 1 / q`. There is `C` such that for
every `f ∈ L²(E)` and every almost everywhere strongly measurable `G : ℝ → L²(E)` for which
`t ↦ W₊(-t) G(t)` is integrable,

`|∫ ⟪W₊(t) f, G(t)⟫ dt| ≤ C (∑ⱼ 2^{jγ} ‖Pⱼ f‖₂) ‖G‖_{L^p_t L^{r'}_x}`.

This is `‖W₊(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖_{\dot B^γ_{2,1}}` tested against `G`. -/
theorem exists_enorm_integral_inner_halfWavePropagator_le_tsum (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (f : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)),
        AEStronglyMeasurable G → Integrable (fun t ↦ halfWavePropagator ℂ (-t) (G t)) →
        ‖∫ t, ⟪halfWavePropagator ℂ t f, G t⟫_ℂ‖ₑ ≤
          C * (∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C, hC⟩ := φ.exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le
    (r' := r') hq hpq hqr
  obtain ⟨K, hK⟩ := φ.exists_enorm_inner_le_mul_tsum (F := ℂ)
    ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)
  refine ⟨K * C, fun m hm f G hG hWG ↦ ?_⟩
  -- The pairing is `⟪f, g⟫` with `g = ∫ W₊(-t) G(t) dt`, since `W₊(t)* = W₊(-t)`.
  have hpair : ∫ t, ⟪halfWavePropagator ℂ t f, G t⟫_ℂ =
      ⟪f, ∫ t, halfWavePropagator ℂ (-t) (G t)⟫_ℂ := by
    rw [← integral_inner hWG f]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
    dsimp only
    rw [← adjoint_halfWavePropagator, ContinuousLinearMap.adjoint_inner_right]
  -- The blocks of `g` obey the frequency-localized dual estimate.
  have hblock : ∀ k : ℤ,
      ‖Lp.fourierMultiplierCLM ℂ (m k) (∫ t, halfWavePropagator ℂ (-t) (G t))‖ₑ ≤
        C * eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume *
          ENNReal.ofReal (((2 : ℝ) ^ k) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) := fun k ↦ by
    rw [← ContinuousLinearMap.integral_comp_comm _ hWG]
    simp only [fourierMultiplierCLM_halfWavePropagator_apply]
    refine (hC k (m k) (hm k) G hG).trans_eq ?_
    ring
  rw [hpair]
  refine (hK m hm f _ _ hblock).trans_eq ?_
  push_cast
  ring

/-- **The Strichartz estimate for the backward half-wave propagator with data in
`\dot B^γ_{2,1}`**, in weak form: under the hypotheses of
`exists_enorm_integral_inner_halfWavePropagator_le_tsum`, for `W₋(t) = W₊(-t)`,

`|∫ ⟪W₊(-t) f, G(t)⟫ dt| ≤ C (∑ⱼ 2^{jγ} ‖Pⱼ f‖₂) ‖G‖_{L^p_t L^{r'}_x}`

whenever `t ↦ W₊(t) G(t)` is integrable. This is `‖W₋(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖_{\dot B^γ_{2,1}}`
tested against `G`. -/
theorem exists_enorm_integral_inner_halfWavePropagator_neg_le_tsum (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (f : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)),
        AEStronglyMeasurable G → Integrable (fun t ↦ halfWavePropagator ℂ t (G t)) →
        ‖∫ t, ⟪halfWavePropagator ℂ (-t) f, G t⟫_ℂ‖ₑ ≤
          C * (∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C, hC⟩ := φ.exists_enorm_integral_inner_halfWavePropagator_le_tsum (r' := r') hq hpq hqr
  refine ⟨C, fun m hm f G hG hWG ↦ ?_⟩
  -- Reverse time: `t ↦ G(-t)` has the same mixed norm, since `t ↦ -t` preserves Lebesgue measure.
  have hneg := Measure.measurePreserving_neg (volume : Measure ℝ)
  have h := hC m hm f (fun t ↦ G (-t)) (hG.comp_quasiMeasurePreserving hneg.quasiMeasurePreserving)
    (by simpa only [neg_neg] using hWG.comp_neg)
  rw [← integral_neg_eq_self, hG.eLpNorm_eLpNorm_comp_neg] at h
  simpa only [neg_neg] using h

/-- Sum frequency-localized mixed-norm estimates with weights `2^{jσ}` for a strongly continuous
family `T(t)` of operators on `L²(E)` over the Littlewood–Paley blocks, for a wave-admissible pair
`(q, r)`. This is the common step of the estimates for `cos(tD)` and `D⁻¹ sin(tD)`. -/
private theorem exists_eLpNorm_eLpNorm_le_tsum_of_littlewoodPaley_le (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) (σ : ℝ)
    (T : ℝ → Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hT : ∀ x, Continuous fun t ↦ T t x)
    (hloc : ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (T t (Lp.fourierMultiplierCLM ℂ m f)) r volume) q volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * ‖f‖ₑ) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (T t f) r volume) q volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ ↦ by simp [eLpNorm_exponent_zero, Lp.aestronglyMeasurable]⟩
  obtain ⟨-, -, hr2⟩ := two_le_finrank_of_waveAdmissible hq hr0 hqr Module.finrank_pos
  obtain ⟨C, hC⟩ := hloc
  obtain ⟨K, hK⟩ := φ.exists_eLpNorm_eLpNorm_le_mul_tsum (F := ℂ) (β := ℝ) (ρ := volume) σ
    (q := q) (by exact_mod_cast one_le_two.trans hq.le) (one_le_two.trans hr2)
  refine ⟨K * C, fun m hm f ↦ (hK m hm T (fun x ↦ (hT x).aestronglyMeasurable) C
    (fun k x ↦ hC k (m k) (hm k) x) f).trans_eq ?_⟩
  push_cast
  ring

/-- **The Strichartz estimate for `cos(tD)` with data in `\dot B^γ_{2,1}`.** Let `E` be nontrivial
of dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, and let `Pⱼ` be the `L²`
Fourier multiplier with symbol `ψⱼ`. Let `(q, r)` be wave-admissible,
`2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞`, and let `γ = n / 2 - n / r - 1 / q`.
There is `C` such that for every `f ∈ L²(E)`,

`‖cos(tD) f‖_{L^q_t L^r_x} ≤ C ∑ⱼ 2^{jγ} ‖Pⱼ f‖₂`. -/
theorem exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t f) r volume) q volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ :=
  φ.exists_eLpNorm_eLpNorm_le_tsum_of_littlewoodPaley_le hq hqr _ _
    continuous_waveCosPropagator_apply <|
      φ.exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le hq
        (NNReal.HolderConjugate.conjExponent (one_lt_two.trans hq)).symm hqr

/-- **The Strichartz estimate for `D⁻¹ sin(tD)` with data in `\dot B^{γ - 1}_{2,1}`.** Under the
hypotheses of `ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum`, there is `C` such
that for every `g ∈ L²(E)`,

`‖D⁻¹ sin(tD) g‖_{L^q_t L^r_x} ≤ C ∑ⱼ 2^{j(γ - 1)} ‖Pⱼ g‖₂`. -/
theorem exists_eLpNorm_eLpNorm_waveSinPropagator_le_tsum (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ g : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveSinPropagator ℂ t g) r volume) q volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹ - 1)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) g‖ₑ :=
  φ.exists_eLpNorm_eLpNorm_le_tsum_of_littlewoodPaley_le hq hqr _ _
    continuous_waveSinPropagator_apply <|
      φ.exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le hq
        (NNReal.HolderConjugate.conjExponent (one_lt_two.trans hq)).symm hqr

/-- **The Strichartz estimate for the free wave equation with data in
`\dot B^γ_{2,1} × \dot B^{γ - 1}_{2,1}`.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum`, there is `C` such that for all
`f, g ∈ L²(E)`, the solution `u(t) = cos(tD) f + D⁻¹ sin(tD) g` of `∂ₜ²u = Δu` with `u(0) = f` and
`∂ₜu(0) = g` satisfies

`‖u‖_{L^q_t L^r_x} ≤ C (∑ⱼ 2^{jγ} ‖Pⱼ f‖₂ + ∑ⱼ 2^{j(γ - 1)} ‖Pⱼ g‖₂)`. -/
theorem exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f g : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t f + waveSinPropagator ℂ t g) r volume) q
            volume ≤
          C * (∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹ - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) g‖ₑ) := by
  obtain ⟨C₁, h₁⟩ := φ.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum hq hqr
  obtain ⟨C₂, h₂⟩ := φ.exists_eLpNorm_eLpNorm_waveSinPropagator_le_tsum hq hqr
  exact ⟨C₁ + C₂, fun m hm f g ↦
    eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le hq hqr (h₁ m hm f) (h₂ m hm g)⟩

/-- **The Strichartz estimate for strong solutions of the free wave equation.** Under the
hypotheses of `ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum`, there is `C` such
that for every interval `I` containing `0`, every strong solution `u` of `∂ₜ²u = Δu` on `I`, with
velocity `u'`, satisfies

`‖u‖_{L^q(I; L^r_x)} ≤ C (∑ⱼ 2^{jγ} ‖Pⱼ u(0)‖₂ + ∑ⱼ 2^{j(γ - 1)} ‖Pⱼ u'(0)‖₂)`. -/
theorem exists_eLpNorm_eLpNorm_le_tsum_of_isWaveSolutionOn (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (s : Set ℝ) [s.OrdConnected], 0 ∈ s →
      ∀ u u' u'' : ℝ → Lp ℂ 2 (volume : Measure E), IsWaveSolutionOn u u' u'' 0 s →
        eLpNorm (fun t ↦ eLpNorm (u t) r volume) q (volume.restrict s) ≤
          C * (∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) (u 0)‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹ - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) (u' 0)‖ₑ) := by
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum hq hqr
  exact ⟨C, fun m hm s _ h0 u u' u'' hu ↦
    (hu.eLpNorm_eLpNorm_restrict_le h0).trans (hC m hm _ _)⟩

end ContDiffBump

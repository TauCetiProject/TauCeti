/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.Strichartz
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional

/-!
# Strichartz estimates for the half-wave propagator with Besov data

On a nontrivial real inner product space `E` of dimension `n`, let `W₊(t) = exp(itD)`,
`D = √(-Δ)`, be the half-wave propagator (`TauCeti.halfWavePropagator`), and let `Pⱼ`, `j ∈ ℤ`, be
the `L²` Fourier multipliers with the homogeneous Littlewood–Paley cutoffs `ψⱼ`
(`ContDiffBump.littlewoodPaley`), supported where `‖ξ‖ ≈ 2^j`, as symbols. Let `(q, r)` be
wave-admissible, `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞`, and let
`γ = n / 2 - n / r - 1 / q` be its scaling-critical regularity. This file proves the
**Strichartz estimate on the whole time line**

`‖W₊(t) f‖_{L^q_t L^r_x} ≤ C ∑ⱼ 2^{jγ} ‖Pⱼ f‖₂`

in weak form, that is tested against `G ∈ L^{q'}_t L^{r'}_x`, and the same estimate for the
backward propagator `W₋(t) = W₊(-t)`. The right-hand side is the norm of `f` in the homogeneous
Besov space `\dot B^γ_{2,1}`, written through the blocks of `f`. Since the bound is an `ℓ¹` sum
over the blocks rather than a square function, the argument also covers the pairs with `r = ∞`.

## The argument

The frequency-localized dual estimate
(`ContDiffBump.exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le`) bounds the blocks
of `g = ∫ W₊(-t) G(t) dt`: since the blocks commute with the propagator,
`Pₖ g = ∫ W₊(-t) Pₖ G(t) dt`, and `‖Pₖ g‖₂ ≤ C 2^{kγ} ‖G‖_{L^{q'}_t L^{r'}_x}` uniformly in `k`.
That is, `g ∈ \dot B^{-γ}_{2,∞}`. The pairing `∫ ⟪W₊(t) f, G(t)⟫ dt = ⟪f, g⟫` of `f` with `g` is
then bounded by the duality of the dyadic `ℓ¹` and `ℓ^∞` norms
(`ContDiffBump.exists_enorm_inner_le_mul_tsum`).

## Main declarations

* `ContDiffBump.exists_enorm_integral_inner_halfWavePropagator_le_tsum`: the Strichartz estimate
  for `W₊(t)` with data in `\dot B^γ_{2,1}`, in weak form.
* `ContDiffBump.exists_enorm_integral_inner_halfWavePropagator_neg_le_tsum`: the same estimate for
  `W₋(t) = W₊(-t)`.

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
    have hint : Integrable
        (fun t ↦ halfWavePropagator ℂ (-t) (Lp.fourierMultiplierCLM ℂ (m k) (G t))) :=
      ((Lp.fourierMultiplierCLM ℂ (m k)).integrable_comp hWG).congr
        (Filter.Eventually.of_forall fun t ↦ fourierMultiplierCLM_halfWavePropagator_apply _ _ _)
    rw [← ContinuousLinearMap.integral_comp_comm _ hWG]
    simp only [fourierMultiplierCLM_halfWavePropagator_apply]
    refine (hC k (m k) (hm k) G hG hint).trans_eq ?_
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
  have hnorm : eLpNorm (fun t ↦ eLpNorm (G (-t)) r' volume) p volume =
      eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
    simpa only [Function.comp_def] using eLpNorm_comp_measurePreserving
      (g := fun t ↦ eLpNorm (G t) r' volume)
      (hG.aemeasurable_eLpNorm_Lp .rfl r').aestronglyMeasurable hneg
  rw [← integral_neg_eq_self, hnorm] at h
  simpa only [neg_neg] using h

end ContDiffBump

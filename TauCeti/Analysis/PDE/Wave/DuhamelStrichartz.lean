/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.HomogeneousStrichartz
public import TauCeti.Analysis.PDE.Wave.InhomogeneousStrichartz
public import TauCeti.Analysis.PDE.Wave.WeakSolution
import TauCeti.Analysis.PDE.Wave.TimeExponentTwo
import TauCeti.MeasureTheory.Function.Lp.MixedNorm

/-!
# Strichartz estimates for the forced wave equation on a time interval

On a real inner product space `E` of dimension `n`, let `D = √(-Δ)` and let `Pⱼ`, `j ∈ ℤ`, be the
`L²` Fourier multipliers with the homogeneous Littlewood–Paley cutoffs `ψⱼ`
(`ContDiffBump.littlewoodPaley`) as symbols. The Cauchy problem

`∂ₜ²u - Δu = G`, `u(0) = f`, `∂ₜu(0) = g`

is solved by Duhamel's formula (`TauCeti.waveDuhamelSolution`)

`u(t) = cos(tD) f + D⁻¹ sin(tD) g + ∫₀ᵗ D⁻¹ sin((t - s)D) G(s) ds`.

Let `(q, r)` be wave-admissible, `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 ≤ q < ∞`, and let
`(q₁, r₁)` be wave-admissible with `2 ≤ q₁ ≤ ∞`, with Hölder conjugates `p₁` and `r₁'`, where the
time exponent `2` is allowed, on either side or on both, in dimension `n ≥ 4`: the pairs `(2, r)`
with `r` at least the endpoint exponent `2 (n - 1) / (n - 3)`, `r = ∞` included. Put
`γ = n / 2 - n / r - 1 / q` and `γ₁ = n / 2 - n / r₁ - 1 / q₁`. This file proves the
**Strichartz estimate for the forced wave equation** on every time interval `[0, T]`, with data in
homogeneous Besov spaces and forcing in the dyadic `ℓ¹` class along the second pair:

`‖u‖_{L^q([0, T]; L^r_x)} ≤ C (∑ⱼ 2^{jγ} ‖Pⱼ f‖₂ + ∑ⱼ 2^{j(γ - 1)} ‖Pⱼ g‖₂`
`  + ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Pⱼ G‖_{L^{p₁}([0, T]; L^{r₁'}_x)})`

for every forcing `G` integrable on `[0, T]`, with `C` independent of `T`, `f`, `g` and `G`
(`ContDiffBump.exists_eLpNorm_eLpNorm_waveDuhamelSolution_le_tsum`). The same estimate holds at
the pairs `(∞, r)`, `2 ≤ r ≤ ∞`, with `γ = n / 2 - n / r`, when the forcing pair also has
`r₁ ≥ 2`, which is automatic in dimension `n ≥ 2`, and `q₁ = 2` only at the endpoint
`1 + (n - 1) / r₁ = (n - 1) / 2`
(`ContDiffBump.exists_eLpNorm_top_eLpNorm_waveDuhamelSolution_le_tsum`); at `(∞, ∞)` it bounds the
solution uniformly on `[0, T] × E`. Since a strong solution of the forced equation on `[0, T]` is
given by Duhamel's formula (`TauCeti.IsWaveSolutionOn.eq_waveDuhamelSolution`), both estimates
hold for strong solutions, with the data `u(0)` and `∂ₜu(0)`.

## The argument

For `0 ≤ t ≤ T` the Duhamel term of `u(t)` is the retarded integral
`∫_{s < t} D⁻¹ sin((t - s)D) G₀(s) ds` of the forcing `G₀` restricted to `[0, T]` and extended by
zero (`TauCeti.waveDuhamelSolution_eq_setIntegral_Iio`). By Minkowski's inequality the mixed norm
of `u` on `[0, T]` is at most the mixed norm on the whole line of the free solution
`cos(tD) f + D⁻¹ sin(tD) g` plus that of this retarded integral
(`TauCeti.eLpNorm_eLpNorm_waveDuhamelSolution_restrict_le`). The first is bounded by the
homogeneous Strichartz estimates of `TauCeti.Analysis.PDE.Wave.HomogeneousStrichartz`, and at the
pairs `(2, r)` by those of `TauCeti.Analysis.PDE.Wave.TimeExponentTwo`; the second is bounded by
the retarded estimates of `TauCeti.Analysis.PDE.Wave.InhomogeneousStrichartz`. Since the blocks are
linear, `Pⱼ G₀` is `Pⱼ G` restricted to `[0, T]`, so the forcing norms on the whole line are the
norms on `[0, T]`.

## Main declarations

* `TauCeti.eLpNorm_eLpNorm_waveDuhamelSolution_restrict_le`: the splitting of the mixed norm of the
  solution into its free part and its retarded part.
* `ContDiffBump.exists_eLpNorm_eLpNorm_waveDuhamelSolution_le_tsum` and
  `ContDiffBump.exists_eLpNorm_top_eLpNorm_waveDuhamelSolution_le_tsum`: the Strichartz estimates
  for the forced wave equation on `[0, T]`.
* `ContDiffBump.exists_eLpNorm_eLpNorm_le_tsum_of_isWaveSolutionOn_Icc` and
  `ContDiffBump.exists_eLpNorm_top_eLpNorm_le_tsum_of_isWaveSolutionOn_Icc`: the same estimates for
  strong solutions.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.6 and its proof.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980,
  Corollary 1.3.
-/

public section

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory TauCeti

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Let `1 ≤ q` and `1 ≤ r`. On a time interval `[0, T]`, the mixed norm `L^q([0, T]; L^r_x)` of
the solution `u` of the forced wave equation given by Duhamel's formula is at most the mixed norm
`L^q_t L^r_x` on the whole line of the free solution `cos(tD) f + D⁻¹ sin(tD) g`, plus that of the
retarded integral `∫_{s < t} D⁻¹ sin((t - s)D) G₀(s) ds` of the forcing `G₀` restricted to
`[0, T]` and extended by zero. -/
theorem eLpNorm_eLpNorm_waveDuhamelSolution_restrict_le {q r : ℝ≥0∞} (hq : 1 ≤ q) (hr : 1 ≤ r)
    (f g : Lp F 2 (volume : Measure E)) {G : ℝ → Lp F 2 (volume : Measure E)} {T : ℝ}
    (hG : AEStronglyMeasurable G (volume.restrict (Set.Icc 0 T))) :
    eLpNorm (fun t ↦ eLpNorm (waveDuhamelSolution F f g G t) r volume) q
        (volume.restrict (Set.Icc 0 T)) ≤
      eLpNorm (fun t ↦ eLpNorm (waveCosPropagator F t f + waveSinPropagator F t g) r volume) q
          volume +
        eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator F (t - s)
          ((Set.Icc 0 T).indicator G s) : Lp F 2 (volume : Measure E))) r volume) q volume := by
  have hrep : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
      eLpNorm (waveDuhamelSolution F f g G t) r volume =
        eLpNorm (waveCosPropagator F t f + waveSinPropagator F t g + ∫ s in Set.Iio t,
          waveSinPropagator F (t - s) ((Set.Icc 0 T).indicator G s)) r volume :=
    ae_restrict_of_forall_mem measurableSet_Icc fun t ht ↦ by
      rw [waveDuhamelSolution_eq_setIntegral_Iio f g G ht.1 ht.2]
  rw [eLpNorm_congr_ae hrep]
  have hGi : AEStronglyMeasurable ((Set.Icc 0 T).indicator G) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Icc).2 hG
  refine (eLpNorm_eLpNorm_add_le ((continuous_waveCosPropagator_apply f).add
    (continuous_waveSinPropagator_apply g)).aestronglyMeasurable
    (aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub hGi).restrict hq hr).trans ?_
  exact add_le_add (eLpNorm_mono_measure _ Measure.restrict_le_self)
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- Let `1 ≤ q` and `1 ≤ r`. If the free solutions satisfy
`‖cos(tD) f + D⁻¹ sin(tD) g‖_{L^q_t L^r_x} ≤ C₀ D(f, g)` and the retarded integrals of integrable
forcing terms satisfy `‖∫_{s < t} D⁻¹ sin((t - s)D) F(s) ds‖_{L^q_t L^r_x} ≤
C₁ ∑ⱼ wⱼ ‖Pⱼ F‖_{L^{p₁}_t L^{r₁'}_x}`, then on every time interval `[0, T]` the solution of the
forced wave equation satisfies
`‖u‖_{L^q([0, T]; L^r_x)} ≤ (C₀ + C₁) (D(f, g) + ∑ⱼ wⱼ ‖Pⱼ G‖_{L^{p₁}([0, T]; L^{r₁'}_x)})`. -/
private theorem eLpNorm_eLpNorm_waveDuhamelSolution_restrict_le_of_le {q r p₁ r₁' : ℝ≥0∞}
    (hq : 1 ≤ q) (hr : 1 ≤ r) {D : Lp ℂ 2 (volume : Measure E) → Lp ℂ 2 (volume : Measure E) → ℝ≥0∞}
    {w : ℤ → ℝ≥0∞} {m : ℤ → Lp ℂ ∞ (volume : Measure E)} {C₀ C₁ : ℝ≥0}
    (hfree : ∀ f g : Lp ℂ 2 (volume : Measure E),
      eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t f + waveSinPropagator ℂ t g) r volume) q
        volume ≤ C₀ * D f g)
    (hret : ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
      eLpNorm (fun t ↦ eLpNorm ((∫ s in Set.Iio t, waveSinPropagator ℂ (t - s) (F s) :
          Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
        C₁ * ∑' j : ℤ, w j *
          eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (F s)) r₁' volume) p₁ volume)
    (f g : Lp ℂ 2 (volume : Measure E)) {G : ℝ → Lp ℂ 2 (volume : Measure E)} {T : ℝ}
    (hG : IntegrableOn G (Set.Icc 0 T)) :
    eLpNorm (fun t ↦ eLpNorm (waveDuhamelSolution ℂ f g G t) r volume) q
        (volume.restrict (Set.Icc 0 T)) ≤
      ((C₀ + C₁ : ℝ≥0) : ℝ≥0∞) * (D f g + ∑' j : ℤ, w j * eLpNorm (fun s ↦
        eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (G s)) r₁' volume) p₁
          (volume.restrict (Set.Icc 0 T))) := by
  have hret' := hret _ (hG.integrable_indicator measurableSet_Icc)
  simp_rw [eLpNorm_eLpNorm_apply_indicator (map_zero _) measurableSet_Icc.nullMeasurableSet]
    at hret'
  grw [eLpNorm_eLpNorm_waveDuhamelSolution_restrict_le hq hr f g hG.aestronglyMeasurable,
    hfree f g, hret', ENNReal.coe_add, add_mul]
  gcongr
  · exact le_self_add
  · exact le_add_self

/-- A strong solution of `∂ₜ²u - Δu = G` on `[0, T]` with `G` integrable on `[0, T]` agrees there
with Duhamel's formula for its data, so the two have the same `L^r` norms at almost every time of
`[0, T]`. -/
private theorem IsWaveSolutionOn.ae_restrict_eLpNorm_eq_waveDuhamelSolution
    {u u' u'' G : ℝ → Lp F 2 (volume : Measure E)} {T : ℝ}
    (hu : IsWaveSolutionOn u u' u'' G (Set.Icc 0 T)) (hG : IntegrableOn G (Set.Icc 0 T))
    {r : ℝ≥0∞} :
    ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
      eLpNorm (u t) r volume = eLpNorm (waveDuhamelSolution F (u 0) (u' 0) G t) r volume :=
  ae_restrict_of_forall_mem measurableSet_Icc fun t ht ↦ by
    rw [hu.eq_waveDuhamelSolution ⟨le_rfl, ht.1.trans ht.2⟩ ht (hG.mono_set (by
      rw [Set.uIcc_of_le ht.1]
      exact Set.Icc_subset_Icc le_rfl ht.2)).intervalIntegrable]

end TauCeti

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (φ : ContDiffBump (0 : E))

/-! ### Finite time exponents -/

section TimeExponentFinite

variable {q : ℝ≥0} {r : ℝ≥0∞}

/-- **The Strichartz estimate for the forced wave equation on `[0, T]`.** Let `E` be nontrivial
of dimension `n`, let `Pⱼ` be the `L²` Fourier multiplier with the Littlewood–Paley cutoff `ψⱼ`
built from `φ` as symbol, let `(q, r)` be wave-admissible, `2 / q + (n - 1) / r ≤ (n - 1) / 2`,
with `2 ≤ q < ∞`, and let `(q₁, r₁)` be wave-admissible with `2 ≤ q₁ ≤ ∞`, with Hölder conjugates
`p₁` and `r₁'`, where `q = 2` and `q₁ = 2` are allowed only in dimension `n ≥ 4`. Put
`γ = n / 2 - n / r - 1 / q` and `γ₁ = n / 2 - n / r₁ - 1 / q₁`. There is `C` such that for every
`T`, all data `f, g ∈ L²(E)` and every forcing `G : ℝ → L²(E)` integrable on `[0, T]`, the
solution `u(t) = cos(tD) f + D⁻¹ sin(tD) g + ∫₀ᵗ D⁻¹ sin((t - s)D) G(s) ds` of `∂ₜ²u - Δu = G`
with `u(0) = f` and `∂ₜu(0) = g` satisfies

`‖u‖_{L^q([0, T]; L^r_x)} ≤ C (∑ⱼ 2^{jγ} ‖Pⱼ f‖₂ + ∑ⱼ 2^{j(γ - 1)} ‖Pⱼ g‖₂`
`  + ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Pⱼ G‖_{L^{p₁}([0, T]; L^{r₁'}_x)})`. -/
theorem exists_eLpNorm_eLpNorm_waveDuhamelSolution_le_tsum (hq : 2 ≤ q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq2 : q = 2 → 3 < Module.finrank ℝ E)
    {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁] [r₁'.HolderConjugate r₁] (hq₁ : 2 ≤ q₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁2 : q₁ = 2 → 3 < Module.finrank ℝ E) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (f g : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)) (T : ℝ),
        IntegrableOn G (Set.Icc 0 T) →
        eLpNorm (fun t ↦ eLpNorm (waveDuhamelSolution ℂ f g G t) r volume) q
            (volume.restrict (Set.Icc 0 T)) ≤
          C * (∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹ - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) g‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹) + ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
                eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (G s)) r₁' volume) p₁
                  (volume.restrict (Set.Icc 0 T))) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ _ _ _ _ ↦ by simp [eLpNorm_exponent_zero, Lp.aestronglyMeasurable]⟩
  -- The retarded estimate is stated with the extended real time exponent `(q : ℝ≥0∞)`.
  have hqinv : (((q : ℝ≥0∞))⁻¹).toReal = (q : ℝ)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal]
  have hq' : (2 : ℝ≥0∞) ≤ q := by exact_mod_cast hq
  have hqr' : 2 * (((q : ℝ≥0∞))⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2 := by
    rwa [hqinv, ← div_eq_mul_inv]
  obtain ⟨-, hr2⟩ := two_le_finrank_of_waveAdmissible_of_two_le hq' ENNReal.coe_ne_top hr0 hqr'
    Module.finrank_pos
  obtain ⟨C₀, h₀⟩ :=
    φ.exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum_of_two_le hq hqr hq2
  obtain ⟨C₁, h₁⟩ := φ.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum
    (p₁ := p₁) (r₁' := r₁') hq' ENNReal.coe_ne_top hqr' (fun h ↦ hq2 (by exact_mod_cast h)) hq₁
    hqr₁ hq₁2
  simp only [hqinv] at h₁
  exact ⟨C₀ + C₁, fun m hm f g G T hG ↦
    eLpNorm_eLpNorm_waveDuhamelSolution_restrict_le_of_le (by exact_mod_cast one_le_two.trans hq)
      (one_le_two.trans hr2) (h₀ m hm) (h₁ m hm) f g hG⟩

/-- **The Strichartz estimate for strong solutions of the forced wave equation on `[0, T]`.**
Under the hypotheses of `ContDiffBump.exists_eLpNorm_eLpNorm_waveDuhamelSolution_le_tsum`, there is
`C` such that for every `T`, every strong solution `u` of `∂ₜ²u - Δu = G` on `[0, T]`, with
velocity `u'` and forcing `G` integrable on `[0, T]`, satisfies

`‖u‖_{L^q([0, T]; L^r_x)} ≤ C (∑ⱼ 2^{jγ} ‖Pⱼ u(0)‖₂ + ∑ⱼ 2^{j(γ - 1)} ‖Pⱼ u'(0)‖₂`
`  + ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Pⱼ G‖_{L^{p₁}([0, T]; L^{r₁'}_x)})`. -/
theorem exists_eLpNorm_eLpNorm_le_tsum_of_isWaveSolutionOn_Icc (hq : 2 ≤ q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq2 : q = 2 → 3 < Module.finrank ℝ E)
    {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁] [r₁'.HolderConjugate r₁] (hq₁ : 2 ≤ q₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁2 : q₁ = 2 → 3 < Module.finrank ℝ E) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (T : ℝ) (u u' u'' G : ℝ → Lp ℂ 2 (volume : Measure E)),
        IsWaveSolutionOn u u' u'' G (Set.Icc 0 T) → IntegrableOn G (Set.Icc 0 T) →
        eLpNorm (fun t ↦ eLpNorm (u t) r volume) q (volume.restrict (Set.Icc 0 T)) ≤
          C * (∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) (u 0)‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹ - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) (u' 0)‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹) + ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
                eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (G s)) r₁' volume) p₁
                  (volume.restrict (Set.Icc 0 T))) := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_eLpNorm_waveDuhamelSolution_le_tsum (p₁ := p₁) (r₁' := r₁')
    hq hqr hq2 hq₁ hqr₁ hq₁2
  refine ⟨C, fun m hm T u u' u'' G hu hG ↦ ?_⟩
  rw [eLpNorm_congr_ae (hu.ae_restrict_eLpNorm_eq_waveDuhamelSolution hG)]
  exact hC m hm _ _ G T hG

end TimeExponentFinite

/-! ### The pairs `(∞, r)` -/

section TimeExponentTop

variable {r : ℝ≥0∞}

/-- **The Strichartz estimate for the forced wave equation on `[0, T]` at the pairs `(∞, r)`.**
Let `E` be nontrivial of dimension `n`, let `Pⱼ` be the `L²` Fourier multiplier with the
Littlewood–Paley cutoff `ψⱼ` built from `φ` as symbol, let `2 ≤ r ≤ ∞` and let `γ = n / 2 - n / r`.
Let `(q₁, r₁)` be wave-admissible with `2 ≤ q₁ ≤ ∞` and `2 ≤ r₁`, with Hölder conjugates `p₁` and
`r₁'`, where `q₁ = 2` only if `1 + (n - 1) / r₁ = (n - 1) / 2` in dimension `n ≥ 4`, and put
`γ₁ = n / 2 - n / r₁ - 1 / q₁`. There is `C` such that for every `T`, all data `f, g ∈ L²(E)` and
every forcing `G : ℝ → L²(E)` integrable on `[0, T]`, the solution
`u(t) = cos(tD) f + D⁻¹ sin(tD) g + ∫₀ᵗ D⁻¹ sin((t - s)D) G(s) ds` of `∂ₜ²u - Δu = G` with
`u(0) = f` and `∂ₜu(0) = g` satisfies

`‖u‖_{L^∞([0, T]; L^r_x)} ≤ C (∑ⱼ 2^{jγ} ‖Pⱼ f‖₂ + ∑ⱼ 2^{j(γ - 1)} ‖Pⱼ g‖₂`
`  + ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Pⱼ G‖_{L^{p₁}([0, T]; L^{r₁'}_x)})`.

In dimension `n ≥ 2` the bound `2 ≤ r₁` follows from wave-admissibility
(`TauCeti.two_le_of_waveAdmissible`). -/
theorem exists_eLpNorm_top_eLpNorm_waveDuhamelSolution_le_tsum (hr : 2 ≤ r)
    {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁] [r₁'.HolderConjugate r₁] (hq₁ : 2 ≤ q₁)
    (hr₁ : 2 ≤ r₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁2 : q₁ = 2 → 3 < Module.finrank ℝ E ∧
      1 + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (f g : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)) (T : ℝ),
        IntegrableOn G (Set.Icc 0 T) →
        eLpNorm (fun t ↦ eLpNorm (waveDuhamelSolution ℂ f g G t) r volume) ∞
            (volume.restrict (Set.Icc 0 T)) ≤
          C * (∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal)) * ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - 1)) * ‖Lp.fourierMultiplierCLM ℂ (m j) g‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
                eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (G s)) r₁' volume) p₁
                  (volume.restrict (Set.Icc 0 T))) := by
  obtain ⟨C₀, h₀⟩ := φ.exists_eLpNorm_top_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum hr
  obtain ⟨C₁, h₁⟩ := φ.exists_eLpNorm_top_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum
    (p₁ := p₁) (r₁' := r₁') hr hq₁ hr₁ hqr₁ hq₁2
  exact ⟨C₀ + C₁, fun m hm f g G T hG ↦
    eLpNorm_eLpNorm_waveDuhamelSolution_restrict_le_of_le le_top (one_le_two.trans hr) (h₀ m hm)
      (h₁ m hm) f g hG⟩

/-- **The Strichartz estimate at the pairs `(∞, r)` for strong solutions of the forced wave
equation on `[0, T]`.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_top_eLpNorm_waveDuhamelSolution_le_tsum`, there is `C` such that for
every `T`, every strong solution `u` of `∂ₜ²u - Δu = G` on `[0, T]`, with velocity `u'` and forcing
`G` integrable on `[0, T]`, satisfies

`‖u‖_{L^∞([0, T]; L^r_x)} ≤ C (∑ⱼ 2^{jγ} ‖Pⱼ u(0)‖₂ + ∑ⱼ 2^{j(γ - 1)} ‖Pⱼ u'(0)‖₂`
`  + ∑ⱼ 2^{j(γ + γ₁ - 1)} ‖Pⱼ G‖_{L^{p₁}([0, T]; L^{r₁'}_x)})`. -/
theorem exists_eLpNorm_top_eLpNorm_le_tsum_of_isWaveSolutionOn_Icc (hr : 2 ≤ r)
    {p₁ q₁ r₁ r₁' : ℝ≥0∞} [p₁.HolderConjugate q₁] [r₁'.HolderConjugate r₁] (hq₁ : 2 ≤ q₁)
    (hr₁ : 2 ≤ r₁)
    (hqr₁ : 2 * (q₁⁻¹).toReal + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hq₁2 : q₁ = 2 → 3 < Module.finrank ℝ E ∧
      1 + ((Module.finrank ℝ E : ℝ) - 1) * (r₁⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (T : ℝ) (u u' u'' G : ℝ → Lp ℂ 2 (volume : Measure E)),
        IsWaveSolutionOn u u' u'' G (Set.Icc 0 T) → IntegrableOn G (Set.Icc 0 T) →
        eLpNorm (fun t ↦ eLpNorm (u t) r volume) ∞ (volume.restrict (Set.Icc 0 T)) ≤
          C * (∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal)) * ‖Lp.fourierMultiplierCLM ℂ (m j) (u 0)‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) (u' 0)‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal) + ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r₁⁻¹).toReal - (q₁⁻¹).toReal) - 1)) *
                eLpNorm (fun s ↦ eLpNorm (Lp.fourierMultiplierCLM ℂ (m j) (G s)) r₁' volume) p₁
                  (volume.restrict (Set.Icc 0 T))) := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_top_eLpNorm_waveDuhamelSolution_le_tsum (p₁ := p₁)
    (r₁' := r₁') hr hq₁ hr₁ hqr₁ hq₁2
  refine ⟨C, fun m hm T u u' u'' G hu hG ↦ ?_⟩
  rw [eLpNorm_congr_ae (hu.ae_restrict_eLpNorm_eq_waveDuhamelSolution hG)]
  exact hC m hm _ _ G T hG

end TimeExponentTop

end ContDiffBump

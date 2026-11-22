/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Strichartz.TTStar
public import TauCeti.Analysis.PDE.Wave.Dispersive
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.Star
import TauCeti.MeasureTheory.Integral.RieszThorin

/-!
# Frequency-localized Strichartz estimates for the wave equation

Let `E` have dimension `n`, let `ψ` be smooth, compactly supported and vanish near the origin, and
for `j ∈ ℤ` let `Pⱼ` be the `L²` Fourier multiplier with the dilated symbol `ψ (2^{-j} ·)`, which
localizes to frequencies `‖ξ‖ ≈ 2^j`; the Littlewood–Paley blocks are the case where `ψ` is the
cutoff `ψ₀` of `ContDiffBump.littlewoodPaley`. This file proves the Strichartz estimates for the
frequency-localized half-wave propagators `W₊(t) Pⱼ`, `W₊(t) = exp(itD)`, `D = √(-Δ)`, with
constants independent of `j`.

A pair `(q, r)` is *wave-admissible* when `2 < q < ∞` and

`2 / q + (n - 1) / r ≤ (n - 1) / 2`,

the non-endpoint, finite-`q` part of the region of Tao, Theorem 2.6 (the excluded pair
`(2, ∞)` in dimension `3` has `q = 2`). In positive dimension admissibility forces `n ≥ 2`
and `r > 2`; in dimension `0` the cutoffs, and with them the estimates, vanish. The regularity
exponent is the scaling-critical `γ = n / 2 - n / r - 1 / q`; the power of `2^j` is the one
dictated by scaling, since `x ↦ 2^j x` maps `ψ` to its dilate. The main estimate is

`‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{jγ} ‖f‖₂`,

stated, like the Schrödinger estimates of `TauCeti.Analysis.PDE.Schrodinger.Strichartz`, in weak
form against `G ∈ L^{q'}_t L^{r'}_x`, together with its dual form, the bilinear bound for the
Duhamel pairings and its retarded restriction to `s < t`. These are the frequency-localized
estimates from which the wave Strichartz estimates with data in the homogeneous Sobolev space of
order `γ` are assembled by Littlewood–Paley summation.

At `q = ∞` every `r ≥ 2` is admissible, and for the Littlewood–Paley blocks the homogeneous and
dual estimates hold with `γ = n / 2 - n / r` and `L¹` in time on the dual side. The endpoint
`q = 2` is not covered.

## The argument

The time pairings of `U(t) = W₊(t) Pⱼ` are `U(s) U(t)* = W₊(s - t) Pⱼ Pⱼ*`, and `Pⱼ Pⱼ*` is the
multiplier with the dilated symbol `|ψ|² (2^{-j} ·)`, again a smooth cutoff vanishing near the
origin. The dispersive estimate for dilated cutoffs
(`TauCeti.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_le`) bounds it from `L¹` to `L^∞`
by `C 2^{jn} (1 + 2^j |τ|)^(-(n - 1)/2)`, and it is bounded on `L²` uniformly in `j`. The
Riesz–Thorin theorem interpolates the two to an `L^{r'} → L^r` bound with the factor
`(1 + 2^j |τ|)^(-(n - 1)(1/2 - 1/r))`, and admissibility makes this at most `(2^j |τ|)^(-2/q)`.
So the pairings decay like `A 2^{2jγ} |τ|^(-2/q)`, which is the hypothesis of the abstract `TT*`
estimates of `TauCeti.Analysis.PDE.Strichartz.TTStar`; their constant is linear in `A` for the
bilinear bound and in `A ^ (1/2)` for the others, which produces the factors `2^{2jγ}` and `2^{jγ}`.
At `q = ∞` only the pairings at equal times enter, where the dispersive factor is `1`, and the
single-time `TT*` argument applies.

## Main declarations

* `TauCeti.exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_fourierMultiplierCLM_le`:
  the bilinear estimate for the frequency-localized Duhamel pairings.
* `exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_fourierMultiplierCLM_le`:
  the retarded estimate, in weak form.
* `TauCeti.exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le`: the dual
  estimate `‖∫ Pⱼ* W₊(-s) F(s) ds‖₂ ≤ C 2^{jγ} ‖F‖_{L^{q'}_t L^{r'}_x}`.
* `TauCeti.exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le`: the
  homogeneous estimate, in weak form.
* `ContDiffBump.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le_of_memLp`:
  the dispersive estimate for the Littlewood–Paley blocks from `Lᵖ` to `L^q`.
* `ContDiffBump.exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_littlewoodPaley_le`,
  `exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_littlewoodPaley_le`,
  `ContDiffBump.exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le` and
  `ContDiffBump.exists_enorm_integral_inner_halfWavePropagator_littlewoodPaley_le`: the four
  estimates for the Littlewood–Paley blocks along wave-admissible pairs. The symbols `ψⱼ`
  are real, so `Pⱼ* = Pⱼ`.
* `ContDiffBump.exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le_eLpNorm_one` and
  `ContDiffBump.exists_enorm_integral_inner_halfWavePropagator_littlewoodPaley_le_eLpNorm_one`:
  the dual and homogeneous estimates for the Littlewood–Paley blocks at the pairs `(∞, r)`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Sections 2.2–2.3 and Theorem 2.6.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal FourierTransform InnerProductSpace InnerProduct ContDiff

namespace TauCeti

section WaveAdmissible

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {q : ℝ≥0} {r : ℝ≥0∞}

/-- In positive dimension `n`, a wave-admissible pair `2 / q + (n - 1) / r ≤ (n - 1) / 2` with
`2 < q` and `r ≠ 0` has `n ≥ 2` and `r > 2`. -/
theorem two_le_finrank_of_waveAdmissible (hq : 2 < q) (hr0 : r ≠ 0)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) (hE : 0 < Module.finrank ℝ E) :
    2 ≤ Module.finrank ℝ E ∧ (r⁻¹).toReal < 2⁻¹ ∧ 2 ≤ r := by
  have hq0 : (0 : ℝ) < 2 / q := div_pos two_pos (by exact_mod_cast zero_lt_two.trans hq)
  have hn : 2 ≤ Module.finrank ℝ E := by
    by_contra h
    have h1 : Module.finrank ℝ E = 1 := by omega
    rw [h1, Nat.cast_one, sub_self, zero_mul, add_zero, zero_div] at hqr
    linarith
  have hn' : (1 : ℝ) ≤ Module.finrank ℝ E - 1 := by
    have : (2 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hn
    linarith
  have hρ : (r⁻¹).toReal < 2⁻¹ := by
    have h : 0 < ((Module.finrank ℝ E : ℝ) - 1) * (2⁻¹ - (r⁻¹).toReal) := by linarith
    linarith [pos_of_mul_pos_right h (by linarith)]
  exact ⟨hn, hρ, ENNReal.two_le_of_toReal_inv_le hr0 hρ.le⟩

end WaveAdmissible

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Time pairings -/

/-- The decay of the Riesz–Thorin bound: if `(q, r)` is wave-admissible, `a = 1 / r` and
`c = 2^j`, then

`(C₁ c^n (1 + c |τ|)^(-(n - 1)/2))^(1 - 2a) B₁^(2a) ≤ C₁^(1 - 2a) B₁^(2a) c^{2γ} |τ|^(-2/q)`

with `γ = n / 2 - n a - 1 / q`. -/
private theorem rpow_mul_rpow_le {n : ℕ} {a c C₁ B₁ τ : ℝ} {q : ℝ≥0} (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((n : ℝ) - 1) * a ≤ ((n : ℝ) - 1) / 2) (hc : 0 < c)
    (hC₁ : 0 ≤ C₁) (hB₁ : 0 ≤ B₁) (hτ : 0 < |τ|) :
    (C₁ * c ^ n * (1 + c * |τ|) ^ (-((n : ℝ) - 1) / 2)) ^ (1 - 2 * a) * B₁ ^ (2 * a) ≤
      C₁ ^ (1 - 2 * a) * B₁ ^ (2 * a) * c ^ (2 * ((n : ℝ) / 2 - n * a - 1 / q)) *
        |τ| ^ (-(2 / q : ℝ)) := by
  have hq0 : (0 : ℝ) < 2 / q := div_pos two_pos (by exact_mod_cast zero_lt_two.trans hq)
  have hx : 0 < c * |τ| := mul_pos hc hτ
  -- Admissibility: the interpolated decay exponent is at least `2 / q`.
  have hdecay : ((1 + c * |τ|) ^ (-((n : ℝ) - 1) / 2)) ^ (1 - 2 * a) ≤
      (c * |τ|) ^ (-(2 / q : ℝ)) := by
    rw [← Real.rpow_mul (by positivity)]
    calc _ ≤ (1 + c * |τ|) ^ (-(2 / q : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos hx (by linarith) (by linarith)
  have hpow : (c ^ n) ^ (1 - 2 * a) * (c * |τ|) ^ (-(2 / q : ℝ)) =
      c ^ (2 * ((n : ℝ) / 2 - n * a - 1 / q)) * |τ| ^ (-(2 / q : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le, Real.mul_rpow hc.le hτ.le, ← mul_assoc,
      ← Real.rpow_add hc]
    congr 2
    ring
  calc _ = C₁ ^ (1 - 2 * a) * B₁ ^ (2 * a) * ((c ^ n) ^ (1 - 2 * a) *
        ((1 + c * |τ|) ^ (-((n : ℝ) - 1) / 2)) ^ (1 - 2 * a)) := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hC₁ (by positivity)]
        ring
    _ ≤ C₁ ^ (1 - 2 * a) * B₁ ^ (2 * a) * ((c ^ n) ^ (1 - 2 * a) *
        (c * |τ|) ^ (-(2 / q : ℝ))) := by
        gcongr
    _ = _ := by rw [hpow]; ring

/-- The square root of `A c^{2s}` is `√A c^s`. -/
private theorem ofReal_rpow_mul_rpow_two_mul {A c s : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    ENNReal.ofReal ((A * c ^ (2 * s)) ^ (2⁻¹ : ℝ)) =
      ENNReal.ofReal √A * ENNReal.ofReal (c ^ s) := by
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_rpow hA (by positivity),
    ← Real.rpow_mul hc.le, Real.sqrt_eq_rpow, one_div, mul_comm 2 s,
    mul_inv_cancel_right₀ two_ne_zero]

variable {ψ : E → ℂ} {q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- **Interpolated dispersive decay.** Let `(q, r)` be wave-admissible in dimension `n`, and let
`T` be bounded on `L²` with `‖T‖ ≤ B₁` and `‖T f‖_∞ ≤ C₁ c^n (1 + c |τ|)^(-(n - 1)/2) ‖f‖₁`. Then

`‖T g‖_r ≤ C₁^(1 - 2/r) B₁^(2/r) c^{2γ} |τ|^(-2/q) ‖g‖_{r'}`,

with `γ = n / 2 - n / r - 1 / q`: the Riesz–Thorin theorem followed by admissibility. -/
private theorem eLpNorm_apply_le_of_eLpNorm_top_le (hq : 2 < q) (hr : 2 ≤ r)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) {C₁ B₁ c τ : ℝ}
    (hC₁ : 0 < C₁) (hB₁ : 0 < B₁) (hc : 0 < c) (hτ : τ ≠ 0)
    (h₀ : ∀ f : Lp ℂ 2 (volume : Measure E), Integrable f →
      eLpNorm (T f) ∞ volume ≤ ENNReal.ofReal (C₁ * c ^ Module.finrank ℝ E *
        (1 + c * |τ|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)) * eLpNorm f 1 volume)
    (h₁ : ‖T‖ ≤ B₁) (g : Lp ℂ 2 (volume : Measure E)) :
    eLpNorm (T g) r volume ≤
      ENNReal.ofReal (C₁ ^ (1 - 2 * (r⁻¹).toReal) * B₁ ^ (2 * (r⁻¹).toReal) *
        c ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) *
        ‖τ‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' volume := by
  have hτ' : 0 < |τ| := abs_pos.2 hτ
  by_cases hg : MemLp g r' volume
  · refine (T.eLpNorm_apply_le_rpow_mul_rpow_mul_eLpNorm h₀
      (h₁.trans_eq (Real.coe_toNNReal _ hB₁.le).symm) hr g hg).trans ?_
    gcongr ?_ * _
    rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_pos hτ',
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ hB₁.le]
    exact rpow_mul_rpow_le hq hqr hc hC₁.le hB₁.le hτ'
  · -- Outside `L^{r'}` the right-hand side is infinite.
    have hpos : ENNReal.ofReal (C₁ ^ (1 - 2 * (r⁻¹).toReal) * B₁ ^ (2 * (r⁻¹).toReal) *
        c ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) *
        ‖τ‖ₑ ^ (-(2 / q : ℝ)) ≠ 0 :=
      mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne'
        (ENNReal.rpow_pos (eNorm_pos.2 hτ) eNorm_ne_top).ne'
    rw [top_unique (not_lt.1 (memLp_iff.not.1 hg)), ENNReal.mul_top hpos]
    exact le_top

/-- The time pairings `U(s) U(t)*` of the frequency-localized half-wave propagators
`U(t) = W₊(t) Pⱼ` decay from `L^{r'}` to `L^r` like `A 2^{2jγ} |s - t| ^ (-2 / q)` along a
wave-admissible pair, with `A` independent of `j`. -/
private theorem exists_eLpNorm_halfWavePropagator_comp_fourierMultiplierCLM_apply_adjoint_le
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ) (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ A : ℝ, 0 < A ∧ ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ ψ (((2 : ℝ) ^ j)⁻¹ • ξ)) → ∀ s t : ℝ, s ≠ t →
      ∀ g : Lp ℂ 2 (volume : Measure E),
        eLpNorm ((halfWavePropagator ℂ s ∘L Lp.fourierMultiplierCLM ℂ m)
          (((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) g)) r volume ≤
        ENNReal.ofReal (A * ((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) *
          ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' volume := by
  -- The symbol of `Pⱼ Pⱼ*` is the dilate of the cutoff `|ψ|² = ψ * star ψ`.
  set ψ' : E → ℂ := fun ξ ↦ ψ ξ * star (ψ ξ)
  have hψ' : ContDiff ℝ ∞ ψ' := hψ.mul (Complex.conjCLE.contDiff.comp hψ)
  have hψ'0 : (0 : E) ∉ tsupport ψ' := fun h ↦ hψ0 (tsupport_mul_subset_left h)
  obtain ⟨C, hC0, hC⟩ :=
    exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_le hψ' hψc.mul_right hψ'0 (F := ℂ)
  obtain ⟨B, hB⟩ := hψ'.continuous.bounded_above_of_compact_support hψc.mul_right
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨(C + 1) ^ (1 - 2 * (r⁻¹).toReal) * (B + 1) ^ (2 * (r⁻¹).toReal), by positivity,
    fun j m hm s t hst g ↦ ?_⟩
  set m' : Lp ℂ ∞ (volume : Measure E) := m • star m
  have hm' : m' =ᵐ[volume] fun ξ ↦ ψ' (((2 : ℝ) ^ j)⁻¹ • ξ) := by
    filter_upwards [Lp.coeFn_lpSMul (r := ∞) m (star m), Lp.coeFn_star m, hm] with ξ h₁ h₂ h₃
    rw [h₁, Pi.smul_apply', h₂, Pi.star_apply, h₃, smul_eq_mul]
  rw [halfWavePropagator_comp_fourierMultiplierCLM_apply_adjoint,
    Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply, ← ContinuousLinearMap.comp_apply]
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hE | hE
  · -- In dimension `0` the symbol of `Pⱼ Pⱼ*` vanishes, and with it the time pairing.
    have : Subsingleton E := Module.finrank_zero_iff.1 hE
    have h0 : Lp.fourierMultiplierCLM ℂ m' = 0 := by
      rw [Lp.fourierMultiplierCLM_of_ae_eq_const (F := ℂ) (c := 0)]
      · exact zero_smul ℂ (ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)))
      filter_upwards [hm'] with ξ h
      rw [h, Subsingleton.elim (((2 : ℝ) ^ j)⁻¹ • ξ) 0, image_eq_zero_of_notMem_tsupport hψ'0]
    rw [h0, ContinuousLinearMap.comp_zero, zero_apply,
      eLpNorm_congr_ae (Lp.coeFn_zero _ _ _), eLpNorm_zero]
    exact zero_le
  refine eLpNorm_apply_le_of_eLpNorm_top_le hq
    (two_le_finrank_of_waveAdmissible hq (ENNReal.HolderConjugate.ne_zero r r') hqr hE).2.2 hqr _
    (by positivity) (by positivity) (zpow_pos two_pos j) (sub_ne_zero.2 hst) (fun f hf ↦ ?_) ?_ g
  · -- The `L¹ → L^∞` bound, from the dispersive estimate for dilated cutoffs.
    refine (hC j m' hm' (s - t) f hf).trans ?_
    gcongr ?_ * _
    exact ENNReal.ofReal_le_ofReal (by gcongr; linarith)
  · -- The `L²` bound, uniform in `j`.
    calc _ ≤ ‖halfWavePropagator (E := E) ℂ (s - t)‖ * ‖Lp.fourierMultiplierCLM ℂ m'‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * B := by
          gcongr
          · exact norm_phasePropagator_le _ _
          · exact (Lp.norm_fourierMultiplierCLM_le m').trans
              (Lp.norm_le_of_ae_bound_top hB0 (hm'.mono fun ξ h ↦ h ▸ hB _))
      _ ≤ B + 1 := by linarith

/-! ### The Strichartz estimates -/

/-- **The bilinear frequency-localized Strichartz estimate for the wave equation.** Let `E` have
dimension `n`, let `ψ` be smooth, compactly supported and vanish near the origin, and let
`(q, r)` be wave-admissible: `2 < q < ∞` and `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `p`
and `r'` the Hölder conjugates of `q` and `r`. Put `γ = n / 2 - n / r - 1 / q`. There is `C` such
that for every `j ∈ ℤ`, every multiplier `Pⱼ` with symbol `ψ (2^{-j} ·)` and all almost
everywhere strongly measurable `F, G : ℝ → L²(E)`,

`∫∫ |⟪W₊(t - s) Pⱼ Pⱼ* F(s), G(t)⟫| ds dt ≤ C 2^{2jγ} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

Since the integrand is the absolute value of the Duhamel pairing, the bound also controls the
integral over any part of the `(s, t)` plane, such as the retarded region `s < t`
(`exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_fourierMultiplierCLM_le`).
-/
theorem exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_fourierMultiplierCLM_le
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ) {p : ℝ≥0}
    (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ ψ (((2 : ℝ) ^ j)⁻¹ • ξ)) →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F → AEStronglyMeasurable G →
        ∫⁻ t, ∫⁻ s, ‖⟪halfWavePropagator ℂ (t - s)
          (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ (star m) (F s))), G t⟫_ℂ‖ₑ ≤
        C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) *
          eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨A, hA0, hA⟩ :=
    exists_eLpNorm_halfWavePropagator_comp_fourierMultiplierCLM_apply_adjoint_le (r' := r') hψ hψc
      hψ0 hq hqr
  obtain ⟨C, hC⟩ := exists_lintegral_lintegral_enorm_inner_adjoint_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq
    hpq
  refine ⟨C * A.toNNReal, fun j m hm F G hF hG ↦ ?_⟩
  -- The Duhamel pairing `⟪W₊(t - s) Pⱼ Pⱼ* F(s), G(t)⟫` is the time pairing
  -- `⟪U(t)* G(t), U(s)* F(s)⟫` of `U(t) = W₊(t) Pⱼ`, up to complex conjugation.
  have hpair (s t : ℝ) : ‖⟪halfWavePropagator ℂ (t - s)
      (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ (star m) (F s))), G t⟫_ℂ‖ₑ =
      ‖⟪((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) (G t),
        ((halfWavePropagator ℂ s ∘L Lp.fourierMultiplierCLM ℂ m)†) (F s)⟫_ℂ‖ₑ := by
    rw [ContinuousLinearMap.adjoint_inner_left,
      halfWavePropagator_comp_fourierMultiplierCLM_apply_adjoint, ← ofReal_norm, ← ofReal_norm,
      norm_inner_symm]
  simp_rw [hpair]
  calc _ ≤ _ := hC (fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m) _
        (hA j m hm) G F hG hF
    _ = _ := by
        rw [ENNReal.ofReal_mul hA0.le, ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal]
        ring

/-- **The retarded frequency-localized Strichartz estimate for the wave equation**, in weak form.
Let `E` have dimension `n`, let `ψ` be smooth, compactly supported and vanish near the origin, and
let `(q, r)` be wave-admissible: `2 < q < ∞` and `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with
`p` and `r'` the Hölder conjugates of `q` and `r`. Put `γ = n / 2 - n / r - 1 / q`. There is `C`
such that for every `j ∈ ℤ`, every multiplier `Pⱼ` with symbol `ψ (2^{-j} ·)` and all almost
everywhere strongly measurable `F, G : ℝ → L²(E)`,

`|∫ ∫_{s < t} ⟪W₊(t - s) Pⱼ Pⱼ* F(s), G(t)⟫ ds dt| ≤
  C 2^{2jγ} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

This is the Duhamel estimate
`‖∫_{s < t} W₊(t - s) Pⱼ Pⱼ* F(s) ds‖_{L^q_t L^r_x} ≤ C 2^{2jγ} ‖F‖_{L^p_t L^{r'}_x}` tested
against `G`. -/
theorem exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_fourierMultiplierCLM_le
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ) {p : ℝ≥0}
    (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ ψ (((2 : ℝ) ^ j)⁻¹ • ξ)) →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F → AEStronglyMeasurable G →
        ‖∫ t, ∫ s in Set.Iio t, ⟪halfWavePropagator ℂ (t - s)
          (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ (star m) (F s))), G t⟫_ℂ‖ₑ ≤
        C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) *
          eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C, hC⟩ :=
    exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_fourierMultiplierCLM_le
      (r' := r') hψ hψc hψ0 hq hpq hqr
  exact ⟨C, fun j m hm F G hF hG ↦
    (enorm_integral_setIntegral_Iio_le_lintegral_lintegral_enorm _).trans (hC j m hm F G hF hG)⟩

/-- **The dual frequency-localized Strichartz estimate for the wave equation.** Let `E` have
dimension `n`, let `ψ` be smooth, compactly supported and vanish near the origin, and let
`(q, r)` be wave-admissible: `2 < q < ∞` and `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `p`
and `r'` the Hölder conjugates of `q` and `r`. Put `γ = n / 2 - n / r - 1 / q`. There is `C` such
that for every `j ∈ ℤ`, every multiplier `Pⱼ` with symbol `ψ (2^{-j} ·)` and every almost
everywhere strongly measurable `F : ℝ → L²(E)` for which `s ↦ Pⱼ* W₊(-s) F(s)` is integrable,

`‖∫ Pⱼ* W₊(-s) F(s) ds‖₂ ≤ C 2^{jγ} ‖F‖_{L^p_t L^{r'}_x}`. -/
theorem exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ) {p : ℝ≥0}
    (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ ψ (((2 : ℝ) ^ j)⁻¹ • ξ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      Integrable (fun s ↦ Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-s) (F s))) →
        ‖∫ s, Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-s) (F s))‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 1 / q)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume := by
  obtain ⟨A, hA0, hA⟩ :=
    exists_eLpNorm_halfWavePropagator_comp_fourierMultiplierCLM_apply_adjoint_le (r' := r') hψ hψc
      hψ0 hq hqr
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le (𝕜 := ℂ) (H := Lp ℂ 2 (volume : Measure E))
    (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq hpq
  refine ⟨C * (√A).toNNReal, fun j m hm F hF hPF ↦ ?_⟩
  have h := hC (fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m) _ (hA j m hm) F hF
    (by simpa only [adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply] using hPF)
  simp only [adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply] at h
  refine h.trans_eq ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ofReal_rpow_mul_rpow_two_mul hA0.le (zpow_pos two_pos j), ENNReal.coe_mul,
    ENNReal.ofNNReal_toNNReal]
  ring

/-- **The frequency-localized Strichartz estimate for the wave equation**, in weak form. Let `E`
have dimension `n`, let `ψ` be smooth, compactly supported and vanish near the origin, and let
`(q, r)` be wave-admissible: `2 < q < ∞` and `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `p`
and `r'` the Hölder conjugates of `q` and `r`. Put `γ = n / 2 - n / r - 1 / q`. There is `C` such
that for every `j ∈ ℤ`, every multiplier `Pⱼ` with symbol `ψ (2^{-j} ·)`, every `f ∈ L²(E)` and
every almost everywhere strongly measurable `G : ℝ → L²(E)` for which `t ↦ Pⱼ* W₊(-t) G(t)` is
integrable,

`|∫ ⟪W₊(t) Pⱼ f, G(t)⟫ dt| ≤ C 2^{jγ} ‖f‖₂ ‖G‖_{L^p_t L^{r'}_x}`.

This is `‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{jγ} ‖f‖₂` tested against `G`. -/
theorem exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ) {p : ℝ≥0}
    (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ ψ (((2 : ℝ) ^ j)⁻¹ • ξ)) →
      ∀ (f : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)),
      AEStronglyMeasurable G →
      Integrable (fun t ↦ Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-t) (G t))) →
        ‖∫ t, ⟪halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f), G t⟫_ℂ‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 1 / q)) * ‖f‖ₑ *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨A, hA0, hA⟩ :=
    exists_eLpNorm_halfWavePropagator_comp_fourierMultiplierCLM_apply_adjoint_le (r' := r') hψ hψc
      hψ0 hq hqr
  obtain ⟨C, hC⟩ := exists_enorm_integral_inner_apply_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq hpq
  refine ⟨C * (√A).toNNReal, fun j m hm f G hG hPG ↦ ?_⟩
  refine (hC (fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m) _ (hA j m hm) f G hG
    (by simpa only [adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply] using
      hPG)).trans_eq ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ofReal_rpow_mul_rpow_two_mul hA0.le (zpow_pos two_pos j), ENNReal.coe_mul,
    ENNReal.ofNNReal_toNNReal]
  ring

end TauCeti

/-! ### The Littlewood–Paley blocks -/

namespace ContDiffBump

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (φ : ContDiffBump (0 : E))

/-- **The dispersive estimate for the frequency-localized half-wave propagator from `Lᵖ` to
`L^q`.** Let `E` have dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, and
let `Pⱼ` be the `L²` Fourier multiplier with symbol `ψⱼ`. There is `C > 0` such that for every
`j ∈ ℤ`, every time `t`, all conjugate exponents `p` and `q` with `2 ≤ q ≤ ∞` and every
`f ∈ L² ∩ Lᵖ`,

`‖W₊(t) Pⱼ f‖_q ≤ (C 2^{jn} (1 + 2^j |t|)^(-(n - 1)/2))^(1 - 2/q) ‖f‖_p`.

This interpolates, by the Riesz–Thorin theorem, between the dispersive estimate from `L¹` to
`L^∞` and the bound `‖W₊(t) Pⱼ‖ ≤ 1` on `L²`. -/
theorem exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le_of_memLp :
    ∃ C, 0 < C ∧ ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ (t : ℝ) {p q : ℝ≥0∞}
      [p.HolderConjugate q], 2 ≤ q → ∀ f : Lp ℂ 2 (volume : Measure E), MemLp f p volume →
      eLpNorm (halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f)) q volume ≤
        ENNReal.ofReal ((C * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
          (1 + 2 ^ j * |t|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)) ^ (1 - 2 * (q⁻¹).toReal)) *
          eLpNorm f p volume := by
  obtain ⟨C, -, hC⟩ :=
    φ.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le (F := ℂ)
  refine ⟨max C 1, zero_lt_one.trans_le (le_max_right _ _), fun j m hm t p q _ hq f hf ↦ ?_⟩
  set B := max C 1 * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
    (1 + 2 ^ j * |t|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)
  have hB : 0 ≤ B := by positivity
  have hT : ‖(halfWavePropagator ℂ t).comp (Lp.fourierMultiplierCLM ℂ m)‖ ≤ ((1 : ℝ≥0) : ℝ) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans <|
      (mul_le_mul (norm_halfWavePropagator_le t) (φ.norm_fourierMultiplierCLM_littlewoodPaley_le hm)
        (norm_nonneg _) zero_le_one).trans_eq (by simp)
  have h₀ : ∀ g : Lp ℂ 2 (volume : Measure E), Integrable g →
      eLpNorm ((halfWavePropagator ℂ t).comp (Lp.fourierMultiplierCLM ℂ m) g) ∞ volume ≤
        B.toNNReal * eLpNorm g 1 volume := fun g hg ↦ by
    rw [ENNReal.ofNNReal_toNNReal, ContinuousLinearMap.comp_apply]
    refine (hC j m hm t g hg).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity)) (by positivity)
  have h := ((halfWavePropagator ℂ t).comp
    (Lp.fourierMultiplierCLM ℂ m)).eLpNorm_apply_le_rpow_mul_rpow_mul_eLpNorm h₀ hT hq f hf
  rwa [NNReal.one_rpow, mul_one, ← Real.toNNReal_rpow_of_nonneg hB, ENNReal.ofNNReal_toNNReal,
    ContinuousLinearMap.comp_apply] at h

section Admissible

variable {φ} {p q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- The Littlewood–Paley symbol `ψⱼ` is the dilate `ψ₀ (2^{-j} ·)`. -/
private theorem ae_eq_littlewoodPaley_zero_comp_smul {j : ℤ} {m : Lp ℂ ∞ (volume : Measure E)}
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) :
    m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley 0 (((2 : ℝ) ^ j)⁻¹ • ξ) : ℂ) := by
  filter_upwards [hm] with ξ hξ
  rw [hξ, φ.littlewoodPaley_apply_eq_littlewoodPaley_zero_apply j]

variable (φ)

/-- **The bilinear Strichartz estimate for the frequency-localized wave equation.** Let `E` have
dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, and let `Pⱼ` be the `L²`
Fourier multiplier with symbol `ψⱼ`. Let `(q, r)` be wave-admissible,
`2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates
of `q` and `r`, and let `γ = n / 2 - n / r - 1 / q`. There is `C` such that for every `j ∈ ℤ` and
all almost everywhere strongly measurable `F, G : ℝ → L²(E)`,

`∫∫ |⟪W₊(t - s) Pⱼ Pⱼ F(s), G(t)⟫| ds dt ≤ C 2^{2jγ} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

This is the case `ψ = ψ₀` of
`TauCeti.exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_fourierMultiplierCLM_le`. -/
theorem exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_littlewoodPaley_le
    (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F → AEStronglyMeasurable G →
        ∫⁻ t, ∫⁻ s, ‖⟪halfWavePropagator ℂ (t - s)
            (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹))) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C, hC⟩ :=
    exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_fourierMultiplierCLM_le
      (r' := r') (φ.contDiff_ofReal_littlewoodPaley 0)
      (φ.hasCompactSupport_ofReal_littlewoodPaley 0)
      (φ.zero_notMem_tsupport_ofReal_littlewoodPaley 0) hq hpq hqr
  refine ⟨C, fun j m hm F G hF hG ↦ ?_⟩
  simpa only [Lp.star_eq_self_of_ae_eq_ofReal hm, one_div] using
    hC j m (ae_eq_littlewoodPaley_zero_comp_smul hm) F G hF hG

/-- **The retarded Strichartz estimate for the frequency-localized wave equation**, in weak form.
Under the hypotheses of
`ContDiffBump.exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_littlewoodPaley_le`,
there is `C` such that for every `j ∈ ℤ` and all almost everywhere strongly measurable
`F, G : ℝ → L²(E)`,

`|∫ ∫_{s < t} ⟪W₊(t - s) Pⱼ Pⱼ F(s), G(t)⟫ ds dt|`
`  ≤ C 2^{2jγ} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

This is the Duhamel estimate
`‖∫_{s < t} W₊(t - s) Pⱼ Pⱼ F(s) ds‖_{L^q_t L^r_x} ≤ C 2^{2jγ} ‖F‖_{L^p_t L^{r'}_x}` tested
against `G`. -/
theorem exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_littlewoodPaley_le
    (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F → AEStronglyMeasurable G →
        ‖∫ t, ∫ s in Set.Iio t, ⟪halfWavePropagator ℂ (t - s)
            (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹))) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C, hC⟩ :=
    φ.exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_littlewoodPaley_le (r' := r')
      hq hpq hqr
  exact ⟨C, fun j m hm F G hF hG ↦
    (enorm_integral_setIntegral_Iio_le_lintegral_lintegral_enorm _).trans (hC j m hm F G hF hG)⟩

/-- **The dual Strichartz estimate for the frequency-localized wave equation.** Let `E` have
dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, and let `Pⱼ` be the `L²`
Fourier multiplier with symbol `ψⱼ`. Let `(q, r)` be wave-admissible,
`2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates
of `q` and `r`, and let `γ = n / 2 - n / r - 1 / q`. There is `C` such that for every `j ∈ ℤ` and
every almost everywhere strongly measurable `F : ℝ → L²(E)` for which `s ↦ W₊(-s) Pⱼ F(s)` is
integrable,

`‖∫ W₊(-s) Pⱼ F(s) ds‖₂ ≤ C 2^{jγ} ‖F‖_{L^p_t L^{r'}_x}`.

This is the case `ψ = ψ₀` of
`TauCeti.exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le`. -/
theorem exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
        Integrable (fun s ↦ halfWavePropagator ℂ (-s) (Lp.fourierMultiplierCLM ℂ m (F s))) →
        ‖∫ s, halfWavePropagator ℂ (-s) (Lp.fourierMultiplierCLM ℂ m (F s))‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le
    (r' := r') (φ.contDiff_ofReal_littlewoodPaley 0) (φ.hasCompactSupport_ofReal_littlewoodPaley 0)
    (φ.zero_notMem_tsupport_ofReal_littlewoodPaley 0) hq hpq hqr
  refine ⟨C, fun j m hm F hF hWF ↦ ?_⟩
  simpa only [Lp.star_eq_self_of_ae_eq_ofReal hm, fourierMultiplierCLM_halfWavePropagator_apply,
    one_div] using hC j m (ae_eq_littlewoodPaley_zero_comp_smul hm) F hF
      (by simpa only [Lp.star_eq_self_of_ae_eq_ofReal hm,
        fourierMultiplierCLM_halfWavePropagator_apply] using hWF)

/-- **The Strichartz estimate for the frequency-localized wave equation**, in weak form. Let `E`
have dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, and let `Pⱼ` be the
`L²` Fourier multiplier with symbol `ψⱼ`. Let `(q, r)` be wave-admissible,
`2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates
of `q` and `r`, and let `γ = n / 2 - n / r - 1 / q`. There is `C` such that for every `j ∈ ℤ`,
every `f ∈ L²(E)` and every almost everywhere strongly measurable `G : ℝ → L²(E)` for which
`t ↦ W₊(-t) Pⱼ G(t)` is integrable,

`|∫ ⟪W₊(t) Pⱼ f, G(t)⟫ dt| ≤ C 2^{jγ} ‖f‖₂ ‖G‖_{L^p_t L^{r'}_x}`.

This is `‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{jγ} ‖f‖₂` tested against `G`, the case `ψ = ψ₀` of
`TauCeti.exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le`. -/
theorem exists_enorm_integral_inner_halfWavePropagator_littlewoodPaley_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (f : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)),
        AEStronglyMeasurable G →
        Integrable (fun t ↦ halfWavePropagator ℂ (-t) (Lp.fourierMultiplierCLM ℂ m (G t))) →
        ‖∫ t, ⟪halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f), G t⟫_ℂ‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) * ‖f‖ₑ *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le
    (r' := r') (φ.contDiff_ofReal_littlewoodPaley 0) (φ.hasCompactSupport_ofReal_littlewoodPaley 0)
    (φ.zero_notMem_tsupport_ofReal_littlewoodPaley 0) hq hpq hqr
  refine ⟨C, fun j m hm f G hG hWG ↦ ?_⟩
  simpa only [one_div] using hC j m (ae_eq_littlewoodPaley_zero_comp_smul hm) f G hG
    (by simpa only [Lp.star_eq_self_of_ae_eq_ofReal hm,
      fourierMultiplierCLM_halfWavePropagator_apply] using hWG)

end Admissible

section TimeExponentTop

/-! ### The pairs `(∞, r)`

At `q = ∞` the wave-admissibility condition reduces to `r ≥ 2`, and the frequency-localized
estimates only need the time pairings at equal times, `U(t) U(t)* = W₊(0) Pⱼ Pⱼ`, bounded from
`L^{r'}` to `L^r` by the dispersive estimate at time `0`. -/

variable {φ} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- The square root of the constant `A 2^{2ja}` of the time pairings is `√A 2^{ja}`. -/
private theorem coe_mul_ofReal_rpow_two_mul_rpow_inv_two (A : ℝ≥0) {x : ℝ} (hx : 0 ≤ x)
    (a : ℝ) :
    ((A : ℝ≥0∞) * ENNReal.ofReal (x ^ (2 * a))) ^ (2⁻¹ : ℝ) =
      (NNReal.sqrt A : ℝ≥0∞) * ENNReal.ofReal (x ^ a) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg (by positivity)
    (by norm_num), ← Real.rpow_mul hx, NNReal.sqrt_eq_rpow, ENNReal.coe_rpow_of_nonneg _
    (by norm_num), one_div]
  congr 3
  ring

variable (φ)

/-- **The time pairings at equal times**: for `r ≥ 2` there is `A` such that for every scale `j`,
every time `t` and every `g ∈ L²`, `‖U(t) U(t)* g‖_r ≤ A 2^{2jγ} ‖g‖_{r'}`, where `U(t) = W₊(t) Pⱼ`
and `γ = n / 2 - n / r`. -/
private theorem exists_eLpNorm_halfWavePropagator_comp_adjoint_self_le (hr : 2 ≤ r) :
    ∃ A : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ (t : ℝ)
      (g : Lp ℂ 2 (volume : Measure E)),
        eLpNorm ((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)
          (((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) g)) r volume ≤
        A * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal))) * eLpNorm g r' volume := by
  obtain ⟨C, hC0, hC⟩ :=
    φ.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le_of_memLp
  set K := eLpNorm (𝓕⁻ (fun ξ ↦ (φ.littlewoodPaley 0 ξ : ℂ))) 1 volume
  set θ := 1 - 2 * (r⁻¹).toReal
  refine ⟨(C ^ θ).toNNReal * K.toNNReal, fun j m hm t g ↦ ?_⟩
  rw [halfWavePropagator_comp_fourierMultiplierCLM_apply_adjoint,
    Lp.star_eq_self_of_ae_eq_ofReal hm, sub_self]
  have h2 : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  -- At time `0` the dispersive factor is `1`, and `n θ = 2 γ`.
  set D := C ^ θ * ((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
    Module.finrank ℝ E * (r⁻¹).toReal))
  have hDe : (C * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
      (1 + 2 ^ j * |(0 : ℝ)|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)) ^ θ = D := by
    simp only [abs_zero, mul_zero, add_zero, Real.one_rpow, mul_one]
    rw [Real.mul_rpow hC0.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h2.le]
    congr 2
    simp only [θ]
    ring
  have hD : 0 < D := by positivity
  -- The dispersive estimate at time `0`, then the uniform `Lᵖ` bound on `Pⱼ`.
  calc _ ≤ ENNReal.ofReal D * eLpNorm (Lp.fourierMultiplierCLM ℂ m g) r' volume := by
        by_cases hPg : MemLp (Lp.fourierMultiplierCLM ℂ m g) r' volume
        · exact (hC j m hm 0 hr _ hPg).trans_eq (by rw [hDe])
        · rw [top_unique (not_lt.1 (memLp_iff.not.1 hPg)),
            ENNReal.mul_top (ENNReal.ofReal_pos.2 hD).ne']
          exact le_top
    _ ≤ ENNReal.ofReal D * (K * eLpNorm g r' volume) := by
        gcongr
        exact φ.eLpNorm_fourierMultiplierCLM_littlewoodPaley_le hm g
          (ENNReal.HolderConjugate.one_le r' r)
    _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal,
          ENNReal.coe_toNNReal (φ.memLp_fourierInv_littlewoodPaley 0 1).eLpNorm_ne_top,
          ENNReal.ofReal_mul (by positivity)]
        ring

/-- **The dual Strichartz estimate for the frequency-localized wave equation at the pairs
`(∞, r)`.** Let `E` have dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`,
and let `Pⱼ` be the `L²` Fourier multiplier with symbol `ψⱼ`. Let `2 ≤ r ≤ ∞`, let `r'` be its
Hölder conjugate, and let `γ = n / 2 - n / r`. There is `C` such that for every `j ∈ ℤ` and every
almost everywhere strongly measurable `F : ℝ → L²(E)`,

`‖∫ W₊(-s) Pⱼ F(s) ds‖₂ ≤ C 2^{jγ} ‖F‖_{L¹_t L^{r'}_x}`. -/
theorem exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le_eLpNorm_one
    (hr : 2 ≤ r) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
        ‖∫ s, halfWavePropagator ℂ (-s) (Lp.fourierMultiplierCLM ℂ m (F s))‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) 1 volume := by
  obtain ⟨A, hA⟩ := φ.exists_eLpNorm_halfWavePropagator_comp_adjoint_self_le (r' := r') hr
  refine ⟨NNReal.sqrt A, fun j m hm F hF ↦ ?_⟩
  have h := enorm_integral_adjoint_le_eLpNorm_one
    (U := fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)
    (fun t g ↦ hA j m hm t g) hF
  simp only [adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply,
    Lp.star_eq_self_of_ae_eq_ofReal hm, fourierMultiplierCLM_halfWavePropagator_apply] at h
  rwa [coe_mul_ofReal_rpow_two_mul_rpow_inv_two A (by positivity)] at h

/-- **The Strichartz estimate for the frequency-localized wave equation at the pairs `(∞, r)`**,
in weak form. Let `E` have dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`,
and let `Pⱼ` be the `L²` Fourier multiplier with symbol `ψⱼ`. Let `2 ≤ r ≤ ∞`, let `r'` be its
Hölder conjugate, and let `γ = n / 2 - n / r`. There is `C` such that for every `j ∈ ℤ`, every
`f ∈ L²(E)` and every almost everywhere strongly measurable `G : ℝ → L²(E)`,

`|∫ ⟪W₊(t) Pⱼ f, G(t)⟫ dt| ≤ C 2^{jγ} ‖f‖₂ ‖G‖_{L¹_t L^{r'}_x}`.

This is `‖W₊(t) Pⱼ f‖_{L^∞_t L^r_x} ≤ C 2^{jγ} ‖f‖₂` tested against `G`. -/
theorem exists_enorm_integral_inner_halfWavePropagator_littlewoodPaley_le_eLpNorm_one
    (hr : 2 ≤ r) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (f : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)),
        AEStronglyMeasurable G →
        ‖∫ t, ⟪halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f), G t⟫_ℂ‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal)) * ‖f‖ₑ *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) 1 volume := by
  obtain ⟨A, hA⟩ := φ.exists_eLpNorm_halfWavePropagator_comp_adjoint_self_le (r' := r') hr
  refine ⟨NNReal.sqrt A, fun j m hm f G hG ↦ ?_⟩
  have h := enorm_integral_inner_apply_le_eLpNorm_one
    (U := fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)
    (fun t g ↦ hA j m hm t g) f hG
  rw [coe_mul_ofReal_rpow_two_mul_rpow_inv_two A (by positivity)] at h
  exact h

end TimeExponentTop

end ContDiffBump

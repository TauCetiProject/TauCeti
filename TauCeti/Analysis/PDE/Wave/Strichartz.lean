/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Strichartz.TTStar
public import TauCeti.Analysis.PDE.Wave.Dispersive
import TauCeti.MeasureTheory.Integral.RieszThorin

/-!
# Frequency-localized Strichartz estimates for the wave equation

Let `E` have dimension `n`, let `ψ` be smooth, compactly supported and vanish near the origin, and
for `j ∈ ℤ` let `Pⱼ` be the `L²` Fourier multiplier with the dilated symbol `ψ (2^{-j} ·)`, which
localizes to frequencies `‖ξ‖ ≈ 2^j`; the Littlewood–Paley blocks are the case where `ψ` is the
cutoff `ψ₀` of `ContDiffBump.littlewoodPaley`. This file proves the Strichartz estimates for the
frequency-localized half-wave propagators `W₊(t) Pⱼ`, `W₊(t) = exp(itD)`, `D = √(-Δ)`, with
constants independent of `j`.

A pair `(q, r)` is *wave-admissible* when `2 ≤ r`, `2 < q < ∞` and

`2 / q + (n - 1) / r ≤ (n - 1) / 2`,

the non-endpoint, finite-`q` part of the region of Tao, Theorem 2.6 (the excluded pair
`(2, ∞)` in dimension `3` has `q = 2`). Admissibility forces `n ≥ 2` and `r > 2`. The regularity
exponent is the scaling-critical `σ = n / 2 - n / r - 1 / q`. The main estimate is

`‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{jσ} ‖f‖₂`,

stated, like the Schrödinger estimates of `TauCeti.Analysis.PDE.Schrodinger.Strichartz`, in weak
form against `G ∈ L^{q'}_t L^{r'}_x`, together with its dual form, the bilinear bound for the
Duhamel pairings and its retarded restriction to `s < t`.

## The argument

The time pairings of `U(t) = W₊(t) Pⱼ` are `U(s) U(t)* = W₊(s - t) Pⱼ Pⱼ*`, and `Pⱼ Pⱼ*` is the
multiplier with the dilated symbol `|ψ|² (2^{-j} ·)`, again a smooth cutoff vanishing near the
origin. The dispersive estimate for dilated cutoffs
(`TauCeti.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_le`) bounds it from `L¹` to `L^∞`
by `C 2^{jn} (1 + 2^j |τ|)^(-(n - 1)/2)`, and it is bounded on `L²` uniformly in `j`. The
Riesz–Thorin theorem interpolates the two to an `L^{r'} → L^r` bound with the factor
`(1 + 2^j |τ|)^(-(n - 1)(1/2 - 1/r))`, and admissibility makes this at most `(2^j |τ|)^(-2/q)`.
So the pairings decay like `A 2^{2jσ} |τ|^(-2/q)`, which is the hypothesis of the abstract `TT*`
estimates of `TauCeti.Analysis.PDE.Strichartz.TTStar`; their constant is linear in `A` for the
bilinear bound and in `A ^ (1/2)` for the others, which produces the factors `2^{2jσ}` and `2^{jσ}`.

## Main declarations

* `TauCeti.exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_fourierMultiplierCLM_le`:
  the bilinear estimate for the frequency-localized Duhamel pairings.
* `exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_fourierMultiplierCLM_le`:
  the retarded estimate, in weak form.
* `TauCeti.exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le`: the dual
  estimate `‖∫ Pⱼ* W₊(-s) F(s) ds‖₂ ≤ C 2^{jσ} ‖F‖_{L^{q'}_t L^{r'}_x}`.
* `TauCeti.exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le`: the
  homogeneous estimate, in weak form.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Sections 2.2–2.3 and Theorem 2.6.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace InnerProduct ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Time pairings -/

/-- The adjoint of `W₊(t) T_m` is `T_{star m} W₊(-t)`. -/
private theorem adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply
    (m : Lp ℂ ∞ (volume : Measure E)) (t : ℝ) (g : Lp ℂ 2 (volume : Measure E)) :
    ((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) g =
      Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-t) g) := by
  rw [ContinuousLinearMap.adjoint_comp, Lp.adjoint_fourierMultiplierCLM,
    adjoint_halfWavePropagator, ContinuousLinearMap.comp_apply]

/-- The time pairings `U(s) U(t)*` of `U(t) = W₊(t) T_m` are `W₊(s - t) T_m T_{star m}`. -/
private theorem halfWavePropagator_comp_apply_adjoint (m : Lp ℂ ∞ (volume : Measure E))
    (s t : ℝ) (g : Lp ℂ 2 (volume : Measure E)) :
    (halfWavePropagator ℂ s ∘L Lp.fourierMultiplierCLM ℂ m)
        (((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) g) =
      halfWavePropagator ℂ (s - t)
        (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ (star m) g)) := by
  rw [adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply, ContinuousLinearMap.comp_apply,
    fourierMultiplierCLM_halfWavePropagator_apply, fourierMultiplierCLM_halfWavePropagator_apply,
    halfWavePropagator_def, halfWavePropagator_def, halfWavePropagator_def,
    ← phasePropagator_add_apply, ← sub_eq_add_neg]

/-- The decay of the Riesz–Thorin bound: if `(q, r)` is wave-admissible, `a = 1 / r` and
`c = 2^j`, then

`(C₁ c^n (1 + c |τ|)^(-(n - 1)/2))^(1 - 2a) B₁^(2a) ≤ C₁^(1 - 2a) B₁^(2a) c^{2σ} |τ|^(-2/q)`

with `σ = n / 2 - n a - 1 / q`. -/
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

`‖T g‖_r ≤ C₁^(1 - 2/r) B₁^(2/r) c^{2σ} |τ|^(-2/q) ‖g‖_{r'}`,

with `σ = n / 2 - n / r - 1 / q`: the Riesz–Thorin theorem followed by admissibility. -/
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
`U(t) = W₊(t) Pⱼ` decay from `L^{r'}` to `L^r` like `A 2^{2jσ} |s - t| ^ (-2 / q)` along a
wave-admissible pair, with `A` independent of `j`. -/
private theorem exists_eLpNorm_halfWavePropagator_comp_apply_adjoint_le (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ) (hq : 2 < q) (hr : 2 ≤ r)
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
  rw [halfWavePropagator_comp_apply_adjoint, Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply,
    ← ContinuousLinearMap.comp_apply]
  refine eLpNorm_apply_le_of_eLpNorm_top_le hq hr hqr _ (by positivity) (by positivity)
    (zpow_pos two_pos j) (sub_ne_zero.2 hst) (fun f hf ↦ ?_) ?_ g
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
          · refine (Lp.norm_fourierMultiplierCLM_le m').trans ?_
            rw [Lp.norm_def, eLpNorm_exponent_top]
            · exact ENNReal.toReal_le_of_le_ofReal hB0
                (eLpNormEssSup_le_of_ae_bound (hm'.mono fun ξ h ↦ h ▸ hB _))
            · exact Lp.aestronglyMeasurable _
      _ ≤ B + 1 := by linarith

/-! ### The Strichartz estimates -/

/-- **The bilinear frequency-localized Strichartz estimate for the wave equation.** Let `E` have
dimension `n`, let `ψ` be smooth, compactly supported and vanish near the origin, and let
`(q, r)` be wave-admissible: `2 ≤ r`, `2 < q < ∞` and `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `p`
and `r'` the Hölder conjugates of `q` and `r`. Put `σ = n / 2 - n / r - 1 / q`. There is `C` such
that for every `j ∈ ℤ`, every multiplier `Pⱼ` with symbol `ψ (2^{-j} ·)` and all almost
everywhere strongly measurable `F, G : ℝ → L²(E)`,

`∫∫ |⟪W₊(t - s) Pⱼ Pⱼ* F(s), G(t)⟫| ds dt ≤ C 2^{2jσ} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

Since the integrand is the absolute value of the Duhamel pairing, the bound also controls the
integral over any part of the `(s, t)` plane, such as the retarded region `s < t`
(`exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_fourierMultiplierCLM_le`).
-/
theorem exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_fourierMultiplierCLM_le
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ) {p : ℝ≥0}
    (hq : 2 < q) (hpq : p.HolderConjugate q) (hr : 2 ≤ r)
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
    exists_eLpNorm_halfWavePropagator_comp_apply_adjoint_le (r' := r') hψ hψc hψ0 hq hr hqr
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
    rw [ContinuousLinearMap.adjoint_inner_left, halfWavePropagator_comp_apply_adjoint,
      ← ofReal_norm, ← ofReal_norm, norm_inner_symm]
  simp_rw [hpair]
  calc _ ≤ _ := hC (fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m) _
        (hA j m hm) G F hG hF
    _ = _ := by
        rw [ENNReal.ofReal_mul hA0.le, ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal]
        ring

/-- **The retarded frequency-localized Strichartz estimate for the wave equation**, in weak form.
Let `E` have dimension `n`, let `ψ` be smooth, compactly supported and vanish near the origin, and
let `(q, r)` be wave-admissible: `2 ≤ r`, `2 < q < ∞` and `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with
`p` and `r'` the Hölder conjugates of `q` and `r`. Put `σ = n / 2 - n / r - 1 / q`. There is `C`
such that for every `j ∈ ℤ`, every multiplier `Pⱼ` with symbol `ψ (2^{-j} ·)` and all almost
everywhere strongly measurable `F, G : ℝ → L²(E)`,

`|∫ ∫_{s < t} ⟪W₊(t - s) Pⱼ Pⱼ* F(s), G(t)⟫ ds dt| ≤
  C 2^{2jσ} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

This is the Duhamel estimate
`‖∫_{s < t} W₊(t - s) Pⱼ Pⱼ* F(s) ds‖_{L^q_t L^r_x} ≤ C 2^{2jσ} ‖F‖_{L^p_t L^{r'}_x}` tested
against `G`. -/
theorem exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_fourierMultiplierCLM_le
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ) {p : ℝ≥0}
    (hq : 2 < q) (hpq : p.HolderConjugate q) (hr : 2 ≤ r)
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
      (r' := r') hψ hψc hψ0 hq hpq hr hqr
  refine ⟨C, fun j m hm F G hF hG ↦ ?_⟩
  set P := fun s ↦ Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ (star m) (F s))
  calc _ ≤ ∫⁻ t, ‖∫ s in Set.Iio t, ⟪halfWavePropagator ℂ (t - s) (P s), G t⟫_ℂ‖ₑ :=
        eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ t, ∫⁻ s in Set.Iio t, ‖⟪halfWavePropagator ℂ (t - s) (P s), G t⟫_ℂ‖ₑ :=
        lintegral_mono fun t ↦ eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ t, ∫⁻ s, ‖⟪halfWavePropagator ℂ (t - s) (P s), G t⟫_ℂ‖ₑ :=
        lintegral_mono fun t ↦ setLIntegral_le_lintegral _ _
    _ ≤ _ := hC j m hm F G hF hG

/-- **The dual frequency-localized Strichartz estimate for the wave equation.** Let `E` have
dimension `n`, let `ψ` be smooth, compactly supported and vanish near the origin, and let
`(q, r)` be wave-admissible: `2 ≤ r`, `2 < q < ∞` and `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `p`
and `r'` the Hölder conjugates of `q` and `r`. Put `σ = n / 2 - n / r - 1 / q`. There is `C` such
that for every `j ∈ ℤ`, every multiplier `Pⱼ` with symbol `ψ (2^{-j} ·)` and every almost
everywhere strongly measurable `F : ℝ → L²(E)` for which `s ↦ Pⱼ* W₊(-s) F(s)` is integrable,

`‖∫ Pⱼ* W₊(-s) F(s) ds‖₂ ≤ C 2^{jσ} ‖F‖_{L^p_t L^{r'}_x}`. -/
theorem exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ) {p : ℝ≥0}
    (hq : 2 < q) (hpq : p.HolderConjugate q) (hr : 2 ≤ r)
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
    exists_eLpNorm_halfWavePropagator_comp_apply_adjoint_le (r' := r') hψ hψc hψ0 hq hr hqr
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
`(q, r)` be wave-admissible: `2 ≤ r`, `2 < q < ∞` and `2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `p`
and `r'` the Hölder conjugates of `q` and `r`. Put `σ = n / 2 - n / r - 1 / q`. There is `C` such
that for every `j ∈ ℤ`, every multiplier `Pⱼ` with symbol `ψ (2^{-j} ·)`, every `f ∈ L²(E)` and
every almost everywhere strongly measurable `G : ℝ → L²(E)` for which `t ↦ Pⱼ* W₊(-t) G(t)` is
integrable,

`|∫ ⟪W₊(t) Pⱼ f, G(t)⟫ dt| ≤ C 2^{jσ} ‖f‖₂ ‖G‖_{L^p_t L^{r'}_x}`.

This is `‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{jσ} ‖f‖₂` tested against `G`. -/
theorem exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ) {p : ℝ≥0}
    (hq : 2 < q) (hpq : p.HolderConjugate q) (hr : 2 ≤ r)
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
    exists_eLpNorm_halfWavePropagator_comp_apply_adjoint_le (r' := r') hψ hψc hψ0 hq hr hqr
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

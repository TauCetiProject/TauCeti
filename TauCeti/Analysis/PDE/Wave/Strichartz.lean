/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Strichartz.TTStar
public import TauCeti.Analysis.PDE.Wave.Dispersive
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Star
import TauCeti.MeasureTheory.Integral.RieszThorin

/-!
# Frequency-localized Strichartz estimates for the half-wave propagator

On a finite-dimensional real inner product space `E` of dimension `n`, let `W(t) = exp(itD)`,
`D = √(-Δ)`, be the half-wave propagator (`TauCeti.halfWavePropagator`), let `ψⱼ` be the
Littlewood–Paley cutoffs built from a bump function `φ`, supported where `‖ξ‖ ≈ 2^j`, and let
`Pⱼ` be the `L²` Fourier multiplier with symbol `ψⱼ`. This file proves the Strichartz estimates
for the frequency-localized propagators `W(t) Pⱼ`, uniformly in the scale `j ∈ ℤ`, in the weak
form tested against `G ∈ L^{q'}_t L^{r'}_x` together with the dual and bilinear forms:

`‖W(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{j σ} ‖f‖₂`,  `σ = n / 2 - n / r - 1 / q`,

for every wave-admissible pair `(q, r)`, `q, r ≥ 2` and `1 / q + (n - 1) / (2 r) ≤ (n - 1) / 4`,
with `2 < q < ∞`; the admissibility condition with `q < ∞` forces `n ≥ 2`. The exponent `σ` is the
scaling-critical regularity: these are the dyadic pieces from which the wave Strichartz estimates
with homogeneous Sobolev data of order `σ` are assembled by Littlewood–Paley summation.

## The argument

The time pairings of the family `U(t) = W(t) Pⱼ` are `U(s) U(t)* = W(s - t) Pⱼ²`, since `Pⱼ` is
self-adjoint and commutes with `W`. The dispersive estimate for the frequency-localized propagator
(`ContDiffBump.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le`) and
the uniform `L¹` bound for `Pⱼ`
(`ContDiffBump.exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le`) give

`‖W(τ) Pⱼ² g‖_∞ ≤ C 2^{jn} (1 + 2^j |τ|)^(-(n - 1)/2) ‖g‖₁`,

and `‖W(τ) Pⱼ²‖_{L² → L²} ≤ 1`. The Riesz–Thorin theorem interpolates these to an
`L^{r'} → L^r` bound with the factor `(1 + 2^j |τ|)^(-(n - 1)(1/2 - 1/r))`, which is at most
`(2^j |τ|)^(-2/q)` exactly when `(q, r)` is wave-admissible. So the time pairings decay like
`A |s - t|^(-2/q)` with `A = C 2^{j(n (1 - 2/r) - 2/q)} = C 2^{2 j σ}`, and the non-endpoint
`TT*` argument (`TauCeti.Analysis.PDE.Strichartz.TTStar`) gives the estimates with the factor
`A ^ (1/2) = C 2^{j σ}`.

## Main declarations

All in the `ContDiffBump` namespace:

* `exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_fourierMultiplierCLM_le`: the
  bilinear estimate for the Duhamel pairings `⟪W(t - s) Pⱼ² F(s), G(t)⟫`.
* `exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le`: the dual estimate
  `‖∫ Pⱼ W(-s) F(s) ds‖₂ ≤ C 2^{j σ} ‖F‖_{L^{q'}_t L^{r'}_x}`.
* `exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le`: the homogeneous
  estimate `‖W(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{j σ} ‖f‖₂`, in weak form.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3, Theorem 2.6 and its proof.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace InnerProduct FourierTransform SchwartzMap

namespace ContDiffBump

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (φ : ContDiffBump (0 : E))

/-! ### The time pairings of `W(t) Pⱼ` -/

section TimePairing

variable {φ} {j : ℤ} {m : Lp ℂ ∞ (volume : Measure E)}

/-- The adjoint of `W(t) Pⱼ` is `Pⱼ W(-t)`. -/
private theorem adjoint_halfWavePropagator_comp_fourierMultiplierCLM
    (hm : m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))) (t : ℝ) :
    (halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)† =
      Lp.fourierMultiplierCLM ℂ m ∘L halfWavePropagator ℂ (-t) := by
  rw [ContinuousLinearMap.adjoint_comp, Lp.adjoint_fourierMultiplierCLM,
    Lp.star_eq_self_of_ae_eq_ofReal hm, halfWavePropagator_def, adjoint_phasePropagator]

/-- The adjoint of `W(t) Pⱼ` applied to `g` is `Pⱼ (W(-t) g)`. -/
private theorem adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply
    (hm : m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))) (t : ℝ)
    (g : Lp ℂ 2 (volume : Measure E)) :
    ((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) g =
      Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ (-t) g) := by
  rw [adjoint_halfWavePropagator_comp_fourierMultiplierCLM hm, ContinuousLinearMap.comp_apply]

/-- The time pairings of the family `W(t) Pⱼ` are `W(s - t) Pⱼ²`. -/
private theorem halfWavePropagator_comp_apply_adjoint_apply
    (hm : m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))) (s t : ℝ)
    (g : Lp ℂ 2 (volume : Measure E)) :
    (halfWavePropagator ℂ s ∘L Lp.fourierMultiplierCLM ℂ m)
        (((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) g) =
      halfWavePropagator ℂ (s - t)
        (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m g)) := by
  have hcomm (τ : ℝ) (h : Lp ℂ 2 (volume : Measure E)) :
      Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ τ h) =
        halfWavePropagator ℂ τ (Lp.fourierMultiplierCLM ℂ m h) :=
    (DFunLike.congr_fun (phasePropagator_comp_fourierMultiplierCLM _ τ m) h).symm
  rw [adjoint_halfWavePropagator_comp_fourierMultiplierCLM hm, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, hcomm, hcomm, sub_eq_add_neg,
    halfWavePropagator_def, phasePropagator_add_apply]

/-- The interpolated dispersive constant: if `0 ≤ M ≤ c x ^ n (1 + x y) ^ (-(n - 1)/2)` with
`x, y > 0`, then `M ^ θ ≤ c ^ θ x ^ (n θ - γ) y ^ (-γ)` whenever `θ ≥ 0` and
`0 ≤ γ ≤ (n - 1) θ / 2`. With `x = 2^j` and `y = |s - t|`, this turns the dyadic dispersive decay
into the `|s - t| ^ (-γ)` decay of the `TT*` argument. -/
private theorem rpow_le_mul_rpow_mul_rpow_neg {M c x y n θ γ : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hx : 0 < x) (hy : 0 < y) (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) (hγθ : γ ≤ (n - 1) / 2 * θ)
    (hMc : M ≤ c * (x ^ n * (1 + x * y) ^ (-(n - 1) / 2))) :
    M ^ θ ≤ c ^ θ * (x ^ (n * θ - γ) * y ^ (-γ)) := by
  have hdecay : ((1 + x * y) ^ (-(n - 1) / 2)) ^ θ ≤ x ^ (-γ) * y ^ (-γ) := by
    rw [← Real.rpow_mul (by positivity), ← Real.mul_rpow hx.le hy.le]
    -- `(1 + x y) ^ (-(n - 1) θ / 2) ≤ (1 + x y) ^ (-γ) ≤ (x y) ^ (-γ)`.
    calc (1 + x * y) ^ (-(n - 1) / 2 * θ) = (1 + x * y) ^ (-((n - 1) / 2 * θ)) := by
          congr 1
          ring
      _ ≤ (1 + x * y) ^ (-γ) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith [mul_pos hx hy]) (neg_le_neg hγθ)
      _ ≤ (x * y) ^ (-γ) := Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  calc M ^ θ ≤ (c * (x ^ n * (1 + x * y) ^ (-(n - 1) / 2))) ^ θ :=
        Real.rpow_le_rpow hM hMc hθ
    _ = c ^ θ * (x ^ (n * θ) * ((1 + x * y) ^ (-(n - 1) / 2)) ^ θ) := by
        rw [Real.mul_rpow hc (by positivity), Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul hx.le]
    _ ≤ c ^ θ * (x ^ (n * θ) * (x ^ (-γ) * y ^ (-γ))) := by gcongr
    _ = c ^ θ * (x ^ (n * θ - γ) * y ^ (-γ)) := by
        rw [← mul_assoc (x ^ (n * θ)), ← Real.rpow_add hx, sub_eq_add_neg]

variable (φ) in
/-- **The dispersive estimate for `W(τ) Pⱼ²`.** There is `C ≥ 0` such that for every `j ∈ ℤ`,
every time `τ` and every integrable `f ∈ L²`,
`‖W(τ) Pⱼ² f‖_∞ ≤ C 2^{jn} (1 + 2^j |τ|)^(-(n - 1)/2) ‖f‖₁`. -/
private theorem exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_sq_le :
    ∃ C, 0 ≤ C ∧ ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ (τ : ℝ)
      (f : Lp ℂ 2 (volume : Measure E)), Integrable f →
      eLpNorm (halfWavePropagator ℂ τ
          (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m f))) ∞ volume ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
          (1 + 2 ^ j * |τ|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)) * eLpNorm f 1 volume := by
  obtain ⟨C₀, hC₀, hdisp⟩ :=
    φ.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le (F := ℂ)
  obtain ⟨K, hK⟩ := φ.exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le (F := ℂ)
  refine ⟨C₀ * K, by positivity, fun j m hm τ f hf ↦ ?_⟩
  -- `Pⱼ f` is integrable, with `‖Pⱼ f‖₁ ≤ K ‖f‖₁`.
  have hPf := hK j m hm le_rfl f
  have hPint : Integrable (Lp.fourierMultiplierCLM ℂ m f) :=
    memLp_one_iff_integrable.1 (hPf.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (memLp_one_iff_integrable.2 hf).eLpNorm_lt_top))
  calc _ ≤ ENNReal.ofReal (C₀ * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
          (1 + 2 ^ j * |τ|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)) *
          eLpNorm (Lp.fourierMultiplierCLM ℂ m f) 1 volume := hdisp j m hm τ _ hPint
    _ ≤ ENNReal.ofReal (C₀ * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
          (1 + 2 ^ j * |τ|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)) *
          (ENNReal.ofReal K * eLpNorm f 1 volume) := by
        gcongr
        simpa using hPf
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

variable {p q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- `W(τ) Pⱼ²` is bounded on `L²` with norm at most `1`. -/
private theorem norm_halfWavePropagator_comp_fourierMultiplierCLM_comp_le_one
    (hm : m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))) (τ : ℝ) :
    ‖halfWavePropagator ℂ τ ∘L (Lp.fourierMultiplierCLM ℂ m ∘L Lp.fourierMultiplierCLM ℂ m)‖ ≤
      1 := by
  have hP : ‖Lp.fourierMultiplierCLM (E := E) ℂ m‖ ≤ 1 :=
    (Lp.norm_fourierMultiplierCLM_le _).trans <| Lp.norm_top_le_of_ae_bound zero_le_one <| by
      filter_upwards [hm] with ξ h
      rw [h, Complex.norm_real, Real.norm_eq_abs]
      exact φ.abs_littlewoodPaley_le_one j ξ
  calc _ ≤ ‖halfWavePropagator (E := E) ℂ τ‖ *
        (‖Lp.fourierMultiplierCLM (E := E) ℂ m‖ * ‖Lp.fourierMultiplierCLM (E := E) ℂ m‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ 1 * (1 * 1) := by
        gcongr
        exact norm_phasePropagator_le _ τ
    _ = 1 := by norm_num

omit [r'.HolderConjugate r] in
/-- The exponents of a wave-admissible pair `(q, r)`, `r ≥ 2` and
`1 / q + (n - 1) / (2 r) ≤ (n - 1) / 4`: the interpolation parameter `θ = 1 - 2 / r` is
nonnegative and the decay exponent `2 / q` is at most `(n - 1) θ / 2`. -/
private theorem exponents_of_admissible {n : ℝ} (hr : 2 ≤ r)
    (hqr : 1 / (q : ℝ) + (n - 1) * (r⁻¹).toReal / 2 ≤ (n - 1) / 4) :
    0 ≤ 1 - 2 * (r⁻¹).toReal ∧ 2 / (q : ℝ) ≤ (n - 1) / 2 * (1 - 2 * (r⁻¹).toReal) := by
  have hr' : (r⁻¹).toReal ≤ 2⁻¹ := by
    rw [← ENNReal.toReal_ofNat 2, ← ENNReal.toReal_inv]
    exact ENNReal.toReal_mono (by simp) (ENNReal.inv_le_inv.2 hr)
  have h2q : (2 : ℝ) / q = 2 * (1 / q) := by ring
  exact ⟨by linarith, by rw [h2q]; linarith⟩

variable (φ) in
/-- **Decay of the time pairings.** Along a wave-admissible pair `(q, r)`, the time
pairings `W(s - t) Pⱼ²` of the family `W(t) Pⱼ` decay from `L^{r'}` to `L^r` like
`c 2^{2 j σ} |s - t| ^ (-2 / q)`, with `σ = n / 2 - n / r - 1 / q` and `c` independent of `j`.
This interpolates, by the Riesz–Thorin theorem, between the dispersive estimate for `W(τ) Pⱼ²`
and its `L²` bound `1`. -/
private theorem exists_eLpNorm_halfWavePropagator_comp_apply_adjoint_apply_le (hr : 2 ≤ r)
    (hqr : 1 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal / 2 ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 4) :
    ∃ c : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ s t, s ≠ t →
      ∀ g : Lp ℂ 2 (volume : Measure E),
        eLpNorm ((halfWavePropagator ℂ s ∘L Lp.fourierMultiplierCLM ℂ m)
            (((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) g)) r volume ≤
          c * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) *
            ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' volume := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  obtain ⟨C, hC, hdisp⟩ := φ.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_sq_le
  -- The interpolation parameter `θ = 1 - 2 / r` and the decay exponent `γ = 2 / q`.
  set θ : ℝ := 1 - 2 * (r⁻¹).toReal
  obtain ⟨hθ0, hγθ⟩ := exponents_of_admissible hr hqr
  refine ⟨((C + 1) ^ θ).toNNReal, fun j m hm s t hst g ↦ ?_⟩
  have hτ : 0 < |s - t| := abs_pos.2 (sub_ne_zero.2 hst)
  have h2 : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  set B : ℝ := C * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E * (1 + 2 ^ j * |s - t|) ^ (-(n - 1) / 2)
  have hB : 0 ≤ B := by positivity
  set P := Lp.fourierMultiplierCLM ℂ m
  -- The `L¹ → L^∞` and `L² → L²` bounds for `W(s - t) Pⱼ²`.
  have h₀ (f : Lp ℂ 2 (volume : Measure E)) (hf : Integrable f) :
      eLpNorm ((halfWavePropagator ℂ (s - t) ∘L (P ∘L P)) f) ∞ volume ≤
        B.toNNReal * eLpNorm f 1 volume := by
    rw [ENNReal.ofNNReal_toNNReal]
    exact hdisp j m hm (s - t) f hf
  have h₁ : ‖halfWavePropagator ℂ (s - t) ∘L (P ∘L P)‖ ≤ (1 : ℝ≥0) := by
    simpa using norm_halfWavePropagator_comp_fourierMultiplierCLM_comp_le_one hm (s - t)
  -- Riesz–Thorin, then the decay of the interpolated constant.
  rw [halfWavePropagator_comp_apply_adjoint_apply hm, ← ContinuousLinearMap.comp_apply P P,
    ← ContinuousLinearMap.comp_apply (halfWavePropagator ℂ (s - t))]
  by_cases hg : MemLp g r' volume
  · refine ((halfWavePropagator ℂ (s - t) ∘L (P ∘L P)).eLpNorm_apply_le_rpow_mul_rpow_mul_eLpNorm
      h₀ h₁ hr g hg).trans ?_
    gcongr
    -- Compare the interpolated constants in `ℝ`, then return to `ℝ≥0∞`.
    have hdecay := rpow_le_mul_rpow_mul_rpow_neg (c := C + 1) (n := n) hB (by linarith) h2 hτ hθ0
      (by positivity) hγθ (by
        simp only [B, n, Real.rpow_natCast]
        rw [← mul_assoc]
        gcongr
        linarith)
    have hexp : n * θ - 2 / q = 2 * (n / 2 - n * (r⁻¹).toReal - 1 / q) := by ring
    rw [hexp] at hdecay
    calc _ = ENNReal.ofReal (B ^ θ) := by
          rw [NNReal.one_rpow, mul_one, ← Real.toNNReal_rpow_of_nonneg hB,
            ENNReal.ofNNReal_toNNReal]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hdecay
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_rpow_of_pos hτ, Real.eNorm_eq_ofReal_abs, mul_assoc,
            ENNReal.ofNNReal_toNNReal]
  · rw [top_unique (not_lt.1 (memLp_iff.not.1 hg)), ENNReal.mul_top]
    · exact le_top
    · refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · simpa using Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < C + 1) θ
      · simpa using Real.rpow_pos_of_pos h2 _
      · exact (ENNReal.rpow_pos (by simpa using hτ.ne') (by simp)).ne'

end TimePairing

/-! ### The Strichartz estimates -/

section Strichartz

variable {p q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- The square root of the `TT*` constant `c x ^ (2 a)` is `c ^ (1/2) x ^ a`. -/
private theorem coe_mul_ofReal_rpow_rpow_inv_two (c : ℝ≥0) {x : ℝ} (hx : 0 < x) (a : ℝ) :
    ((c : ℝ≥0∞) * ENNReal.ofReal (x ^ (2 * a))) ^ (2⁻¹ : ℝ) =
      ((c ^ (2⁻¹ : ℝ) : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (x ^ a) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.coe_rpow_of_nonneg _ (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_mul hx.le]
  congr 3
  ring

/-- **The bilinear frequency-localized Strichartz estimate for the half-wave propagator.** Let
`E` have dimension `n`, let `Pⱼ` be the `L²` Fourier multiplier with the Littlewood–Paley
cutoff `ψⱼ` built from `φ`, and let `(q, r)` be a wave-admissible pair with `2 < q < ∞`:
`r ≥ 2` and `1 / q + (n - 1) / (2 r) ≤ (n - 1) / 4`, with `p` and `r'` the Hölder conjugates of
`q` and `r`. There is `C` such that for every `j ∈ ℤ` and all almost everywhere strongly
measurable `F, G : ℝ → L²(E)`,

`∫∫ |⟪W(t - s) Pⱼ² F(s), G(t)⟫| ds dt ≤ C 2^{2 j σ} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`,

where `σ = n / 2 - n / r - 1 / q`. Since the integrand is the absolute value of the Duhamel
pairing, the bound also controls the integral over any part of the `(s, t)` plane, such as the
retarded region `s < t`. -/
theorem exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_fourierMultiplierCLM_le
    (hr : 2 ≤ r) (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 1 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal / 2 ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 4) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
        AEStronglyMeasurable G →
        ∫⁻ t, ∫⁻ s, ‖⟪halfWavePropagator ℂ (t - s)
          (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨c, hc⟩ := φ.exists_eLpNorm_halfWavePropagator_comp_apply_adjoint_apply_le
    (r' := r') hr hqr
  obtain ⟨C, hC⟩ := exists_lintegral_lintegral_enorm_inner_adjoint_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq
    hpq
  refine ⟨C * c, fun j m hm F G hF hG ↦ ?_⟩
  -- The Duhamel pairing `⟪W(t - s) Pⱼ² F(s), G(t)⟫` is the time pairing `⟪U(t)* G(t), U(s)* F(s)⟫`
  -- of `U(t) = W(t) Pⱼ`, up to complex conjugation.
  have hpair (s t : ℝ) : ‖⟪halfWavePropagator ℂ (t - s)
      (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ =
      ‖⟪((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) (G t),
        ((halfWavePropagator ℂ s ∘L Lp.fourierMultiplierCLM ℂ m)†) (F s)⟫_ℂ‖ₑ := by
    rw [ContinuousLinearMap.adjoint_inner_left,
      halfWavePropagator_comp_apply_adjoint_apply hm, ← ofReal_norm, ← ofReal_norm,
      norm_inner_symm]
  simp_rw [hpair]
  calc _ ≤ _ := hC (fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m) _
        (fun s t hst g ↦ hc j m hm s t hst g) G F hG hF
    _ = _ := by
        rw [ENNReal.coe_mul]
        ring

/-- **The dual frequency-localized Strichartz estimate for the half-wave propagator.** Let `E`
have dimension `n`, let `Pⱼ` be the `L²` Fourier multiplier with the Littlewood–Paley cutoff
`ψⱼ` built from `φ`, and let `(q, r)` be a wave-admissible pair with `2 < q < ∞`: `r ≥ 2` and
`1 / q + (n - 1) / (2 r) ≤ (n - 1) / 4`, with `p` and `r'` the Hölder conjugates of `q` and `r`.
There is `C` such that for every `j ∈ ℤ` and every almost everywhere strongly measurable
`F : ℝ → L²(E)` for which `s ↦ Pⱼ W(-s) F(s)` is integrable,

`‖∫ Pⱼ W(-s) F(s) ds‖₂ ≤ C 2^{j σ} ‖F‖_{L^p_t L^{r'}_x}`,  `σ = n / 2 - n / r - 1 / q`. -/
theorem exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le (hr : 2 ≤ r)
    (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 1 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal / 2 ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 4) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
        Integrable (fun s ↦ Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ (-s) (F s))) →
        ‖∫ s, Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ (-s) (F s))‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 1 / q)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume := by
  obtain ⟨c, hc⟩ := φ.exists_eLpNorm_halfWavePropagator_comp_apply_adjoint_apply_le
    (r' := r') hr hqr
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq
    hpq
  refine ⟨C * c ^ (2⁻¹ : ℝ), fun j m hm F hF hPF ↦ ?_⟩
  have h := hC (fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m) _
    (fun s t hst g ↦ hc j m hm s t hst g) F hF
    (by simpa only [adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply hm] using hPF)
  simp only [adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply hm] at h
  refine h.trans_eq ?_
  rw [coe_mul_ofReal_rpow_rpow_inv_two c (zpow_pos two_pos j), ENNReal.coe_mul]
  ring

/-- **The frequency-localized Strichartz estimate for the half-wave propagator**, in weak form.
Let `E` have dimension `n`, let `Pⱼ` be the `L²` Fourier multiplier with the Littlewood–Paley
cutoff `ψⱼ` built from `φ`, and let `(q, r)` be a wave-admissible pair with `2 < q < ∞`: `r ≥ 2`
and `1 / q + (n - 1) / (2 r) ≤ (n - 1) / 4`, with `p` and `r'` the Hölder conjugates of `q` and
`r`. There is `C` such that for every `j ∈ ℤ`, every `f ∈ L²(E)` and every almost everywhere
strongly measurable `G : ℝ → L²(E)` for which `t ↦ Pⱼ W(-t) G(t)` is integrable,

`|∫ ⟪W(t) Pⱼ f, G(t)⟫ dt| ≤ C 2^{j σ} ‖f‖₂ ‖G‖_{L^p_t L^{r'}_x}`,  `σ = n / 2 - n / r - 1 / q`.

This is `‖W(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{j σ} ‖f‖₂` tested against `G`. -/
theorem exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le (hr : 2 ≤ r)
    (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 1 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal / 2 ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 4) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (f : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)),
        AEStronglyMeasurable G →
        Integrable (fun t ↦ Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ (-t) (G t))) →
        ‖∫ t, ⟪halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f), G t⟫_ℂ‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 1 / q)) * ‖f‖ₑ *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨c, hc⟩ := φ.exists_eLpNorm_halfWavePropagator_comp_apply_adjoint_apply_le
    (r' := r') hr hqr
  obtain ⟨C, hC⟩ := exists_enorm_integral_inner_apply_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq
    hpq
  refine ⟨C * c ^ (2⁻¹ : ℝ), fun j m hm f G hG hPG ↦ ?_⟩
  have h := hC (fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m) _
    (fun s t hst g ↦ hc j m hm s t hst g) f G hG
    (by simpa only [adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply hm] using hPG)
  simp only [ContinuousLinearMap.comp_apply] at h
  refine h.trans_eq ?_
  rw [coe_mul_ofReal_rpow_rpow_inv_two c (zpow_pos two_pos j), ENNReal.coe_mul]
  ring

end Strichartz

end ContDiffBump

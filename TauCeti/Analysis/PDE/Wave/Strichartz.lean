/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Strichartz.TTStar
public import TauCeti.Analysis.PDE.Wave.Dispersive
import TauCeti.Analysis.Convolution.Young
import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.MeasureTheory.Function.Lp.Star
import TauCeti.MeasureTheory.Integral.RieszThorin

/-!
# Frequency-localized Strichartz estimates for the half-wave propagator

Let `E` have dimension `n`, let `W₊(t) = exp(itD)`, `D = √(-Δ)`, be the half-wave propagator
(`TauCeti.halfWavePropagator`), and let `Pⱼ` be the `L²` Fourier multiplier with the
Littlewood–Paley cutoff `ψⱼ`, supported where `‖ξ‖ ≈ 2^j`. The frequency-localized propagators
`W₊(t) Pⱼ` disperse at the rate `σ = (n - 1)/2`,

`‖W₊(t) Pⱼ f‖_∞ ≤ C 2^{jn} (1 + 2^j |t|)^(-σ) ‖f‖₁`

(`ContDiffBump.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le`), and
this file feeds that decay to the `TT*` argument of `TauCeti.Analysis.PDE.Strichartz.TTStar`. For a
pair `(q, r)` on the sharp wave-admissible line

`2 / q + (n - 1) / r = (n - 1) / 2`, `2 < q < ∞`,

it gives, uniformly in `j ∈ ℤ`, the homogeneous estimate

`‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{j s(q, r)} ‖f‖₂`, `s(q, r) = n/2 - n/r - 1/q`,

in weak form, its dual form, and the bilinear and retarded bounds on the Duhamel pairings of
`W₊(t - s) Pⱼ²`, with the factor `2^{2 j s(q, r)}`. The exponent `s(q, r)` is the scaling-critical
regularity: on the sharp line it equals `(n + 1)/2 · (1/2 - 1/r)`. The admissibility condition
forces `n ≥ 2`, since the line `2 / q = 0` contains no finite `q`; in dimension one the half-wave
propagator is a translation and does not disperse.

## The argument

The time pairings of the family `U(t) = W₊(t) Pⱼ` are `U(s) U(t)* = W₊(s - t) Pⱼ²`, since `Pⱼ` is
self-adjoint and commutes with `W₊`. The multiplier `Pⱼ` is convolution with the kernel `𝓕⁻ ψⱼ`,
whose `L¹` norm does not depend on `j` because `ψⱼ` is `ψ₀` rescaled, so by Young's inequality
`Pⱼ` is bounded on `L¹` uniformly in `j`. With the dispersive estimate for `W₊(τ) Pⱼ` and
`(1 + 2^j |τ|)^(-σ) ≤ (2^j |τ|)^(-σ)` this gives

`‖W₊(τ) Pⱼ² g‖_∞ ≤ C 2^{j (n + 1)/2} |τ|^(-σ) ‖g‖₁`,

and the Riesz–Thorin theorem interpolates it with the bound `‖W₊(τ) Pⱼ²‖_{L² → L²} ≤ 1`:

`‖W₊(τ) Pⱼ² g‖_r ≤ C 2^{2 j s(q, r)} |τ|^(-2/q) ‖g‖_{r'}`,

where `σ (1 - 2/r) = 2/q` is exactly the admissibility condition. The `TT*` argument turns this
decay into the estimates above.

Summing the frequency-localized estimates over `j` to reach data in the homogeneous Sobolev space
of order `s(q, r)`, the non-sharp pairs, the endpoint `q = 2` and the inhomogeneous estimates for
different pairs are not treated here.

## Main declarations

* `ContDiffBump.exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le`: the dual
  estimate `‖∫ Pⱼ W₊(-s) F(s) ds‖₂ ≤ C 2^{j s(q, r)} ‖F‖_{L^{q'}_t L^{r'}_x}`.
* `ContDiffBump.exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le`: the
  homogeneous estimate `‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{j s(q, r)} ‖f‖₂`, in weak form.
* `ContDiffBump.exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_le`: the bilinear
  estimate for the Duhamel pairings `⟪W₊(t - s) Pⱼ² F(s), G(t)⟫`.
* `ContDiffBump.exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_le`: the
  retarded estimate, in weak form.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3 (Theorem 2.6 and its proof).
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace InnerProduct FourierTransform ContDiff SchwartzMap
  Convolution

namespace ContDiffBump

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (φ : ContDiffBump (0 : E))

/-! ### The multiplier `Pⱼ` -/

/-- **`Pⱼ` is bounded on `L¹`, uniformly in `j`.** It is convolution with `𝓕⁻ ψⱼ`, and
`‖𝓕⁻ ψⱼ‖₁ = ‖𝓕⁻ ψ₀‖₁` because `ψⱼ` is `ψ₀` rescaled. -/
private theorem exists_eLpNorm_fourierMultiplierCLM_one_le :
    ∃ K : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ g : Lp ℂ 2 (volume : Measure E),
      eLpNorm (Lp.fourierMultiplierCLM ℂ m g) 1 volume ≤ K * eLpNorm g 1 volume := by
  -- The cutoffs `ψᵢ` as complex Schwartz functions.
  set ψ : ℤ → 𝓢(E, ℂ) := fun i ↦
    φ.littlewoodPaleyPiece (m := fun _ : E ↦ (1 : ℂ)) contDiffOn_const i
  have hψ (i : ℤ) (ξ : E) : ψ i ξ = φ.littlewoodPaley i ξ := by
    simp [ψ, Complex.real_smul]
  refine ⟨(∫ x, ‖𝓕⁻ (ψ 0 : E → ℂ) x‖).toNNReal, fun j m hm g ↦ ?_⟩
  set σ := ψ j
  have hmσ : m = σ.toLp ∞ := by
    apply Lp.ext
    filter_upwards [hm, σ.coeFn_toLp ∞] with ξ h₁ h₂
    rw [h₁, h₂, hψ]
  -- `𝓕⁻ ψⱼ` has the same `L¹` norm as `𝓕⁻ ψ₀`.
  have hscale : ∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖ = ∫ x, ‖𝓕⁻ (ψ 0 : E → ℂ) x‖ := by
    have hσ : (σ : E → ℂ) = fun ξ ↦ (ψ 0 : E → ℂ) (((2 : ℝ) ^ j)⁻¹ • ξ) := by
      funext ξ
      rw [hψ, hψ, littlewoodPaley_apply_eq_littlewoodPaley_zero_apply φ j ξ]
    rw [hσ]
    exact integral_norm_fourierInv_comp_smul _ (inv_ne_zero (zpow_ne_zero j two_ne_zero))
  have hK : AEStronglyMeasurable (𝓕⁻ (σ : E → ℂ)) volume := by
    rw [← SchwartzMap.fourierInv_coe]
    exact (𝓕⁻ σ).continuous.aestronglyMeasurable
  have hKi : Integrable (𝓕⁻ (σ : E → ℂ)) volume := by
    rw [← SchwartzMap.fourierInv_coe]
    exact (𝓕⁻ σ).integrable
  have hconv : Lp.fourierMultiplierCLM ℂ m g =ᵐ[volume]
      𝓕⁻ (σ : E → ℂ) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] (g : E → ℂ) := by
    filter_upwards [hmσ ▸ σ.coeFn_fourierMultiplierCLM_toLp g] with x hx
    rw [hx, convolution_lsmul_swap, SchwartzMap.fourierInv_coe]
  have hL : ‖ContinuousLinearMap.lsmul ℂ ℂ (E := ℂ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 ContinuousLinearMap.opNorm_lsmul_le
  calc eLpNorm (Lp.fourierMultiplierCLM ℂ m g) 1 volume
      = eLpNorm (𝓕⁻ (σ : E → ℂ) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] (g : E → ℂ)) 1
          volume := eLpNorm_congr_ae hconv
    _ ≤ ‖ContinuousLinearMap.lsmul ℂ ℂ (E := ℂ)‖ₑ * eLpNorm (𝓕⁻ (σ : E → ℂ)) 1 volume *
          eLpNorm g 1 volume :=
        eLpNorm_convolution_le_of_inv_add_inv_eq _ le_rfl le_rfl (by simp) hK
          (Lp.aestronglyMeasurable g)
    _ ≤ eLpNorm (𝓕⁻ (σ : E → ℂ)) 1 volume * eLpNorm g 1 volume := by
        rw [mul_assoc]
        exact mul_le_of_le_one_left zero_le hL
    _ = _ := by
        rw [eLpNorm_one_eq_lintegral_eNorm, ← ofReal_integral_norm_eq_lintegral_eNorm hKi,
          hscale, ENNReal.ofReal]
        exact hK

/-- In dimension `0` the space is a point, where `ψⱼ` vanishes, so `Pⱼ = 0`. -/
private theorem fourierMultiplierCLM_eq_zero_of_finrank_eq_zero (hE : Module.finrank ℝ E = 0)
    {j : ℤ} {m : Lp ℂ ∞ (volume : Measure E)}
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) :
    Lp.fourierMultiplierCLM ℂ m = 0 := by
  have : Subsingleton E := Module.finrank_zero_iff.1 hE
  have hm0 : m =ᵐ[volume] fun _ ↦ (0 : ℂ) := by
    filter_upwards [hm] with ξ h
    rw [h, Subsingleton.elim ξ 0, φ.littlewoodPaley_eq_zero_of_norm_le (by
      rw [norm_zero]; exact (mul_pos (zpow_pos two_pos _) φ.rIn_pos).le), Complex.ofReal_zero]
  rw [Lp.fourierMultiplierCLM_of_ae_eq_const hm0]
  ext1 f
  simp

/-! ### The dispersive estimate for the time pairings -/

/-- **The dispersive estimate for `W₊(t) Pⱼ²`.** In dimension `n ≥ 1` there is `C ≥ 0` such that
for every `j`, every time `t ≠ 0` and every integrable `g ∈ L²`,
`‖W₊(t) Pⱼ² g‖_∞ ≤ C 2^{j (n + 1)/2} |t|^(-(n - 1)/2) ‖g‖₁`. -/
private theorem exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_sq_le
    (hE : Module.finrank ℝ E ≠ 0) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ t : ℝ, t ≠ 0 →
      ∀ g : Lp ℂ 2 (volume : Measure E), Integrable g →
      eLpNorm (halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m
          (Lp.fourierMultiplierCLM ℂ m g))) ∞ volume ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) + 1) / 2) *
          |t| ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)) * eLpNorm g 1 volume := by
  obtain ⟨C, hC0, hC⟩ :=
    φ.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le (F := ℂ)
  obtain ⟨K, hK⟩ := φ.exists_eLpNorm_fourierMultiplierCLM_one_le
  refine ⟨C.toNNReal * K, fun j m hm t ht g hg ↦ ?_⟩
  set n : ℝ := ((Module.finrank ℝ E : ℕ) : ℝ) with hn_def
  set Pg := Lp.fourierMultiplierCLM ℂ m g
  have h2 : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  have hn1 : 1 ≤ n := by
    rw [hn_def]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hE
  have hPg : eLpNorm Pg 1 volume ≤ K * eLpNorm g 1 volume := hK j m hm g
  have hPgi : Integrable Pg := memLp_one_iff_integrable.1
    (hPg.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (memLp_one_iff_integrable.2 hg)))
  -- Since `n ≥ 1`, `(1 + 2^j |t|)^(-(n - 1)/2) ≤ (2^j |t|)^(-(n - 1)/2)`.
  have hdecay : ((2 : ℝ) ^ j) ^ (n : ℝ) * (1 + 2 ^ j * |t|) ^ (-(n - 1) / 2) ≤
      ((2 : ℝ) ^ j) ^ ((n + 1) / 2) * |t| ^ (-(n - 1) / 2) := by
    have hpos : 0 < 2 ^ j * |t| := mul_pos h2 (abs_pos.2 ht)
    calc ((2 : ℝ) ^ j) ^ (n : ℝ) * (1 + 2 ^ j * |t|) ^ (-(n - 1) / 2)
        ≤ ((2 : ℝ) ^ j) ^ (n : ℝ) * (2 ^ j * |t|) ^ (-(n - 1) / 2) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos ?_ ?_) (by positivity)
          · linarith
          · linarith
      _ = ((2 : ℝ) ^ j) ^ ((n + 1) / 2) * |t| ^ (-(n - 1) / 2) := by
          rw [Real.mul_rpow h2.le (abs_nonneg t), ← mul_assoc, ← Real.rpow_add h2]
          congr 2
          ring
  calc eLpNorm (halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m Pg)) ∞ volume
      ≤ ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
          (1 + 2 ^ j * |t|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)) * eLpNorm Pg 1 volume :=
        hC j m hm t Pg hPgi
    _ ≤ ENNReal.ofReal (C * (((2 : ℝ) ^ j) ^ ((n + 1) / 2) * |t| ^ (-(n - 1) / 2))) *
          (K * eLpNorm g 1 volume) := by
        gcongr ENNReal.ofReal ?_ * ?_
        rw [mul_assoc, ← Real.rpow_natCast]
        exact mul_le_mul_of_nonneg_left hdecay hC0
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_coe_nnreal (p := K),
          ← ENNReal.ofReal_mul (mul_nonneg hC0 (by positivity))]
        congr 2
        push_cast [Real.coe_toNNReal _ hC0]
        ring

/-- `Pⱼ` is self-adjoint, so `(W₊(t) Pⱼ)* = Pⱼ W₊(-t)`. -/
private theorem adjoint_halfWavePropagator_comp_fourierMultiplierCLM {j : ℤ}
    {m : Lp ℂ ∞ (volume : Measure E)} (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    (t : ℝ) :
    (halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)† =
      Lp.fourierMultiplierCLM ℂ m ∘L halfWavePropagator ℂ (-t) := by
  rw [ContinuousLinearMap.adjoint_comp, Lp.adjoint_fourierMultiplierCLM,
    Lp.star_eq_self_of_ae_eq_ofReal hm, halfWavePropagator_def, adjoint_phasePropagator]

/-- The time pairings of `U(t) = W₊(t) Pⱼ` are `U(s) U(t)* = W₊(s - t) Pⱼ²`. -/
private theorem halfWavePropagator_comp_apply_adjoint {j : ℤ}
    {m : Lp ℂ ∞ (volume : Measure E)} (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    (s t : ℝ) (g : Lp ℂ 2 (volume : Measure E)) :
    (halfWavePropagator ℂ s ∘L Lp.fourierMultiplierCLM ℂ m)
        (((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) g) =
      halfWavePropagator ℂ (s - t)
        (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m g)) := by
  have hc (τ : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
      Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ τ x) =
        halfWavePropagator ℂ τ (Lp.fourierMultiplierCLM ℂ m x) :=
    (DFunLike.congr_fun (phasePropagator_comp_fourierMultiplierCLM _ τ m) x).symm
  simp only [φ.adjoint_halfWavePropagator_comp_fourierMultiplierCLM hm,
    ContinuousLinearMap.comp_apply]
  rw [hc, hc, halfWavePropagator_def, halfWavePropagator_def, ← phasePropagator_add_apply,
    ← sub_eq_add_neg]

/-! ### Strichartz estimates at the sharp wave-admissible pairs -/

section Admissible

variable {p q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- `|ψⱼ| ≤ 1`, so `‖Pⱼ‖ ≤ 1`. -/
private theorem norm_fourierMultiplierCLM_le_one {j : ℤ} {m : Lp ℂ ∞ (volume : Measure E)}
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) :
    ‖Lp.fourierMultiplierCLM (E := E) ℂ m‖ ≤ 1 := by
  refine (Lp.norm_fourierMultiplierCLM_le m).trans ?_
  rw [Lp.norm_def, eLpNorm_exponent_top]
  · refine ENNReal.toReal_le_of_le_ofReal zero_le_one (eLpNormEssSup_le_of_ae_bound ?_)
    filter_upwards [hm] with ξ h
    rw [h, Complex.norm_real, Real.norm_eq_abs]
    exact φ.abs_littlewoodPaley_le_one j ξ
  · exact Lp.aestronglyMeasurable m

/-- `‖W₊(τ) Pⱼ²‖_{L² → L²} ≤ 1`. -/
private theorem norm_halfWavePropagator_comp_le_one {j : ℤ} {m : Lp ℂ ∞ (volume : Measure E)}
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (τ : ℝ) :
    ‖halfWavePropagator ℂ τ ∘L (Lp.fourierMultiplierCLM ℂ m ∘L Lp.fourierMultiplierCLM ℂ m)‖ ≤
      1 := by
  have hm1 := φ.norm_fourierMultiplierCLM_le_one hm
  have hW := norm_phasePropagator_le (E := E) (F := ℂ) sqrtNegLaplacianSymbol τ
  have hmm := ContinuousLinearMap.opNorm_comp_le (Lp.fourierMultiplierCLM (E := E) ℂ m)
    (Lp.fourierMultiplierCLM ℂ m)
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  nlinarith [norm_nonneg (Lp.fourierMultiplierCLM (E := E) ℂ m),
    norm_nonneg (Lp.fourierMultiplierCLM (E := E) ℂ m ∘L Lp.fourierMultiplierCLM ℂ m),
    norm_nonneg (halfWavePropagator (E := E) ℂ τ)]

/-- **The `L^{r'} → L^r` dispersive estimate for `W₊(τ) Pⱼ²`.** Along a sharp wave-admissible
pair, `2 / q + (n - 1) / r = (n - 1) / 2` with `2 < q`, in dimension `n ≥ 1`,
`‖W₊(τ) Pⱼ² g‖_r ≤ K 2^{2 j s(q, r)} |τ| ^ (-2 / q) ‖g‖_{r'}` for `τ ≠ 0` and `g ∈ L² ∩ L^{r'}`,
where `s(q, r) = n/2 - n/r - 1/q`. This interpolates the `L¹ → L^∞` bound with the `L²` bound. -/
private theorem exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_sq_le_of_memLp
    (hq : 2 < q) (hE : Module.finrank ℝ E ≠ 0)
    (hqr : 2 / (q : ℝ) + (Module.finrank ℝ E - 1) * (r⁻¹).toReal =
      (Module.finrank ℝ E - 1) / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ τ : ℝ, τ ≠ 0 →
      ∀ g : Lp ℂ 2 (volume : Measure E), MemLp g r' volume →
      eLpNorm (halfWavePropagator ℂ τ (Lp.fourierMultiplierCLM ℂ m
          (Lp.fourierMultiplierCLM ℂ m g))) r volume ≤
        ENNReal.ofReal (K * ((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) * ‖τ‖ₑ ^ (-(2 / q : ℝ)) *
          eLpNorm g r' volume := by
  set n : ℝ := ((Module.finrank ℝ E : ℕ) : ℝ)
  set ρ := (r⁻¹).toReal
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_sq_le hE
  -- The constant `C + 1 > 0` keeps `K` positive.
  refine ⟨((C : ℝ) + 1) ^ (1 - 2 * ρ), by positivity, fun j m hm τ hτ0 g hg ↦ ?_⟩
  -- Admissibility with `2 < q` and `n ≥ 1` forces `1 / r < 1 / 2`, so `2 ≤ r`.
  have hρ : ρ < 2⁻¹ := by
    have hq0 : (0 : ℝ) < 2 / q := div_pos two_pos (by exact_mod_cast zero_lt_two.trans hq)
    have hn1 : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hE
    nlinarith
  have hr : 2 ≤ r := by
    rw [← ENNReal.inv_le_inv,
      ← ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 (ENNReal.HolderConjugate.ne_zero r r')),
      ← ENNReal.ofReal_toReal (a := 2⁻¹) (by simp)]
    exact ENNReal.ofReal_le_ofReal (hρ.le.trans_eq (by simp))
  have hτ : 0 < |τ| := abs_pos.2 hτ0
  have h2 : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  set B : ℝ := (C + 1) * ((2 : ℝ) ^ j) ^ ((n + 1) / 2) * |τ| ^ (-(n - 1) / 2)
  have hB : 0 ≤ B := by positivity
  have h₀ (f : Lp ℂ 2 (volume : Measure E)) (hf : Integrable f) :
      eLpNorm (halfWavePropagator ℂ τ (Lp.fourierMultiplierCLM ℂ m
        (Lp.fourierMultiplierCLM ℂ m f))) ∞ volume ≤ B.toNNReal * eLpNorm f 1 volume := by
    refine (hC j m hm τ hτ0 f hf).trans ?_
    rw [ENNReal.ofNNReal_toNNReal]
    gcongr ENNReal.ofReal ?_ * _
    simp only [B, n]
    gcongr
    linarith
  refine ((halfWavePropagator ℂ τ ∘L (Lp.fourierMultiplierCLM ℂ m ∘L
      Lp.fourierMultiplierCLM ℂ m)).eLpNorm_apply_le_rpow_mul_rpow_mul_eLpNorm (M₀ := B.toNNReal)
    (M₁ := 1) (p := r') (q := r) h₀ (φ.norm_halfWavePropagator_comp_le_one hm τ) hr g hg).trans_eq
    ?_
  -- `B^(1 - 2/r) = K 2^{2 j s(q, r)} |τ|^(-2/q)` on the admissible line.
  have hexp₁ : (n + 1) / 2 * (1 - 2 * ρ) = 2 * (n / 2 - n * ρ - 1 / q) := by
    linear_combination hqr
  have hexp₂ : -(n - 1) / 2 * (1 - 2 * ρ) = -(2 / q : ℝ) := by
    linear_combination hqr
  rw [NNReal.one_rpow, mul_one, ← Real.toNNReal_rpow_of_nonneg hB, ENNReal.ofNNReal_toNNReal,
    ← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_pos hτ,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul h2.le, ← Real.rpow_mul (abs_nonneg _), hexp₁, hexp₂]

/-- **Decay of the time pairings.** Along a sharp wave-admissible pair,
`2 / q + (n - 1) / r = (n - 1) / 2` with `2 < q`, the time pairings `W₊(s - t) Pⱼ²` of
`U(t) = W₊(t) Pⱼ` decay from `L^{r'}` to `L^r` like `|s - t| ^ (-2 / q)`, with the factor
`2^{2 j s(q, r)}`, `s(q, r) = n/2 - n/r - 1/q`. This is the hypothesis of the `TT*` argument. -/
private theorem exists_eLpNorm_halfWavePropagator_comp_adjoint_le (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + (Module.finrank ℝ E - 1) * (r⁻¹).toReal =
      (Module.finrank ℝ E - 1) / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ s t : ℝ, s ≠ t →
      ∀ g : Lp ℂ 2 (volume : Measure E),
      eLpNorm ((halfWavePropagator ℂ s ∘L Lp.fourierMultiplierCLM ℂ m)
          (((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) g)) r volume ≤
        ENNReal.ofReal (K * ((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) *
          eLpNorm g r' volume := by
  rcases eq_or_ne (Module.finrank ℝ E) 0 with hE | hE
  · -- In dimension `0`, `Pⱼ = 0`.
    refine ⟨0, le_rfl, fun j m hm s t _ g ↦ ?_⟩
    rw [φ.halfWavePropagator_comp_apply_adjoint hm,
      φ.fourierMultiplierCLM_eq_zero_of_finrank_eq_zero hE hm]
    simp only [zero_apply, map_zero]
    rw [eLpNorm_congr_ae (Lp.coeFn_zero _ _ _), eLpNorm_zero]
    exact zero_le
  obtain ⟨K, hK, hKb⟩ :=
    φ.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_sq_le_of_memLp (r' := r') hq hE hqr
  refine ⟨K, hK.le, fun j m hm s t hst g ↦ ?_⟩
  rw [φ.halfWavePropagator_comp_apply_adjoint hm]
  by_cases hg : MemLp g r' volume
  · exact hKb j m hm (s - t) (sub_ne_zero.2 hst) g hg
  -- Off `L^{r'}` the right-hand side is infinite.
  have hA : ENNReal.ofReal (K * ((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
      Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) ≠ 0 :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne'
      (ENNReal.rpow_pos (eNorm_pos.2 (sub_ne_zero.2 hst)) eNorm_ne_top).ne').ne'
  rw [top_unique (not_lt.1 (memLp_iff.not.1 hg)), ENNReal.mul_top hA]
  exact le_top

/-- **The dual frequency-localized Strichartz estimate for the half-wave propagator.** Let `E`
have dimension `n`, let `(q, r)` be a sharp wave-admissible pair, `2 / q + (n - 1) / r = (n - 1)/2`
with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates of `q` and `r`, and let
`s(q, r) = n/2 - n/r - 1/q`. There is `C` such that for every `j ∈ ℤ`, every symbol `m` of `Pⱼ` and
every almost everywhere strongly measurable `F : ℝ → L²(E)`,

`‖∫ Pⱼ W₊(-s) F(s) ds‖₂ ≤ C 2^{j s(q, r)} ‖F‖_{L^p_t L^{r'}_x}`. -/
theorem exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + (Module.finrank ℝ E - 1) * (r⁻¹).toReal =
      (Module.finrank ℝ E - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      ‖∫ s, Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ (-s) (F s))‖ₑ ≤
        C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q)) *
          eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume := by
  obtain ⟨K, hK0, hK⟩ := φ.exists_eLpNorm_halfWavePropagator_comp_adjoint_le (r' := r') hq hqr
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le (𝕜 := ℂ) (H := Lp ℂ 2 (volume : Measure E))
    (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq hpq
  refine ⟨C * (K ^ (2⁻¹ : ℝ)).toNNReal, fun j m hm F hF ↦ ?_⟩
  -- Without integrability the integral is `0`.
  by_cases hPF : Integrable (fun s ↦ Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ (-s) (F s)))
  swap
  · rw [integral_undef hPF, eNorm_zero]
    exact zero_le
  have h := hC (fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m) _ (hK j m hm) F
    hF (by simpa only [φ.adjoint_halfWavePropagator_comp_fourierMultiplierCLM hm,
      ContinuousLinearMap.comp_apply] using hPF)
  simp only [φ.adjoint_halfWavePropagator_comp_fourierMultiplierCLM hm,
    ContinuousLinearMap.comp_apply] at h
  refine h.trans_eq ?_
  -- `(K 2^{2 j s(q, r)})^{1/2} = K^{1/2} 2^{j s(q, r)}`.
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    Real.mul_rpow hK0 (by positivity), ← Real.rpow_mul (zpow_pos two_pos j).le, mul_right_comm 2,
    mul_inv_cancel₀ two_ne_zero, one_mul, ENNReal.ofReal_mul (by positivity), ENNReal.coe_mul,
    ENNReal.ofNNReal_toNNReal]
  ring

/-- **The frequency-localized Strichartz estimate for the half-wave propagator**, in weak form.
Let `E` have dimension `n`, let `(q, r)` be a sharp wave-admissible pair,
`2 / q + (n - 1) / r = (n - 1) / 2` with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates
of `q` and `r`, and let `s(q, r) = n/2 - n/r - 1/q`. There is `C` such that for every `j ∈ ℤ`, every
symbol `m` of `Pⱼ`, every `f ∈ L²(E)` and every almost everywhere strongly measurable
`G : ℝ → L²(E)` for which `t ↦ Pⱼ W₊(-t) G(t)` is integrable,

`|∫ ⟪W₊(t) Pⱼ f, G(t)⟫ dt| ≤ C 2^{j s(q, r)} ‖f‖₂ ‖G‖_{L^p_t L^{r'}_x}`.

This is `‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{j s(q, r)} ‖f‖₂` tested against `G`. -/
theorem exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + (Module.finrank ℝ E - 1) * (r⁻¹).toReal =
      (Module.finrank ℝ E - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (f : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)),
      AEStronglyMeasurable G →
      Integrable (fun t ↦ Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ (-t) (G t))) →
      ‖∫ t, ⟪halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f), G t⟫_ℂ‖ₑ ≤
        C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q)) * ‖f‖ₑ *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨K, hK0, hK⟩ := φ.exists_eLpNorm_halfWavePropagator_comp_adjoint_le (r' := r') hq hqr
  obtain ⟨C, hC⟩ := exists_enorm_integral_inner_apply_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq hpq
  refine ⟨C * (K ^ (2⁻¹ : ℝ)).toNNReal, fun j m hm f G hG hPG ↦ ?_⟩
  have h := hC (fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m) _ (hK j m hm) f G
    hG (by simpa only [φ.adjoint_halfWavePropagator_comp_fourierMultiplierCLM hm,
      ContinuousLinearMap.comp_apply] using hPG)
  simp only [ContinuousLinearMap.comp_apply] at h
  refine h.trans_eq ?_
  -- `(K 2^{2 j s(q, r)})^{1/2} = K^{1/2} 2^{j s(q, r)}`.
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    Real.mul_rpow hK0 (by positivity), ← Real.rpow_mul (zpow_pos two_pos j).le, mul_right_comm 2,
    mul_inv_cancel₀ two_ne_zero, one_mul, ENNReal.ofReal_mul (by positivity), ENNReal.coe_mul,
    ENNReal.ofNNReal_toNNReal]
  ring

/-- **The bilinear frequency-localized Strichartz estimate for the half-wave propagator.** Let
`E` have dimension `n`, let `(q, r)` be a sharp wave-admissible pair,
`2 / q + (n - 1) / r = (n - 1) / 2` with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates
of `q` and `r`, and let `s(q, r) = n/2 - n/r - 1/q`. There is `C` such that for every `j ∈ ℤ`, every
symbol `m` of `Pⱼ` and all almost everywhere strongly measurable `F, G : ℝ → L²(E)`,

`∫∫ |⟪W₊(t - s) Pⱼ² F(s), G(t)⟫| ds dt ≤
  C 2^{2 j s(q, r)} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

Since the integrand is the absolute value of the Duhamel pairing, the bound also controls the
integral over any part of the `(s, t)` plane, such as the retarded region `s < t`
(`ContDiffBump.exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_le`). -/
theorem exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + (Module.finrank ℝ E - 1) * (r⁻¹).toReal =
      (Module.finrank ℝ E - 1) / 2) :
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
  obtain ⟨K, hK0, hK⟩ := φ.exists_eLpNorm_halfWavePropagator_comp_adjoint_le (r' := r') hq hqr
  obtain ⟨C, hC⟩ := exists_lintegral_lintegral_enorm_inner_adjoint_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq
    hpq
  refine ⟨C * K.toNNReal, fun j m hm F G hF hG ↦ ?_⟩
  set U : ℝ → Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
    fun t ↦ halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m
  -- The Duhamel pairing `⟪W₊(t - s) Pⱼ² F(s), G(t)⟫` is the time pairing
  -- `⟪U(t)* G(t), U(s)* F(s)⟫` up to complex conjugation.
  have hpair (s t : ℝ) : ‖⟪halfWavePropagator ℂ (t - s)
      (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ =
      ‖⟪((U t)†) (G t), ((U s)†) (F s)⟫_ℂ‖ₑ := by
    rw [ContinuousLinearMap.adjoint_inner_left, φ.halfWavePropagator_comp_apply_adjoint hm,
      ← ofReal_norm, ← ofReal_norm, norm_inner_symm]
  simp_rw [hpair]
  calc _ ≤ _ := hC U _ (hK j m hm) G F hG hF
    _ = _ := by
        rw [ENNReal.ofReal_mul hK0, ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal]
        ring

/-- **The retarded frequency-localized Strichartz estimate for the half-wave propagator**, in
weak form. Let `E` have dimension `n`, let `(q, r)` be a sharp wave-admissible pair,
`2 / q + (n - 1) / r = (n - 1) / 2` with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates
of `q` and `r`, and let `s(q, r) = n/2 - n/r - 1/q`. There is `C` such that for every `j ∈ ℤ`, every
symbol `m` of `Pⱼ` and all almost everywhere strongly measurable `F, G : ℝ → L²(E)`,

`|∫ ∫_{s < t} ⟪W₊(t - s) Pⱼ² F(s), G(t)⟫ ds dt| ≤
  C 2^{2 j s(q, r)} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

This is the Duhamel estimate
`‖∫_{s < t} W₊(t - s) Pⱼ² F(s) ds‖_{L^q_t L^r_x} ≤ C 2^{2 j s(q, r)} ‖F‖_{L^p_t L^{r'}_x}` tested
against `G`. -/
theorem exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + (Module.finrank ℝ E - 1) * (r⁻¹).toReal =
      (Module.finrank ℝ E - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      AEStronglyMeasurable G →
      ‖∫ t, ∫ s in Set.Iio t, ⟪halfWavePropagator ℂ (t - s)
          (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ ≤
        C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) *
          eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C, hC⟩ :=
    φ.exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_le (r' := r') hq hpq hqr
  refine ⟨C, fun j m hm F G hF hG ↦ ?_⟩
  calc _ ≤ ∫⁻ t, ‖∫ s in Set.Iio t, ⟪halfWavePropagator ℂ (t - s)
          (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ :=
        eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ t, ∫⁻ s in Set.Iio t, ‖⟪halfWavePropagator ℂ (t - s)
          (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ :=
        lintegral_mono fun t ↦ eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ t, ∫⁻ s, ‖⟪halfWavePropagator ℂ (t - s)
          (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ :=
        lintegral_mono fun t ↦ setLIntegral_le_lintegral _ _
    _ ≤ _ := hC j m hm F G hF hG

end Admissible

end ContDiffBump

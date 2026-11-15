/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Strichartz.TTStar
public import TauCeti.Analysis.PDE.Wave.Dispersive
import TauCeti.Analysis.Fourier.LittlewoodPaley
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
wave-admissible pair `(q, r)`,

`2 / q + (n - 1) / r ≤ (n - 1) / 2`, `2 < q < ∞`,

it gives, uniformly in `j ∈ ℤ`, the homogeneous estimate

`‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{j s(q, r)} ‖f‖₂`, `s(q, r) = n/2 - n/r - 1/q`,

in weak form, its dual form, and the bilinear and retarded bounds on the Duhamel pairings of
`W₊(t - s) Pⱼ`, with the factor `2^{2 j s(q, r)}`. On the sharp line, where equality holds,
`s(q, r) = (n + 1)/2 · (1/2 - 1/r)`. For `n ≥ 1` the admissibility condition forces `n ≥ 2` and
`r > 2`, since for `n = 1` its right side vanishes; in dimension one the half-wave propagator is a
translation and does not disperse. In dimension `0` the condition admits pairs with `r < 2`, but
there `Pⱼ = 0` and the estimates hold trivially.

## The argument

For `2 ≤ r ≤ ∞` the Riesz–Thorin theorem interpolates the dispersive estimate with the bound
`‖W₊(τ) Pⱼ‖_{L² → L²} ≤ 1`:

`‖W₊(τ) Pⱼ g‖_r ≤ (C 2^{jn} (1 + 2^j |τ|)^(-σ))^(1 - 2/r) ‖g‖_{r'}`

(`ContDiffBump.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_le`). For `n ≥ 1`,
`σ ≥ 0`, and admissibility says exactly `2/q ≤ σ (1 - 2/r)`. Since `(1 + x)^(-a) ≤ x^(-b)` for
`x > 0` and `0 ≤ b ≤ a`, this gives

`‖W₊(τ) Pⱼ g‖_r ≤ C 2^{2 j s(q, r)} |τ|^(-2/q) ‖g‖_{r'}`.

The Duhamel kernel `W₊(t - s) Pⱼ` therefore satisfies the hypothesis of the bilinear estimate
`TauCeti.exists_lintegral_lintegral_enorm_inner_le`. The time pairings of the family
`U(t) = W₊(t) Pⱼ` are `U(s) U(t)* = W₊(s - t) Pⱼ²`, since `Pⱼ` is self-adjoint and commutes with
`W₊`, and `Pⱼ` is bounded on `L^{r'}` uniformly in `j`
(`ContDiffBump.exists_eLpNorm_fourierMultiplierCLM_le`), so the `TT*` argument gives the dual and
homogeneous estimates.

Summing the frequency-localized estimates over `j` to reach data in the homogeneous Sobolev space
of order `s(q, r)`, the endpoint `q = 2` and the inhomogeneous estimates for different pairs are
not treated here.

## Main declarations

* `ContDiffBump.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_le`: the
  `L^{r'} → L^r` dispersive estimate for `W₊(t) Pⱼ`, `2 ≤ r ≤ ∞`.
* `ContDiffBump.exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le`: the dual
  estimate `‖∫ Pⱼ W₊(-s) F(s) ds‖₂ ≤ C 2^{j s(q, r)} ‖F‖_{L^{q'}_t L^{r'}_x}`.
* `ContDiffBump.exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le`: the
  homogeneous estimate `‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{j s(q, r)} ‖f‖₂`, in weak form.
* `ContDiffBump.exists_lintegral_lintegral_enorm_inner_halfWavePropagator_fourierMultiplierCLM_le`:
  the bilinear estimate for the Duhamel pairings `⟪W₊(t - s) Pⱼ F(s), G(t)⟫`.
* `ContDiffBump.exists_enorm_integral_setIntegral_inner_halfWavePropagator_fourierMultiplierCLM_le`:
  the retarded estimate over `s < t`, in weak form.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3 (Theorem 2.6 and its proof).
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace InnerProduct

namespace ContDiffBump

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (φ : ContDiffBump (0 : E))

/-! ### The time pairings -/

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

/-! ### The `L^{r'} → L^r` dispersive estimate -/

section Admissible

variable {p q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- `‖W₊(t) Pⱼ‖_{L² → L²} ≤ 1`. -/
private theorem norm_halfWavePropagator_comp_fourierMultiplierCLM_le_one {j : ℤ}
    {m : Lp ℂ ∞ (volume : Measure E)} (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ))
    (t : ℝ) : ‖halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul (norm_phasePropagator_le _ t)
    (φ.norm_fourierMultiplierCLM_le_one hm) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

/-- **The `L^{r'} → L^r` dispersive estimate for the frequency-localized half-wave propagator.**
Let `E` have dimension `n`, let `2 ≤ r ≤ ∞` with Hölder conjugate `r'`, and let `Pⱼ` be the `L²`
Fourier multiplier with symbol `ψⱼ`. There is `C ≥ 0` such that for every `j ∈ ℤ`, every time `t`
and every `g ∈ L²`,

`‖W₊(t) Pⱼ g‖_r ≤ (C 2^{jn} (1 + 2^j |t|)^(-(n - 1)/2))^(1 - 2/r) ‖g‖_{r'}`.

This is the Riesz–Thorin interpolation of the `L¹ → L^∞` estimate
`ContDiffBump.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le` with the
`L²` bound `‖W₊(t) Pⱼ‖ ≤ 1`. -/
theorem exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_le (hr : 2 ≤ r) :
    ∃ C, 0 ≤ C ∧ ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ (t : ℝ)
      (g : Lp ℂ 2 (volume : Measure E)),
      eLpNorm (halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m g)) r volume ≤
        ENNReal.ofReal ((C * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
          (1 + 2 ^ j * |t|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)) ^ (1 - 2 * (r⁻¹).toReal)) *
          eLpNorm g r' volume := by
  obtain ⟨C, hC0, hC⟩ :=
    φ.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le (F := ℂ)
  -- The constant `C + 1 > 0` makes the bound positive, so that it is `∞` off `L^{r'}`.
  refine ⟨C + 1, by positivity, fun j m hm t g ↦ ?_⟩
  by_cases hg : MemLp g r' volume
  swap
  · rw [top_unique (not_lt.1 (memLp_iff.not.1 hg)),
      ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
    exact le_top
  have hθ : 0 ≤ 1 - 2 * (r⁻¹).toReal := by
    have h := ENNReal.toReal_mono (by simp) (ENNReal.inv_le_inv.2 hr)
    have h2 : ((2 : ℝ≥0∞)⁻¹).toReal = 2⁻¹ := by norm_num [ENNReal.toReal_inv]
    linarith
  set B := C * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
    (1 + 2 ^ j * |t|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)
  have hB : 0 ≤ B := by positivity
  have h₀ (f : Lp ℂ 2 (volume : Measure E)) (hf : Integrable f) :
      eLpNorm ((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m) f) ∞ volume ≤
        B.toNNReal * eLpNorm f 1 volume := by
    rw [ENNReal.ofNNReal_toNNReal]
    exact hC j m hm t f hf
  refine ((halfWavePropagator ℂ t ∘L
      Lp.fourierMultiplierCLM ℂ m).eLpNorm_apply_le_rpow_mul_rpow_mul_eLpNorm (M₀ := B.toNNReal)
    (M₁ := 1) (p := r') (q := r) h₀
    (φ.norm_halfWavePropagator_comp_fourierMultiplierCLM_le_one hm t) hr g hg).trans ?_
  rw [NNReal.one_rpow, mul_one, ← Real.toNNReal_rpow_of_nonneg hB, ENNReal.ofNNReal_toNNReal]
  gcongr
  simp only [B]
  gcongr
  linarith

/-- **Decay along the wave-admissible pairs.** Along a wave-admissible pair,
`2 / q + (n - 1) / r ≤ (n - 1) / 2` with `2 < q`, `W₊(τ) Pⱼ` decays from `L^{r'}` to `L^r` like
`|τ| ^ (-2 / q)`: `‖W₊(τ) Pⱼ g‖_r ≤ K 2^{2 j s(q, r)} |τ| ^ (-2 / q) ‖g‖_{r'}` for `τ ≠ 0` and
`g ∈ L²`, where `s(q, r) = n/2 - n/r - 1/q`. -/
private theorem exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_le_rpow (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + (Module.finrank ℝ E - 1) * (r⁻¹).toReal ≤
      (Module.finrank ℝ E - 1) / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ τ : ℝ, τ ≠ 0 →
      ∀ g : Lp ℂ 2 (volume : Measure E),
      eLpNorm (halfWavePropagator ℂ τ (Lp.fourierMultiplierCLM ℂ m g)) r volume ≤
        ENNReal.ofReal (K * ((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) * ‖τ‖ₑ ^ (-(2 / q : ℝ)) *
          eLpNorm g r' volume := by
  rcases eq_or_ne (Module.finrank ℝ E) 0 with hE | hE
  · -- In dimension `0`, `Pⱼ = 0`.
    refine ⟨0, le_rfl, fun j m hm τ _ g ↦ ?_⟩
    rw [φ.fourierMultiplierCLM_eq_zero_of_finrank_eq_zero hE hm, zero_apply,
      map_zero, eLpNorm_congr_ae (Lp.coeFn_zero _ _ _), eLpNorm_zero]
    exact zero_le
  have hq0 : (0 : ℝ) < 2 / q := div_pos two_pos (by exact_mod_cast zero_lt_two.trans hq)
  have hn1 : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hE
  set n : ℝ := ((Module.finrank ℝ E : ℕ) : ℝ)
  set ρ := (r⁻¹).toReal
  -- Admissibility with `2 < q` and `n ≥ 1` forces `1 / r < 1 / 2`, so `2 ≤ r`.
  have hρ : ρ < 2⁻¹ := by nlinarith
  have hr : 2 ≤ r := by
    rw [← ENNReal.inv_le_inv,
      ← ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 (ENNReal.HolderConjugate.ne_zero r r')),
      ← ENNReal.ofReal_toReal (a := 2⁻¹) (by simp)]
    exact ENNReal.ofReal_le_ofReal (hρ.le.trans_eq (by simp))
  obtain ⟨C, hC0, hC⟩ := φ.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_le
    (r' := r') hr
  set θ := 1 - 2 * ρ
  refine ⟨C ^ θ, by positivity, fun j m hm τ hτ0 g ↦ ?_⟩
  have h2 : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  have hτ : 0 < |τ| := abs_pos.2 hτ0
  refine (hC j m hm τ g).trans ?_
  rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_pos hτ,
    ← ENNReal.ofReal_mul (by positivity)]
  gcongr
  -- Since `2 / q ≤ (n - 1) / 2 · (1 - 2 / r)`, the factor
  -- `(1 + 2^j |τ|)^(-(n - 1)/2 · (1 - 2 / r))` is at most `(2^j |τ|)^(-2 / q)`.
  have hx : 0 < 2 ^ j * |τ| := mul_pos h2 hτ
  have hexp : 2 / (q : ℝ) ≤ (n - 1) / 2 * θ := by
    simp only [θ]
    linarith
  calc (C * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E * (1 + 2 ^ j * |τ|) ^ (-(n - 1) / 2)) ^ θ
      = C ^ θ * ((2 : ℝ) ^ j) ^ (n * θ) * (1 + 2 ^ j * |τ|) ^ (-(n - 1) / 2 * θ) := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hC0 (by positivity),
          ← Real.rpow_natCast, ← Real.rpow_mul h2.le, ← Real.rpow_mul (by positivity)]
    _ ≤ C ^ θ * ((2 : ℝ) ^ j) ^ (n * θ) * (2 ^ j * |τ|) ^ (-(2 / q : ℝ)) := by
        gcongr
        calc (1 + 2 ^ j * |τ|) ^ (-(n - 1) / 2 * θ)
            ≤ (1 + 2 ^ j * |τ|) ^ (-(2 / q : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hexp])
          _ ≤ (2 ^ j * |τ|) ^ (-(2 / q : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos hx (by linarith) (by linarith)
    _ = C ^ θ * ((2 : ℝ) ^ j) ^ (2 * (n / 2 - n * ρ - 1 / q)) * |τ| ^ (-(2 / q : ℝ)) := by
        rw [Real.mul_rpow h2.le hτ.le, ← mul_assoc, mul_assoc (C ^ θ),
          ← Real.rpow_add h2]
        congr 3
        simp only [θ]
        ring

/-! ### Strichartz estimates at the wave-admissible pairs -/

/-- **Decay of the time pairings.** Along a wave-admissible pair,
`2 / q + (n - 1) / r ≤ (n - 1) / 2` with `2 < q`, the time pairings `W₊(s - t) Pⱼ²` of
`U(t) = W₊(t) Pⱼ` decay from `L^{r'}` to `L^r` like `|s - t| ^ (-2 / q)`, with the factor
`2^{2 j s(q, r)}`, `s(q, r) = n/2 - n/r - 1/q`, since `Pⱼ` is bounded on `L^{r'}` uniformly in
`j`. This is the hypothesis of the `TT*` argument. -/
private theorem exists_eLpNorm_halfWavePropagator_comp_adjoint_le (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + (Module.finrank ℝ E - 1) * (r⁻¹).toReal ≤
      (Module.finrank ℝ E - 1) / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ s t : ℝ, s ≠ t →
      ∀ g : Lp ℂ 2 (volume : Measure E),
      eLpNorm ((halfWavePropagator ℂ s ∘L Lp.fourierMultiplierCLM ℂ m)
          (((halfWavePropagator ℂ t ∘L Lp.fourierMultiplierCLM ℂ m)†) g)) r volume ≤
        ENNReal.ofReal (K * ((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) *
          eLpNorm g r' volume := by
  obtain ⟨K, hK0, hK⟩ :=
    φ.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_le_rpow (r' := r') hq hqr
  obtain ⟨L, hL⟩ := φ.exists_eLpNorm_fourierMultiplierCLM_le (F := ℂ)
  refine ⟨K * L, by positivity, fun j m hm s t hst g ↦ ?_⟩
  rw [φ.halfWavePropagator_comp_apply_adjoint hm]
  calc _ ≤ _ := hK j m hm (s - t) (sub_ne_zero.2 hst) _
    _ ≤ ENNReal.ofReal (K * ((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) *
          (L * eLpNorm g r' volume) := by
        gcongr
        exact hL j m hm (ENNReal.HolderConjugate.one_le r' r) g
    _ = _ := by
        rw [mul_right_comm K, ENNReal.ofReal_mul' (q := (L : ℝ)) L.coe_nonneg,
          ENNReal.ofReal_coe_nnreal]
        ring

/-- **The dual frequency-localized Strichartz estimate for the half-wave propagator.** Let `E`
have dimension `n`, let `(q, r)` be a wave-admissible pair, `2 / q + (n - 1) / r ≤ (n - 1) / 2`
with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates of `q` and `r`, and let
`s(q, r) = n/2 - n/r - 1/q`. There is `C` such that for every `j ∈ ℤ`, every symbol `m` of `Pⱼ` and
every almost everywhere strongly measurable `F : ℝ → L²(E)`,

`‖∫ Pⱼ W₊(-s) F(s) ds‖₂ ≤ C 2^{j s(q, r)} ‖F‖_{L^p_t L^{r'}_x}`. -/
theorem exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + (Module.finrank ℝ E - 1) * (r⁻¹).toReal ≤
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
  have hs (x : ℝ) : 2 * x * 2⁻¹ = x := by ring
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    Real.mul_rpow hK0 (by positivity), ← Real.rpow_mul (zpow_pos two_pos j).le, hs,
    ENNReal.ofReal_mul (by positivity), ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal]
  ring

/-- **The frequency-localized Strichartz estimate for the half-wave propagator**, in weak form.
Let `E` have dimension `n`, let `(q, r)` be a wave-admissible pair,
`2 / q + (n - 1) / r ≤ (n - 1) / 2` with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates
of `q` and `r`, and let `s(q, r) = n/2 - n/r - 1/q`. There is `C` such that for every `j ∈ ℤ`, every
symbol `m` of `Pⱼ`, every `f ∈ L²(E)` and every almost everywhere strongly measurable
`G : ℝ → L²(E)` for which `t ↦ Pⱼ W₊(-t) G(t)` is integrable,

`|∫ ⟪W₊(t) Pⱼ f, G(t)⟫ dt| ≤ C 2^{j s(q, r)} ‖f‖₂ ‖G‖_{L^p_t L^{r'}_x}`.

This is `‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{j s(q, r)} ‖f‖₂` tested against `G`, and follows from
the dual estimate
`ContDiffBump.exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le`. -/
theorem exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + (Module.finrank ℝ E - 1) * (r⁻¹).toReal ≤
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
  obtain ⟨C, hC⟩ :=
    φ.exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le (r' := r') hq hpq hqr
  refine ⟨C, fun j m hm f G hG hPG ↦ ?_⟩
  -- `⟪W₊(t) Pⱼ f, G(t)⟫ = ⟪f, Pⱼ W₊(-t) G(t)⟫`.
  have hadj (t : ℝ) : ⟪halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f), G t⟫_ℂ =
      ⟪f, Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ (-t) (G t))⟫_ℂ := by
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_right,
      φ.adjoint_halfWavePropagator_comp_fourierMultiplierCLM hm, ContinuousLinearMap.comp_apply]
  simp_rw [hadj]
  rw [integral_inner hPG]
  calc _ ≤ ‖f‖ₑ * ‖∫ t, Lp.fourierMultiplierCLM ℂ m (halfWavePropagator ℂ (-t) (G t))‖ₑ :=
        eNorm_inner_le_eNorm _ _
    _ ≤ ‖f‖ₑ * (C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q)) *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume) := by
        gcongr
        exact hC j m hm G hG
    _ = _ := by ring

/-- **The bilinear frequency-localized Strichartz estimate for the half-wave propagator.** Let
`E` have dimension `n`, let `(q, r)` be a wave-admissible pair,
`2 / q + (n - 1) / r ≤ (n - 1) / 2` with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates
of `q` and `r`, and let `s(q, r) = n/2 - n/r - 1/q`. There is `C` such that for every `j ∈ ℤ`, every
symbol `m` of `Pⱼ` and all almost everywhere strongly measurable `F, G : ℝ → L²(E)`,

`∫∫ |⟪W₊(t - s) Pⱼ F(s), G(t)⟫| ds dt ≤
  C 2^{2 j s(q, r)} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

Since the integrand is the absolute value of the Duhamel pairing, the bound also controls the
integral over any part of the `(s, t)` plane, such as the retarded region `s < t`:
`ContDiffBump.exists_enorm_integral_setIntegral_inner_halfWavePropagator_fourierMultiplierCLM_le`.
-/
theorem exists_lintegral_lintegral_enorm_inner_halfWavePropagator_fourierMultiplierCLM_le
    (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + (Module.finrank ℝ E - 1) * (r⁻¹).toReal ≤
      (Module.finrank ℝ E - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      AEStronglyMeasurable G →
      ∫⁻ t, ∫⁻ s, ‖⟪halfWavePropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ m (F s)), G t⟫_ℂ‖ₑ ≤
        C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) *
          eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨K, hK0, hK⟩ :=
    φ.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_le_rpow (r' := r') hq hqr
  obtain ⟨C, hC⟩ := exists_lintegral_lintegral_enorm_inner_le (𝕜 := ℂ) (E := ℂ) (X := E)
    (μ := volume) (r := r) (r' := r') hq hpq
  refine ⟨C * K.toNNReal, fun j m hm F G hF hG ↦ ?_⟩
  -- The Duhamel pairing `⟪W₊(t - s) Pⱼ F(s), G(t)⟫` is `⟪G(t), T(t, s) F(s)⟫` up to complex
  -- conjugation, for the kernel `T(t, s) = W₊(t - s) Pⱼ`.
  have hpair (s t : ℝ) :
      ‖⟪halfWavePropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ m (F s)), G t⟫_ℂ‖ₑ =
        ‖⟪G t, halfWavePropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ m (F s))⟫_ℂ‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, norm_inner_symm]
  simp_rw [hpair]
  calc _ ≤ _ := hC (fun t s g ↦ halfWavePropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ m g)) _
        (fun t s hts g ↦ hK j m hm (t - s) (sub_ne_zero.2 hts) g) G F hG hF
    _ = _ := by
        rw [ENNReal.ofReal_mul hK0, ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal]
        ring

/-- **The retarded frequency-localized Strichartz estimate for the half-wave propagator**, in
weak form. Let `E` have dimension `n`, let `(q, r)` be a wave-admissible pair,
`2 / q + (n - 1) / r ≤ (n - 1) / 2` with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates
of `q` and `r`, and let `s(q, r) = n/2 - n/r - 1/q`. There is `C` such that for every `j ∈ ℤ`, every
symbol `m` of `Pⱼ` and all almost everywhere strongly measurable `F, G : ℝ → L²(E)`,

`|∫ ∫_{s < t} ⟪W₊(t - s) Pⱼ F(s), G(t)⟫ ds dt| ≤
  C 2^{2 j s(q, r)} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

This is the Duhamel estimate
`‖∫_{s < t} W₊(t - s) Pⱼ F(s) ds‖_{L^q_t L^r_x} ≤ C 2^{2 j s(q, r)} ‖F‖_{L^p_t L^{r'}_x}` tested
against `G`. -/
theorem exists_enorm_integral_setIntegral_inner_halfWavePropagator_fourierMultiplierCLM_le
    (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + (Module.finrank ℝ E - 1) * (r⁻¹).toReal ≤
      (Module.finrank ℝ E - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      AEStronglyMeasurable G →
      ‖∫ t, ∫ s in Set.Iio t,
          ⟪halfWavePropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ m (F s)), G t⟫_ℂ‖ₑ ≤
        C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / q))) *
          eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨C, hC⟩ :=
    φ.exists_lintegral_lintegral_enorm_inner_halfWavePropagator_fourierMultiplierCLM_le
      (r' := r') hq hpq hqr
  refine ⟨C, fun j m hm F G hF hG ↦ ?_⟩
  calc _ ≤ ∫⁻ t, ‖∫ s in Set.Iio t,
          ⟪halfWavePropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ m (F s)), G t⟫_ℂ‖ₑ :=
        eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ t, ∫⁻ s in Set.Iio t,
          ‖⟪halfWavePropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ m (F s)), G t⟫_ℂ‖ₑ :=
        lintegral_mono fun t ↦ eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ t, ∫⁻ s,
          ‖⟪halfWavePropagator ℂ (t - s) (Lp.fourierMultiplierCLM ℂ m (F s)), G t⟫_ℂ‖ₑ :=
        lintegral_mono fun t ↦ setLIntegral_le_lintegral _ _
    _ ≤ _ := hC j m hm F G hF hG

end Admissible

end ContDiffBump

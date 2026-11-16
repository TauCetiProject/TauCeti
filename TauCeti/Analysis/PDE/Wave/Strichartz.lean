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
# Frequency-localized Strichartz estimates for the wave equation

On a real inner product space `E` of dimension `n`, let `W₊(t) = exp(itD)`, `D = √(-Δ)`, be the
half-wave propagator (`TauCeti.halfWavePropagator`) and let `Pⱼ` be the `L²` Fourier multiplier
with the Littlewood–Paley cutoff `ψⱼ` (`ContDiffBump.littlewoodPaley`), supported where
`‖ξ‖ ≈ 2^j`, as symbol. The frequency-localized propagators satisfy the dispersive estimate
`‖W₊(t) Pⱼ f‖_∞ ≤ C 2^{jn} (1 + 2^j |t|)^(-(n - 1)/2) ‖f‖₁`
(`ContDiffBump.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le`). This
file turns it into Strichartz estimates for `W₊(t) Pⱼ`, uniformly in the scale `j ∈ ℤ`.

Call `(q, r)` *sharp wave-admissible* when `2 / q + (n - 1) / r = (n - 1) / 2`, the
`σ`-admissibility of the abstract `TT*` argument with the wave decay exponent `σ = (n - 1) / 2`,
and let `γ = n / 2 - n / r - 1 / q` be the scaling-critical regularity of the pair. For every such
pair with `2 < q < ∞`, and `p`, `r'` the Hölder conjugates of `q`, `r`, there is `C` such that for
every `j ∈ ℤ`

`‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{jγ} ‖f‖₂`,

in weak form, together with the dual estimate and the bilinear and retarded estimates for the
Duhamel pairings `⟪W₊(t - s) Pⱼ Pⱼ F(s), G(t)⟫`, with the factor `2^{2jγ}`. The power of `2^j`
is the one dictated by scaling: rescaling `x ↦ 2^j x` maps the cutoff `ψ₀` to `ψⱼ`. These are
the frequency-localized estimates from which the wave Strichartz estimates with data in the
homogeneous Sobolev space of order `γ` are assembled by Littlewood–Paley summation. The endpoint
`q = 2` is not covered.

## The argument

Let `U(t) = W₊(t) Pⱼ`. Its time pairings are `U(s) U(t)* = W₊(s - t) Pⱼ Pⱼ`, since the symbol of
`Pⱼ` is real and Fourier multipliers commute. Two facts bound them from `L^{r'}` to `L^r`:

* `Pⱼ` is bounded on every `Lᵖ`, `1 ≤ p ≤ ∞`, uniformly in `j`
  (`ContDiffBump.eLpNorm_fourierMultiplierCLM_littlewoodPaley_le`);
* interpolating the dispersive estimate with the `L²` bound `‖W₊(t) Pⱼ‖ ≤ 1` by the Riesz–Thorin
  theorem gives `‖W₊(t) Pⱼ f‖_r ≤ (C 2^{jn} (1 + 2^j |t|)^(-(n - 1)/2))^(1 - 2/r) ‖f‖_{r'}`.

Dropping the `1` in `1 + 2^j |t|` bounds the time pairings by `A 2^{2jγ} |s - t|^(-2/q)`, with
`A` independent of `j`, exactly when `(q, r)` is sharp wave-admissible; the `TT*` theorems of
`TauCeti.Analysis.PDE.Strichartz.TTStar` then apply with the constant `A 2^{2jγ}`.

## Main declarations

All in the `ContDiffBump` namespace, with `φ` the bump function defining the cutoffs.

* `exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le_of_memLp`:
  the dispersive estimate for `W₊(t) Pⱼ` from `Lᵖ` to `L^q`.
* `exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_littlewoodPaley_le`:
  the bilinear estimate for the Duhamel pairings.
* `exists_enorm_integral_setIntegral_Iio_inner_halfWavePropagator_sub_littlewoodPaley_le`:
  the retarded estimate, in weak form.
* `exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le`: the dual
  estimate.
* `exists_enorm_integral_inner_halfWavePropagator_littlewoodPaley_le`: the
  homogeneous estimate, in weak form.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Sections 2.2 and 2.3 (Theorem 2.6 and its proof).
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
-/

public section

noncomputable section

open scoped ENNReal NNReal FourierTransform InnerProductSpace InnerProduct
open MeasureTheory TauCeti

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (φ : ContDiffBump (0 : E))

/-! ### The dispersive estimate from `Lᵖ` to `L^q` -/

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

/-! ### The time pairings -/

section TimePairing

variable {φ} {j : ℤ} {m : Lp ℂ ∞ (volume : Measure E)}

/-- The adjoint of `W₊(t) Pⱼ` is `W₊(-t) Pⱼ`: the symbol `ψⱼ` is real, and multipliers
commute. -/
private theorem adjoint_halfWavePropagator_comp_apply
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (t : ℝ)
    (g : Lp ℂ 2 (volume : Measure E)) :
    (((halfWavePropagator ℂ t).comp (Lp.fourierMultiplierCLM ℂ m))†) g =
      halfWavePropagator ℂ (-t) (Lp.fourierMultiplierCLM ℂ m g) := by
  rw [ContinuousLinearMap.adjoint_comp, Lp.adjoint_fourierMultiplierCLM,
    Lp.star_eq_self_of_ae_eq_ofReal hm, adjoint_halfWavePropagator,
    ← halfWavePropagator_comp_fourierMultiplierCLM, ContinuousLinearMap.comp_apply]

/-- The time pairings of the family `U(t) = W₊(t) Pⱼ` are `U(s) U(t)* = W₊(s - t) Pⱼ Pⱼ`. -/
private theorem halfWavePropagator_comp_apply_adjoint_apply
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (s t : ℝ)
    (g : Lp ℂ 2 (volume : Measure E)) :
    ((halfWavePropagator ℂ s).comp (Lp.fourierMultiplierCLM ℂ m))
        ((((halfWavePropagator ℂ t).comp (Lp.fourierMultiplierCLM ℂ m))†) g) =
      halfWavePropagator ℂ (s - t)
        (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m g)) := by
  rw [adjoint_halfWavePropagator_comp_apply hm, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.comp_apply (Lp.fourierMultiplierCLM ℂ m) (halfWavePropagator ℂ (-t)),
    ← halfWavePropagator_comp_fourierMultiplierCLM, ContinuousLinearMap.comp_apply,
    sub_eq_add_neg, halfWavePropagator_add_apply]

/-- In dimension `0` the cutoffs vanish, and so do the blocks. -/
private theorem fourierMultiplierCLM_littlewoodPaley_eq_zero
    (hm : m =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) (hE : Module.finrank ℝ E = 0) :
    Lp.fourierMultiplierCLM ℂ m = 0 := by
  have : Subsingleton E := Module.finrank_zero_iff.1 hE
  rw [Lp.fourierMultiplierCLM_of_ae_eq_const (F := ℂ) (c := 0)]
  · exact zero_smul ℂ (ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure E)))
  filter_upwards [hm] with ξ h
  rw [h, Subsingleton.elim ξ 0, φ.littlewoodPaley_eq_zero_of_norm_le (by
    rw [norm_zero]; exact (mul_pos (zpow_pos two_pos _) φ.rIn_pos).le), Complex.ofReal_zero]

/-- Dropping the `1` in `1 + 2^j |τ|`: for `τ ≠ 0`, `n ≥ 1` and `θ ≥ 0`,
`(C 2^{jn} (1 + 2^j |τ|)^(-(n - 1)/2))^θ ≤ C^θ 2^{j (n + 1) θ / 2} |τ|^(-(n - 1) θ / 2)`. -/
private theorem rpow_mul_one_add_rpow_le {C θ : ℝ} (hC : 0 ≤ C) (hθ : 0 ≤ θ) (j : ℤ) {τ : ℝ}
    (hτ : τ ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    (C * ((2 : ℝ) ^ j) ^ n * (1 + 2 ^ j * |τ|) ^ (-((n : ℝ) - 1) / 2)) ^ θ ≤
      C ^ θ * ((2 : ℝ) ^ j) ^ (((n : ℝ) + 1) / 2 * θ) *
        |τ| ^ (-((n : ℝ) - 1) / 2 * θ) := by
  have h2 : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  have hτ' : 0 < |τ| := abs_pos.2 hτ
  have hz : -((n : ℝ) - 1) / 2 ≤ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc _ ≤ (C * ((2 : ℝ) ^ j) ^ n * (2 ^ j * |τ|) ^ (-((n : ℝ) - 1) / 2)) ^ θ := by
        refine Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hz) (by positivity)) hθ
    _ = _ := by
        rw [Real.mul_rpow h2.le hτ'.le, ← mul_assoc, mul_assoc C, ← Real.rpow_natCast,
          ← Real.rpow_add h2, Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow hC (by positivity), ← Real.rpow_mul h2.le, ← Real.rpow_mul hτ'.le]
        congr 3
        ring

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

end TimePairing

section Admissible

variable {p q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
include r' in
/-- In positive dimension `n`, a sharp wave-admissible pair `2 / q + (n - 1) / r = (n - 1) / 2`
with `2 < q` has `n ≥ 2` and `r > 2`. -/
private theorem two_le_finrank_of_admissible (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal =
      ((Module.finrank ℝ E : ℝ) - 1) / 2) (hE : 0 < Module.finrank ℝ E) :
    2 ≤ Module.finrank ℝ E ∧ (r⁻¹).toReal < 2⁻¹ ∧ 2 ≤ r := by
  have hq0 : (0 : ℝ) < 2 / q := div_pos two_pos (by exact_mod_cast zero_lt_two.trans hq)
  have hn : 2 ≤ Module.finrank ℝ E := by
    by_contra h
    have h1 : Module.finrank ℝ E = 1 := by omega
    rw [h1, Nat.cast_one, sub_self, zero_mul, add_zero, zero_div] at hqr
    exact hq0.ne' hqr
  have hn' : (1 : ℝ) ≤ Module.finrank ℝ E - 1 := by
    have : (2 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hn
    linarith
  have hρ : (r⁻¹).toReal < 2⁻¹ := by
    have h : 0 < ((Module.finrank ℝ E : ℝ) - 1) * (2⁻¹ - (r⁻¹).toReal) := by linarith
    linarith [pos_of_mul_pos_right h (by linarith)]
  refine ⟨hn, hρ, ?_⟩
  rw [← ENNReal.inv_le_inv,
    ← ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 (ENNReal.HolderConjugate.ne_zero r r')),
    ← ENNReal.ofReal_toReal (a := 2⁻¹) (by simp)]
  exact ENNReal.ofReal_le_ofReal (hρ.le.trans_eq (by simp))

/-- **Decay of the time pairings** along a sharp wave-admissible pair: if `2 < q` and
`2 / q + (n - 1) / r = (n - 1) / 2`, there is `A` such that for every scale `j`, all times
`s ≠ t` and every `g ∈ L²`, `‖U(s) U(t)* g‖_r ≤ A 2^{2jγ} |s - t|^(-2/q) ‖g‖_{r'}`, where
`U(t) = W₊(t) Pⱼ` and `γ = n / 2 - n / r - 1 / q`. -/
private theorem exists_eLpNorm_halfWavePropagator_comp_adjoint_le (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal =
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ A : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ s t, s ≠ t →
      ∀ g : Lp ℂ 2 (volume : Measure E),
        eLpNorm (((halfWavePropagator ℂ s).comp (Lp.fourierMultiplierCLM ℂ m))
          ((((halfWavePropagator ℂ t).comp (Lp.fourierMultiplierCLM ℂ m))†) g)) r volume ≤
        A * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (2 * ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹))) *
          ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' volume := by
  obtain ⟨C, hC0, hC⟩ :=
    φ.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le_of_memLp
  set K := eLpNorm (𝓕⁻ (fun ξ ↦ (φ.littlewoodPaley 0 ξ : ℂ))) 1 volume
  set ρ := (r⁻¹).toReal
  set θ := 1 - 2 * ρ
  refine ⟨(C ^ θ).toNNReal * K.toNNReal, fun j m hm s t hst g ↦ ?_⟩
  rw [halfWavePropagator_comp_apply_adjoint_apply hm]
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hE | hE
  · -- In dimension `0` the blocks vanish.
    rw [fourierMultiplierCLM_littlewoodPaley_eq_zero hm hE, zero_apply, map_zero,
      eLpNorm_congr_ae (Lp.coeFn_zero _ _ _), eLpNorm_zero]
    exact zero_le
  -- In positive dimension, admissibility with `2 < q` forces `n ≥ 2` and `r > 2`.
  obtain ⟨hn, hρ, hr⟩ := two_le_finrank_of_admissible (r' := r') hq hqr hE
  have hθ : 0 ≤ θ := by linarith
  have hst' : 0 < |s - t| := abs_pos.2 (sub_ne_zero.2 hst)
  set D := (C * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
    (1 + 2 ^ j * |s - t|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)) ^ θ
  have hD : 0 < D := Real.rpow_pos_of_pos (by positivity) _
  -- The exponents: `(n + 1) θ / 2 = 2 γ` and `(n - 1) θ / 2 = 2 / q`.
  have he₁ : ((Module.finrank ℝ E : ℝ) + 1) / 2 * θ =
      2 * ((Module.finrank ℝ E : ℝ) / 2 - Module.finrank ℝ E * ρ - (q : ℝ)⁻¹) := by
    rw [div_eq_mul_inv] at hqr
    linarith
  have he₂ : -((Module.finrank ℝ E : ℝ) - 1) / 2 * θ = -(2 / q : ℝ) := by linarith
  calc _ ≤ ENNReal.ofReal D * eLpNorm (Lp.fourierMultiplierCLM ℂ m g) r' volume := by
        by_cases hPg : MemLp (Lp.fourierMultiplierCLM ℂ m g) r' volume
        · exact hC j m hm (s - t) hr _ hPg
        · rw [top_unique (not_lt.1 (memLp_iff.not.1 hPg)),
            ENNReal.mul_top (ENNReal.ofReal_pos.2 hD).ne']
          exact le_top
    _ ≤ ENNReal.ofReal (C ^ θ * ((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) + 1) / 2 * θ) *
          |s - t| ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2 * θ)) *
          (K * eLpNorm g r' volume) := by
        gcongr
        · exact rpow_mul_one_add_rpow_le hC0.le hθ j (sub_ne_zero.2 hst) (by omega)
        · exact φ.eLpNorm_fourierMultiplierCLM_littlewoodPaley_le hm g
            (ENNReal.HolderConjugate.one_le r' r)
    _ = _ := by
        rw [he₁, he₂, ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal,
          ENNReal.coe_toNNReal (φ.memLp_fourierInv_littlewoodPaley 0 1).eLpNorm_ne_top,
          ← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_pos hst',
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        ring

/-- **The bilinear Strichartz estimate for the frequency-localized wave equation.** Let `E` have
dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, and let `Pⱼ` be the `L²`
Fourier multiplier with symbol `ψⱼ`. Let `(q, r)` be sharp wave-admissible,
`2 / q + (n - 1) / r = (n - 1) / 2`, with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates
of `q` and `r`, and let `γ = n / 2 - n / r - 1 / q`. There is `C` such that for every `j ∈ ℤ` and
all almost everywhere strongly measurable `F, G : ℝ → L²(E)`,

`∫∫ |⟪W₊(t - s) Pⱼ Pⱼ F(s), G(t)⟫| ds dt ≤ C 2^{2jγ} ‖F‖_{L^p_t L^{r'}_x} ‖G‖_{L^p_t L^{r'}_x}`.

Since the integrand is the absolute value of the Duhamel pairing, the bound also controls the
integral over any part of the `(s, t)` plane, such as the retarded region `s < t`. -/
theorem exists_lintegral_lintegral_enorm_inner_halfWavePropagator_sub_littlewoodPaley_le
    (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal =
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
  obtain ⟨A, hA⟩ := φ.exists_eLpNorm_halfWavePropagator_comp_adjoint_le (r' := r') hq hqr
  obtain ⟨C, hC⟩ := exists_lintegral_lintegral_enorm_inner_adjoint_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq
    hpq
  refine ⟨C * A, fun j m hm F G hF hG ↦ ?_⟩
  -- The Duhamel pairing `⟪W₊(t - s) Pⱼ Pⱼ F(s), G(t)⟫` is the time pairing
  -- `⟪U(t)* G(t), U(s)* F(s)⟫` up to complex conjugation.
  have hpair (s t : ℝ) : ‖⟪halfWavePropagator ℂ (t - s)
      (Lp.fourierMultiplierCLM ℂ m (Lp.fourierMultiplierCLM ℂ m (F s))), G t⟫_ℂ‖ₑ =
      ‖⟪(((halfWavePropagator ℂ t).comp (Lp.fourierMultiplierCLM ℂ m))†) (G t),
        (((halfWavePropagator ℂ s).comp (Lp.fourierMultiplierCLM ℂ m))†) (F s)⟫_ℂ‖ₑ := by
    rw [ContinuousLinearMap.adjoint_inner_left, halfWavePropagator_comp_apply_adjoint_apply hm,
      ← ofReal_norm, ← ofReal_norm, norm_inner_symm]
  simp_rw [hpair]
  calc _ ≤ _ := hC (fun t ↦ (halfWavePropagator ℂ t).comp (Lp.fourierMultiplierCLM ℂ m)) _
        (fun s t hst g ↦ hA j m hm s t hst g) G F hG hF
    _ = _ := by
        push_cast
        ring

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
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal =
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
Fourier multiplier with symbol `ψⱼ`. Let `(q, r)` be sharp wave-admissible,
`2 / q + (n - 1) / r = (n - 1) / 2`, with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates
of `q` and `r`, and let `γ = n / 2 - n / r - 1 / q`. There is `C` such that for every `j ∈ ℤ` and
every almost everywhere strongly measurable `F : ℝ → L²(E)` for which `s ↦ W₊(-s) Pⱼ F(s)` is
integrable,

`‖∫ W₊(-s) Pⱼ F(s) ds‖₂ ≤ C 2^{jγ} ‖F‖_{L^p_t L^{r'}_x}`. -/
theorem exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal =
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
        Integrable (fun s ↦ halfWavePropagator ℂ (-s) (Lp.fourierMultiplierCLM ℂ m (F s))) →
        ‖∫ s, halfWavePropagator ℂ (-s) (Lp.fourierMultiplierCLM ℂ m (F s))‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume := by
  obtain ⟨A, hA⟩ := φ.exists_eLpNorm_halfWavePropagator_comp_adjoint_le (r' := r') hq hqr
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le (𝕜 := ℂ) (H := Lp ℂ 2 (volume : Measure E))
    (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq hpq
  refine ⟨C * NNReal.sqrt A, fun j m hm F hF hWF ↦ ?_⟩
  have h := hC (fun t ↦ (halfWavePropagator ℂ t).comp (Lp.fourierMultiplierCLM ℂ m)) _
    (fun s t hst g ↦ hA j m hm s t hst g) F hF
    (by simpa only [adjoint_halfWavePropagator_comp_apply hm] using hWF)
  simp only [adjoint_halfWavePropagator_comp_apply hm] at h
  rw [coe_mul_ofReal_rpow_two_mul_rpow_inv_two A (by positivity)] at h
  calc _ ≤ _ := h
    _ = _ := by
        push_cast
        ring

/-- **The Strichartz estimate for the frequency-localized wave equation**, in weak form. Let `E`
have dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, and let `Pⱼ` be the
`L²` Fourier multiplier with symbol `ψⱼ`. Let `(q, r)` be sharp wave-admissible,
`2 / q + (n - 1) / r = (n - 1) / 2`, with `2 < q < ∞`, let `p` and `r'` be the Hölder conjugates
of `q` and `r`, and let `γ = n / 2 - n / r - 1 / q`. There is `C` such that for every `j ∈ ℤ`,
every `f ∈ L²(E)` and every almost everywhere strongly measurable `G : ℝ → L²(E)` for which
`t ↦ W₊(-t) Pⱼ G(t)` is integrable,

`|∫ ⟪W₊(t) Pⱼ f, G(t)⟫ dt| ≤ C 2^{jγ} ‖f‖₂ ‖G‖_{L^p_t L^{r'}_x}`.

This is `‖W₊(t) Pⱼ f‖_{L^q_t L^r_x} ≤ C 2^{jγ} ‖f‖₂` tested against `G`. -/
theorem exists_enorm_integral_inner_halfWavePropagator_littlewoodPaley_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal =
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
  obtain ⟨A, hA⟩ := φ.exists_eLpNorm_halfWavePropagator_comp_adjoint_le (r' := r') hq hqr
  obtain ⟨C, hC⟩ := exists_enorm_integral_inner_apply_le (𝕜 := ℂ)
    (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (X := E) (μ := volume) (r := r) (r' := r') hq hpq
  refine ⟨C * NNReal.sqrt A, fun j m hm f G hG hWG ↦ ?_⟩
  have h := hC (fun t ↦ (halfWavePropagator ℂ t).comp (Lp.fourierMultiplierCLM ℂ m)) _
    (fun s t hst g ↦ hA j m hm s t hst g) f G hG
    (by simpa only [adjoint_halfWavePropagator_comp_apply hm] using hWG)
  rw [coe_mul_ofReal_rpow_two_mul_rpow_inv_two A (by positivity)] at h
  calc _ ≤ _ := h
    _ = _ := by
        push_cast
        ring

end Admissible

end ContDiffBump

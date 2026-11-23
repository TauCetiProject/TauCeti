/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Strichartz.Endpoint
public import TauCeti.Analysis.PDE.Wave.Strichartz
import TauCeti.Analysis.Fourier.LittlewoodPaley
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.MeasureTheory.Function.Lp.MixedNorm
import TauCeti.MeasureTheory.Function.Lp.Star

/-!
# The endpoint Strichartz estimate for the frequency-localized wave equation

Let `E` have dimension `n ≥ 4`, let `ψ` be smooth, compactly supported and vanish near the origin,
and for `j ∈ ℤ` let `Pⱼ` be the `L²` Fourier multiplier with the dilated symbol `ψ (2^{-j} ·)`.
The wave-admissible pairs `(q, r)`, `2 / q + (n - 1) / r ≤ (n - 1) / 2`, include for `n ≥ 4` the
endpoint `q = 2`, `r = 2 (n - 1) / (n - 3)`, which lies on the boundary line:
`1 + (n - 1) / r = (n - 1) / 2`. This file proves the **endpoint Strichartz estimate** for the
frequency-localized half-wave propagators `W₊(t) Pⱼ`, `W₊(t) = exp(itD)`, `D = √(-Δ)`,

`‖W₊(t) Pⱼ f‖_{L²_t L^r_x} ≤ C 2^{jγ} ‖f‖₂`,  `γ = n / 2 - n / r - 1 / 2 = (n + 1) / (2 (n - 1))`,

with `C` independent of `j`, in its dual form
(`TauCeti.exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le_of_endpoint`) and in
weak form tested against `L²_t L^{r'}_x`
(`TauCeti.exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le_of_endpoint`),
and for the Littlewood–Paley blocks, where it also holds in mixed norm
(`ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_endpoint`). The
endpoint exponent satisfies `2 ≤ r < ∞` (`TauCeti.two_le_and_ne_top_of_waveEndpoint`). The power
of `2^j` is the one dictated by scaling, as at the non-endpoint pairs of
`TauCeti.Analysis.PDE.Wave.Strichartz`. In dimension `3` the boundary pair with `q = 2` is
`(2, ∞)`, which is excluded; there the time decay `|t|^(-1)` of the dispersive estimate is not
integrable at infinity, and the argument below needs a decay rate above `1`.

## The argument

This is the endpoint theorem of Keel and Tao, applied with the decay rate `σ = (n - 1) / 2 > 1`
to the time-rescaled family `V(t) = W₊(μ t) Pⱼ` with `μ = 2^{2jγ}`: the region estimate
`TauCeti.exists_enorm_setIntegral_inner_adjoint_le_of_endpoint_of_four_thirds` on the whole plane
bounds the pairings, and `TauCeti.enorm_integral_le_sqrt_mul_of_enorm_integral_inner_le` turns
that into the dual estimate. The constant depends only on the constants of three bounds, and the
rescaling makes all three independent of `j`:

* `‖V(t)‖ ≤ sup |ψ|`;
* the time pairings `V(s) V(t)* = W₊(μ (s - t)) Pⱼ Pⱼ*` are bounded from `L¹` to `L^∞` by
  `C 2^{jn} (1 + 2^j μ |s - t|)^(-σ) ≤ C 2^{jn} (2^j μ)^(-σ) |s - t|^(-σ) = C |s - t|^(-σ)`
  (`TauCeti.exists_eLpNorm_halfWavePropagator_comp_fourierMultiplierCLM_apply_adjoint_le_top`),
  since `σ (1 + 2γ) = n`;
* the non-endpoint dual estimate at the wave-admissible pair `(4, r₄)` on the boundary line,
  `‖∫ Pⱼ* W₊(-s) G(s) ds‖ ≤ K 2^{jγ/2} ‖G‖_{L^{4/3}_t L^{b}_x}` with `b = r₄'`, becomes after the
  substitution `s = μ t` the same estimate for `V` with constant `K 2^{jγ/2} μ^{-1/4} = K`.

Undoing the rescaling costs `μ^{1/2} = 2^{jγ}`: the substitution multiplies the dual integral by
`μ` and the `L²_t` norm by at most `μ^{-1/2}` (`MeasureTheory.Measure.eLpNorm_comp_inv_smul`).

## References

* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980,
  Theorem 1.2 and Corollary 1.3.
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.6.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace InnerProduct ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ψ : E → ℂ}

/-! ### The time-rescaled family -/

/-- The decay of the dispersive bound after the time rescaling `τ ↦ c^κ τ`, `κ = (n + 1) / (n - 1)`:

`C c^n (1 + c c^κ τ)^(-(n - 1)/2) ≤ C τ^(-(n - 1)/2)`, since `(1 + κ) (n - 1) / 2 = n`. -/
private theorem mul_pow_mul_one_add_rpow_le {n : ℕ} (hn : 1 < n) {c C τ : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) (hτ : 0 < τ) :
    C * c ^ n * (1 + c * (c ^ (((n : ℝ) + 1) / ((n : ℝ) - 1)) * τ)) ^ (-(((n : ℝ) - 1) / 2)) ≤
      C * τ ^ (-(((n : ℝ) - 1) / 2)) := by
  have hn' : (0 : ℝ) < n - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hx : 0 < c * c ^ (((n : ℝ) + 1) / ((n : ℝ) - 1)) := by positivity
  have hcn : c ^ n * (c * c ^ (((n : ℝ) + 1) / ((n : ℝ) - 1))) ^ (-(((n : ℝ) - 1) / 2)) = 1 := by
    rw [← Real.rpow_one_add' hc.le (by positivity), ← Real.rpow_mul hc.le, ← Real.rpow_natCast,
      ← Real.rpow_add hc, show (n : ℝ) + (1 + ((n : ℝ) + 1) / ((n : ℝ) - 1)) *
        -(((n : ℝ) - 1) / 2) = 0 by field_simp; ring, Real.rpow_zero]
  calc _ ≤ C * c ^ n * (c * c ^ (((n : ℝ) + 1) / ((n : ℝ) - 1)) * τ) ^ (-(((n : ℝ) - 1) / 2)) := by
        rw [← mul_assoc c]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)) (by positivity)
    _ = _ := by rw [Real.mul_rpow hx.le hτ.le, ← mul_assoc, mul_assoc C, hcn, mul_one]

/-- The time pairings of the rescaled family `V(t) = W₊(2^{jκ} t) Pⱼ`, `κ = (n + 1) / (n - 1)`,
decay from `L¹` to `L^∞` like `A |s - t|^(-(n - 1)/2)` with `A` independent of `j`. -/
private theorem exists_eLpNorm_halfWavePropagator_mul_comp_apply_adjoint_le_top
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ)
    (hn : 1 < Module.finrank ℝ E) :
    ∃ A : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ ψ (((2 : ℝ) ^ j)⁻¹ • ξ)) → ∀ s t : ℝ, s ≠ t →
      ∀ g : Lp ℂ 2 (volume : Measure E),
        eLpNorm ((halfWavePropagator ℂ (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) + 1) /
            ((Module.finrank ℝ E : ℝ) - 1)) * s) ∘L Lp.fourierMultiplierCLM ℂ m)
          (((halfWavePropagator ℂ (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) + 1) /
            ((Module.finrank ℝ E : ℝ) - 1)) * t) ∘L Lp.fourierMultiplierCLM ℂ m)†) g)) ∞ volume ≤
        A * ‖s - t‖ₑ ^ (-(((Module.finrank ℝ E : ℝ) - 1) / 2)) * eLpNorm g 1 volume := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_eLpNorm_halfWavePropagator_comp_fourierMultiplierCLM_apply_adjoint_le_top hψ hψc hψ0
  refine ⟨C.toNNReal, fun j m hm s t hst g ↦ (hC j m hm _ _ g).trans ?_⟩
  gcongr ?_ * _
  have hst' : 0 < |s - t| := abs_pos.2 (sub_ne_zero.2 hst)
  rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_pos hst', ← ENNReal.ofReal_coe_nnreal,
    Real.coe_toNNReal _ hC0.le, ← ENNReal.ofReal_mul hC0.le, ← mul_sub, abs_mul,
    abs_of_pos (by positivity), neg_div]
  exact ENNReal.ofReal_le_ofReal (mul_pow_mul_one_add_rpow_le hn (zpow_pos two_pos j) hC0.le hst')

/-- The non-endpoint dual estimate at the wave-admissible pair `(4, r₄)` on the boundary line,
`1 / r₄ = 1/2 - 1/(2 (n - 1))`, with dual exponent `b`, `1 / b = 1/2 + 1/(2 (n - 1))`. Its power
of `2^j` is `2^{jκ/4}` with `κ = (n + 1) / (n - 1)`. -/
private theorem exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le_four
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ)
    (hn : 1 < Module.finrank ℝ E) :
    ∃ K : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ ψ (((2 : ℝ) ^ j)⁻¹ • ξ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      Integrable (fun s ↦ Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-s) (F s))) →
        ‖∫ s, Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-s) (F s))‖ₑ ≤
          K * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) + 1) /
            ((Module.finrank ℝ E : ℝ) - 1) / 4)) *
            eLpNorm (fun s ↦ eLpNorm (F s)
              (ENNReal.ofReal (2⁻¹ + (2 * ((Module.finrank ℝ E : ℝ) - 1))⁻¹))⁻¹ volume)
              ((4 / 3 : ℝ≥0) : ℝ≥0∞) volume := by
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn2 : (2 : ℝ) ≤ n := by simp only [n]; exact_mod_cast hn
  have hn1 : 0 < n - 1 := by linarith
  have hxp : 0 ≤ 2⁻¹ + (2 * (n - 1))⁻¹ := by positivity
  have hxm : 0 ≤ 2⁻¹ - (2 * (n - 1))⁻¹ := by
    rw [sub_nonneg]; exact inv_anti₀ two_pos (by linarith)
  set r₄ : ℝ≥0∞ := (ENNReal.ofReal (2⁻¹ - (2 * (n - 1))⁻¹))⁻¹
  have : (ENNReal.ofReal (2⁻¹ + (2 * (n - 1))⁻¹))⁻¹.HolderConjugate r₄ :=
    ENNReal.holderConjugate_iff.2 (by
      rw [inv_inv, inv_inv, ← ENNReal.ofReal_add hxp hxm, add_add_sub_cancel]
      norm_num)
  have hr₄inv : (r₄⁻¹).toReal = 2⁻¹ - (2 * (n - 1))⁻¹ := by
    rw [inv_inv, ENNReal.toReal_ofReal hxm]
  obtain ⟨K, hK⟩ := exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le hψ hψc
    hψ0 (p := 4 / 3) (q := 4) (r := r₄) (r' := (ENNReal.ofReal (2⁻¹ + (2 * (n - 1))⁻¹))⁻¹)
    (by norm_num)
    (by rw [← NNReal.holderConjugate_coe_iff, Real.holderConjugate_iff]; norm_num)
    (le_of_eq (by rw [← hn_def, hr₄inv]; push_cast; field_simp; ring))
  refine ⟨K, fun j m hm F hF hPF ↦ (hK j m hm F hF hPF).trans_eq ?_⟩
  rw [← hn_def, hr₄inv, show n / 2 - n * (2⁻¹ - (2 * (n - 1))⁻¹) - 1 / ((4 : ℝ≥0) : ℝ) =
    (n + 1) / (n - 1) / 4 by push_cast; field_simp; ring]

/-- After the substitution `s = c^κ t`, the dual estimate `hK`, whose constant carries the factor
`c^{κ/4}`, holds for `V(t) = W₊(c^κ t) T` with the constant `K`: the substitution contributes
`c^{-κ}` and the `L^{4/3}_t` norm `c^{3κ/4}`. -/
private theorem enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_mul_le {c κ : ℝ}
    (hc : 0 < c) {b : ℝ≥0∞} {K : ℝ≥0} {m : Lp ℂ ∞ (volume : Measure E)}
    (hK : ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      Integrable (fun s ↦ Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-s) (F s))) →
        ‖∫ s, Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-s) (F s))‖ₑ ≤
          K * ENNReal.ofReal (c ^ (κ / 4)) *
            eLpNorm (fun s ↦ eLpNorm (F s) b volume) ((4 / 3 : ℝ≥0) : ℝ≥0∞) volume)
    {G : ℝ → Lp ℂ 2 (volume : Measure E)} (hG : AEStronglyMeasurable G)
    (hVG : Integrable fun t ↦
      Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-(c ^ κ * t)) (G t))) :
    ‖∫ t, Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-(c ^ κ * t)) (G t))‖ₑ ≤
      K * eLpNorm (fun t ↦ eLpNorm (G t) b volume) ((4 / 3 : ℝ≥0) : ℝ≥0∞) volume := by
  have hμ : 0 < c ^ κ := Real.rpow_pos_of_pos hc κ
  have hμ' : (c ^ κ)⁻¹ ≠ 0 := inv_ne_zero hμ.ne'
  -- The substituted forcing `G ((c^κ)⁻¹ ·)`.
  have hint : Integrable fun s ↦ Lp.fourierMultiplierCLM ℂ (star m)
      (halfWavePropagator ℂ (-s) (G ((c ^ κ)⁻¹ * s))) := by
    simpa only [← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul] using hVG.comp_mul_left' hμ'
  rw [show (∫ t, Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-(c ^ κ * t)) (G t))) =
      |(c ^ κ)⁻¹| • ∫ s, Lp.fourierMultiplierCLM ℂ (star m)
        (halfWavePropagator ℂ (-s) (G ((c ^ κ)⁻¹ * s))) by
    rw [← Measure.integral_comp_mul_left]
    simp only [← mul_assoc, inv_mul_cancel₀ hμ.ne', one_mul], eNorm_smul]
  have hdil := Measure.eLpNorm_comp_inv_smul volume (fun s ↦ eLpNorm (G s) b volume) hμ.ne'
    ((4 / 3 : ℝ≥0) : ℝ≥0∞)
  simp only [smul_eq_mul, Module.finrank_self, Nat.cast_one, abs_of_pos hμ] at hdil
  refine (mul_le_mul_of_nonneg_left (hK (fun s ↦ G ((c ^ κ)⁻¹ * s))
    (hG.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_smul volume hμ')) hint)
      zero_le).trans_eq ?_
  rw [hdil, abs_inv, abs_of_pos hμ, Real.eNorm_eq_ofReal (inv_nonneg.2 hμ.le),
    show (1 : ℝ) / ((4 / 3 : ℝ≥0) : ℝ≥0∞).toReal = 3 / 4 by norm_num]
  have hconst : (c ^ κ)⁻¹ * c ^ (κ / 4) * (c ^ κ) ^ ((3 : ℝ) / 4) = 1 := by
    rw [← Real.rpow_neg hc.le, ← Real.rpow_mul hc.le, ← Real.rpow_add hc, ← Real.rpow_add hc,
      show -κ + κ / 4 + κ * (3 / 4) = 0 by ring, Real.rpow_zero]
  calc _ = K * (ENNReal.ofReal ((c ^ κ)⁻¹ * c ^ (κ / 4) * (c ^ κ) ^ ((3 : ℝ) / 4)) *
        eLpNorm (fun t ↦ eLpNorm (G t) b volume) ((4 / 3 : ℝ≥0) : ℝ≥0∞) volume) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        ring
    _ = _ := by rw [hconst, ENNReal.ofReal_one, one_mul]

/-- Undoing the time rescaling `t = c^κ s` in an `L²_t` norm costs `c^{κ/2}`:
`‖c^κ‖ C ‖h (c^κ ·)‖₂ = C c^{κ/2} ‖h‖₂`. -/
private theorem enorm_rpow_mul_eLpNorm_comp_mul_left {c κ : ℝ} (hc : 0 < c) (C : ℝ≥0∞)
    (h : ℝ → ℝ≥0∞) :
    ‖c ^ κ‖ₑ * (C * eLpNorm (fun t ↦ h (c ^ κ * t)) 2 volume) =
      C * ENNReal.ofReal (c ^ (κ / 2)) * eLpNorm h 2 volume := by
  have hμ : 0 < c ^ κ := Real.rpow_pos_of_pos hc κ
  have hsqrt : c ^ κ * ((c ^ κ)⁻¹) ^ (2⁻¹ : ℝ) = c ^ (κ / 2) := by
    rw [Real.inv_rpow hμ.le, ← Real.rpow_mul hc.le, ← Real.rpow_neg hc.le, ← Real.rpow_add hc]
    ring_nf
  have hdil := Measure.eLpNorm_comp_inv_smul volume h (inv_ne_zero hμ.ne') 2
  simp only [inv_inv, smul_eq_mul, Module.finrank_self, Nat.cast_one, ENNReal.toReal_ofNat,
    one_div, abs_inv, abs_of_pos hμ] at hdil
  rw [hdil, Real.eNorm_eq_ofReal hμ.le, ← hsqrt, ENNReal.ofReal_mul hμ.le]
  ring

variable {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- The endpoint exponent: `1 + (n - 1) / r = (n - 1) / 2` means `1 / r = 1/2 - 1/(n - 1)`. -/
private theorem toReal_inv_eq_of_endpoint {n : ℝ} (hn : 1 < n)
    (hr : 1 + (n - 1) * (r⁻¹).toReal = (n - 1) / 2) : (r⁻¹).toReal = 2⁻¹ - (n - 1)⁻¹ := by
  have : n - 1 ≠ 0 := by linarith
  field_simp
  linarith

/-- The endpoint exponent `r = 2 (n - 1) / (n - 3)` of the wave equation in dimension `n > 3`,
given by `1 + (n - 1) / r = (n - 1) / 2`, satisfies `2 ≤ r < ∞`. -/
theorem two_le_and_ne_top_of_waveEndpoint {n : ℝ} (hn : 3 < n)
    (hr : 1 + (n - 1) * (r⁻¹).toReal = (n - 1) / 2) : 2 ≤ r ∧ r ≠ (∞ : ℝ≥0∞) := by
  refine ⟨ENNReal.two_le_of_toReal_inv_le (fun h ↦ ?_) ?_, fun h ↦ ?_⟩
  · rw [h, ENNReal.inv_zero, ENNReal.toReal_top, mul_zero, add_zero] at hr
    linarith
  · rw [toReal_inv_eq_of_endpoint (by linarith) hr]
    linarith [inv_pos.2 (show (0 : ℝ) < n - 1 by linarith)]
  · rw [h, ENNReal.inv_top, ENNReal.toReal_zero, mul_zero, add_zero] at hr
    linarith

/-- The endpoint dual estimate for the rescaled family `V(t) = W₊(2^{jκ} t) Pⱼ`,
`κ = (n + 1) / (n - 1)`, with a constant independent of `j`: the abstract endpoint theorem applies
with constants that do not depend on `j`. -/
private theorem exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_mul_le
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ)
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ ψ (((2 : ℝ) ^ j)⁻¹ • ξ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
        ‖∫ t, Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ
          (-(((2 : ℝ) ^ j) ^ (((Module.finrank ℝ E : ℝ) + 1) / ((Module.finrank ℝ E : ℝ) - 1)) *
            t)) (F t))‖ₑ ≤ C * eLpNorm (fun t ↦ eLpNorm (F t) r' volume) 2 volume := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn' : 3 < n := by simp only [n]; exact_mod_cast hn
  have hn1 : 0 < n - 1 := by linarith
  -- The exponents of the abstract endpoint theorem, with `σ = (n - 1) / 2`.
  have hxp : 0 ≤ 2⁻¹ + (2 * (n - 1))⁻¹ := by positivity
  have hbinv : ((ENNReal.ofReal (2⁻¹ + (2 * (n - 1))⁻¹))⁻¹).toReal⁻¹ = 2⁻¹ + (2 * (n - 1))⁻¹ := by
    rw [ENNReal.toReal_inv, inv_inv, ENNReal.toReal_ofReal hxp]
  have hr'inv : r'.toReal⁻¹ = ((n - 1) / 2 + 1) / (2 * ((n - 1) / 2)) := by
    have h := congrArg ENNReal.toReal (ENNReal.HolderConjugate.inv_add_inv_eq_one r' r)
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 (ENNReal.HolderConjugate.ne_zero r' r))
      (ENNReal.inv_ne_top.2 (ENNReal.HolderConjugate.ne_zero r r')), ENNReal.toReal_one,
      toReal_inv_eq_of_endpoint (by linarith) hr] at h
    rw [← ENNReal.toReal_inv, show r'⁻¹.toReal = 2⁻¹ + (n - 1)⁻¹ by linarith]
    field_simp
  obtain ⟨A, hA⟩ :=
    exists_eLpNorm_halfWavePropagator_mul_comp_apply_adjoint_le_top hψ hψc hψ0 (by omega)
  obtain ⟨K, hK⟩ :=
    exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le_four hψ hψc hψ0 (by omega)
  obtain ⟨B, hB⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨C, hC⟩ := exists_enorm_setIntegral_inner_adjoint_le_of_endpoint_of_four_thirds
    (𝕜 := ℂ) (H := Lp ℂ 2 (volume : Measure E)) (E := ℂ) (μ := (volume : Measure E))
    (σ := (n - 1) / 2) (b := (ENNReal.ofReal (2⁻¹ + (2 * (n - 1))⁻¹))⁻¹) (r' := r')
    (by linarith) (by rw [hbinv]; ring) hr'inv A B.toNNReal K
  refine ⟨NNReal.sqrt C, fun j m hm F hF ↦ ?_⟩
  have hV (t : ℝ) (g : Lp ℂ 2 (volume : Measure E)) :
      ((halfWavePropagator ℂ (((2 : ℝ) ^ j) ^ ((n + 1) / (n - 1)) * t) ∘L
        Lp.fourierMultiplierCLM ℂ m)†) g = Lp.fourierMultiplierCLM ℂ (star m)
          (halfWavePropagator ℂ (-(((2 : ℝ) ^ j) ^ ((n + 1) / (n - 1)) * t)) g) :=
    adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply _ _ _
  have h := hC (fun t ↦ halfWavePropagator ℂ (((2 : ℝ) ^ j) ^ ((n + 1) / (n - 1)) * t) ∘L
      Lp.fourierMultiplierCLM ℂ m)
    (fun t ↦ by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal
        (norm_halfWavePropagator_comp_fourierMultiplierCLM_le hB0 (hm.mono fun ξ h ↦ h ▸ hB _) _))
    (hA j m hm)
    (fun G hG hVG ↦ by
      simp_rw [hV] at hVG ⊢
      exact enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_mul_le
        (zpow_pos two_pos j) (hK j m hm) hG hVG)
    (fun G hG ↦ by
      simp_rw [hV, halfWavePropagator_def]
      exact (Lp.fourierMultiplierCLM ℂ (star m)).continuous.comp_aestronglyMeasurable
        (aestronglyMeasurable_phasePropagator_apply _
          (continuous_const.mul continuous_id).neg.aestronglyMeasurable hG))
    Set.univ MeasurableSet.univ F F hF hF
  simp only [hV, Measure.restrict_univ] at h
  -- `TT*` turns the bound on the pairings over the whole plane into the dual estimate.
  refine enorm_integral_le_sqrt_mul_of_enorm_integral_inner_le (𝕜 := ℂ)
    ((Lp.fourierMultiplierCLM ℂ (star m)).integrable_comp ?_) h
  simp_rw [halfWavePropagator_def]
  exact integrable_phasePropagator_apply _
    (continuous_const.mul continuous_id).neg.aestronglyMeasurable hF

/-! ### The endpoint estimates -/

/-- **The dual endpoint Strichartz estimate for the frequency-localized wave equation.** Let `E`
have dimension `n ≥ 4`, let `ψ` be smooth, compactly supported and vanish near the origin, and let
`r` be the endpoint exponent, `1 + (n - 1) / r = (n - 1) / 2`, with Hölder conjugate `r'`. Put
`γ = n / 2 - n / r - 1 / 2`. There is `C` such that for every `j ∈ ℤ`, every multiplier `Pⱼ` with
symbol `ψ (2^{-j} ·)` and every integrable `F : ℝ → L²(E)`,

`‖∫ Pⱼ* W₊(-s) F(s) ds‖₂ ≤ C 2^{jγ} ‖F‖_{L²_t L^{r'}_x}`. -/
theorem exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le_of_endpoint
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ)
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ ψ (((2 : ℝ) ^ j)⁻¹ • ξ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
        ‖∫ s, Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-s) (F s))‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 1 / 2)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) 2 volume := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_mul_le
    (r' := r') hψ hψc hψ0 hn hr
  refine ⟨C, fun j m hm F hF ↦ ?_⟩
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn1 : 0 < n - 1 := by
    have : (3 : ℝ) < n := by simp only [n]; exact_mod_cast hn
    linarith
  have hμ : 0 < ((2 : ℝ) ^ j) ^ ((n + 1) / (n - 1)) := by positivity
  have hγ : n / 2 - n * (r⁻¹).toReal - 1 / 2 = (n + 1) / (n - 1) / 2 := by
    rw [toReal_inv_eq_of_endpoint (by linarith) hr]
    field_simp
    ring
  -- Substitute `s = 2^{jκ} t`.
  rw [show (∫ s, Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-s) (F s))) =
      ((2 : ℝ) ^ j) ^ ((n + 1) / (n - 1)) • ∫ t, Lp.fourierMultiplierCLM ℂ (star m)
        (halfWavePropagator ℂ (-(((2 : ℝ) ^ j) ^ ((n + 1) / (n - 1)) * t))
          (F (((2 : ℝ) ^ j) ^ ((n + 1) / (n - 1)) * t))) by
    rw [Measure.integral_comp_mul_left (fun s ↦ Lp.fourierMultiplierCLM ℂ (star m)
      (halfWavePropagator ℂ (-s) (F s))), smul_smul, abs_inv, abs_of_pos hμ,
      mul_inv_cancel₀ hμ.ne', one_smul], eNorm_smul, hγ]
  calc _ ≤ ‖((2 : ℝ) ^ j) ^ ((n + 1) / (n - 1))‖ₑ * (C * eLpNorm (fun t ↦ eLpNorm
        (F (((2 : ℝ) ^ j) ^ ((n + 1) / (n - 1)) * t)) r' volume) 2 volume) := by
        gcongr
        exact hC j m hm _ (hF.comp_mul_left' hμ.ne')
    _ = _ := enorm_rpow_mul_eLpNorm_comp_mul_left (zpow_pos two_pos j) C
        (fun s ↦ eLpNorm (F s) r' volume)

/-- **The endpoint Strichartz estimate for the frequency-localized wave equation**, in weak form.
Let `E` have dimension `n ≥ 4`, let `ψ` be smooth, compactly supported and vanish near the origin,
and let `r` be the endpoint exponent, `1 + (n - 1) / r = (n - 1) / 2`, with Hölder conjugate `r'`.
Put `γ = n / 2 - n / r - 1 / 2`. There is `C` such that for every `j ∈ ℤ`, every multiplier `Pⱼ`
with symbol `ψ (2^{-j} ·)`, every `f ∈ L²(E)` and every integrable `G : ℝ → L²(E)`,

`|∫ ⟪W₊(t) Pⱼ f, G(t)⟫ dt| ≤ C 2^{jγ} ‖f‖₂ ‖G‖_{L²_t L^{r'}_x}`.

This is `‖W₊(t) Pⱼ f‖_{L²_t L^r_x} ≤ C 2^{jγ} ‖f‖₂` tested against `G`. -/
theorem exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le_of_endpoint
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ)
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ ψ (((2 : ℝ) ^ j)⁻¹ • ξ)) →
      ∀ (f : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)), Integrable G →
        ‖∫ t, ⟪halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f), G t⟫_ℂ‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 1 / 2)) * ‖f‖ₑ *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) 2 volume := by
  obtain ⟨C, hC⟩ :=
    exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le_of_endpoint (r' := r') hψ
      hψc hψ0 hn hr
  refine ⟨C, fun j m hm f G hG ↦ ?_⟩
  have hPG : Integrable fun t ↦
      Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-t) (G t)) :=
    (Lp.fourierMultiplierCLM ℂ (star m)).integrable_comp
      (integrable_phasePropagator_apply _ continuous_neg.aestronglyMeasurable hG)
  simp_rw [← ContinuousLinearMap.comp_apply (halfWavePropagator ℂ _),
    ← ContinuousLinearMap.adjoint_inner_right,
    adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply]
  rw [integral_inner hPG]
  calc _ ≤ ‖f‖ₑ * ‖∫ t, Lp.fourierMultiplierCLM ℂ (star m) (halfWavePropagator ℂ (-t) (G t))‖ₑ :=
        eNorm_inner_le_eNorm _ _
    _ ≤ ‖f‖ₑ * (C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 1 / 2)) *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) 2 volume) := by
        gcongr
        exact hC j m hm G hG
    _ = _ := by ring

end TauCeti

/-! ### The Littlewood–Paley blocks -/

namespace ContDiffBump

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (φ : ContDiffBump (0 : E)) {r r' : ℝ≥0∞}
  [r'.HolderConjugate r]

/-- **The dual endpoint Strichartz estimate for the frequency-localized wave equation**, for the
Littlewood–Paley blocks. Let `E` have dimension `n ≥ 4`, let `Pⱼ` be the `L²` Fourier multiplier
with the Littlewood–Paley symbol `ψⱼ` built from `φ`, and let `r` be the endpoint exponent,
`1 + (n - 1) / r = (n - 1) / 2`, with Hölder conjugate `r'`. Put `γ = n / 2 - n / r - 1 / 2`.
There is `C` such that for every `j ∈ ℤ` and every integrable `F : ℝ → L²(E)`,

`‖∫ W₊(-s) Pⱼ F(s) ds‖₂ ≤ C 2^{jγ} ‖F‖_{L²_t L^{r'}_x}`.

This is the case `ψ = ψ₀` of
`TauCeti.exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le_of_endpoint`. -/
theorem exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le_of_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
        ‖∫ s, halfWavePropagator ℂ (-s) (Lp.fourierMultiplierCLM ℂ m (F s))‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) 2 volume := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_fourierMultiplierCLM_halfWavePropagator_neg_le_of_endpoint
    (r' := r') (φ.contDiff_ofReal_littlewoodPaley 0) (φ.hasCompactSupport_ofReal_littlewoodPaley 0)
    (φ.zero_notMem_tsupport_ofReal_littlewoodPaley 0) hn hr
  refine ⟨C, fun j m hm F hF ↦ ?_⟩
  simpa only [Lp.star_eq_self_of_ae_eq_ofReal hm, fourierMultiplierCLM_halfWavePropagator_apply,
    one_div] using hC j m (ae_eq_littlewoodPaley_zero_comp_smul hm) F hF

/-- **The endpoint Strichartz estimate for the frequency-localized wave equation**, in weak form,
for the Littlewood–Paley blocks. Let `E` have dimension `n ≥ 4`, let `Pⱼ` be the `L²` Fourier
multiplier with the Littlewood–Paley symbol `ψⱼ` built from `φ`, and let `r` be the endpoint
exponent, `1 + (n - 1) / r = (n - 1) / 2`, with Hölder conjugate `r'`. Put
`γ = n / 2 - n / r - 1 / 2`. There is `C` such that for every `j ∈ ℤ`, every `f ∈ L²(E)` and
every integrable `G : ℝ → L²(E)`,

`|∫ ⟪W₊(t) Pⱼ f, G(t)⟫ dt| ≤ C 2^{jγ} ‖f‖₂ ‖G‖_{L²_t L^{r'}_x}`.

This is the case `ψ = ψ₀` of
`TauCeti.exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le_of_endpoint`. -/
theorem exists_enorm_integral_inner_halfWavePropagator_littlewoodPaley_le_of_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (f : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)), Integrable G →
        ‖∫ t, ⟪halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f), G t⟫_ℂ‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) * ‖f‖ₑ *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) 2 volume := by
  obtain ⟨C, hC⟩ :=
    exists_enorm_integral_inner_halfWavePropagator_fourierMultiplierCLM_le_of_endpoint (r' := r')
      (φ.contDiff_ofReal_littlewoodPaley 0) (φ.hasCompactSupport_ofReal_littlewoodPaley 0)
      (φ.zero_notMem_tsupport_ofReal_littlewoodPaley 0) hn hr
  refine ⟨C, fun j m hm f G hG ↦ ?_⟩
  simpa only [one_div] using hC j m (ae_eq_littlewoodPaley_zero_comp_smul hm) f G hG

/-- **The endpoint Strichartz estimate for the frequency-localized wave equation** in mixed norm,
for the Littlewood–Paley blocks. Let `E` have dimension `n ≥ 4`, let `Pⱼ` be the `L²` Fourier
multiplier with the Littlewood–Paley symbol `ψⱼ` built from `φ`, and let `r` be the endpoint
exponent, `1 + (n - 1) / r = (n - 1) / 2`. Put `γ = n / 2 - n / r - 1 / 2`. There is `C` such that
for every `j ∈ ℤ` and every `f ∈ L²(E)`,

`‖W₊(t) Pⱼ f‖_{L²_t L^r_x} ≤ C 2^{jγ} ‖f‖₂`. -/
theorem exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal = ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f)) r
            volume) 2 volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) * ‖f‖ₑ := by
  obtain ⟨hr2, -⟩ := two_le_and_ne_top_of_waveEndpoint (by exact_mod_cast hn) hr
  -- Test against `L^{r'}` with `r'` the Hölder conjugate of `r`.
  have := ENNReal.HolderConjugate.inv_one_sub_inv' (one_le_two.trans hr2)
  obtain ⟨C, hC⟩ := φ.exists_enorm_integral_inner_halfWavePropagator_littlewoodPaley_le_of_endpoint
    (r' := (1 - r⁻¹)⁻¹) hn hr
  exact ⟨C, fun j m hm f ↦ (continuous_phasePropagator_apply _ _).aestronglyMeasurable
    |>.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le (q' := 2) (r' := (1 - r⁻¹)⁻¹)
      ENNReal.ofNat_ne_top hr2 fun G hG _ ↦ hC j m hm f G hG⟩

end ContDiffBump

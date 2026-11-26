/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.Analysis.SpecialFunctions.Beta.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic
import TauCeti.NumberTheory.ModularForms.DedekindEta.Basic
import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation

/-!
# Kronecker's first limit formula

For `τ` in the upper half-plane, the real Epstein zeta function of the lattice `ℤ τ + ℤ` is

`E(τ, s) = ∑_{(m, n) ≠ (0, 0)} (Im τ / |m τ + n|²) ^ s`,

which converges for `s > 1`. Kronecker's first limit formula gives its expansion at the pole:

`E(τ, s) = π / (s - 1) + π (2 γ + log π - logPeriod τ) + o(1)` as `s → 1⁺`,

where `γ` is Euler's constant and `logPeriod τ = log (4 π Im τ |η(τ)|⁴)` is the logarithmic
period of the lattice `ℤ τ + ℤ`. Equivalently, the classical form is
`E(τ, s) = π / (s - 1) + 2 π (γ - log 2 - log (√(Im τ) |η(τ)|²)) + o(1)`.

## Main definitions and results

* `UpperHalfPlane.logPeriod`: the logarithmic period `log (4 π Im τ |η(τ)|⁴)`.
* `UpperHalfPlane.logPeriod_smul`: it is invariant under `SL(2, ℤ)`, so it only depends on the
  homothety class of the lattice `ℤ τ + ℤ`.
* `UpperHalfPlane.epsteinZeta`: the real Epstein zeta function `E(τ, s)` of `ℤ τ + ℤ`.
* `UpperHalfPlane.hasSum_epsteinZeta`: the series `E(τ, s)` converges for `s > 1`.
* `UpperHalfPlane.tendsto_epsteinZeta_sub`: **Kronecker's first limit formula**, the constant
  term of `E(τ, s)` at `s = 1`.
* `UpperHalfPlane.tendsto_sub_one_mul_epsteinZeta`: its residue `π`.

## Implementation notes

Only real `s > 1` occur; the Epstein function is not continued analytically. Each row
`∑ₙ |m τ + n| ^ (-2 s)`, `m ≥ 1`, is compared with the integral `∫ |m τ + t| ^ (-2 s) dt`, which
is Euler's beta integral `√π Γ(s - 1/2) / Γ(s) · (m Im τ) ^ (1 - 2 s)`. The differences, the mean
errors, are bounded by the mean value theorem, so their sum is continuous on `[1, 2]`, while the
integrals sum to a multiple of `ζ(2 s - 1)`, which has a simple pole at `1`. At `s = 1` the mean
errors of a row are computed through the partial fraction expansion of the cotangent, and their
sum is `-2 π / Im τ · log |∏ (1 - qⁿ)|`, `q = e^{2 π i τ}`.

## References

The statements and proofs are adapted from the file `src/Lib/CM/KroneckerLimit.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC), in particular
`New.kronecker_limit`, `New.sub_one_mul_tsum_norm_mul_add_rpow`, `New.tsum_meanError_row_one`,
`New.tsum_meanError_one` and `New.hasDerivAt_betaFactor`. There the formula is stated for an
arbitrary lattice with its discriminant; here it is stated for `ℤ τ + ℤ` with the Dedekind eta
function, and Euler's beta integral is Tau Ceti's `TauCeti.integral_one_add_sq_div_rpow`.

* C. L. Siegel, *Lectures on Advanced Analytic Number Theory*, Tata Institute (1961),
  Chapter I, Theorem 1.
* F. Chamizo, *A simple evaluation of a theta value, the Kronecker limit formula and a formula of
  Ramanujan*, Ramanujan J. (2022), Proposition 3.1.
-/

public section

noncomputable section

open Complex Filter Function MeasureTheory Real Set Topology intervalIntegral
open ModularForm hiding eta
open scoped ModularForm MatrixGroups

namespace UpperHalfPlane

/-! ### The logarithmic period -/

/-- The **logarithmic period** `log (4 π Im τ |η(τ)|⁴)` of the lattice `ℤ τ + ℤ`. For a lattice
`Λ = ℤ τ + ℤ` it equals `log (area (ℂ / Λ) / π) + log |Δ(Λ)| / 6`, `Δ` the modular discriminant,
and it only depends on the homothety class of `Λ` (`UpperHalfPlane.logPeriod_smul`). -/
def logPeriod (τ : ℍ) : ℝ :=
  Real.log (4 * π * τ.im * ‖η (τ : ℂ)‖ ^ 4)

/-- The defining formula of `UpperHalfPlane.logPeriod`. -/
theorem logPeriod_def (τ : ℍ) : logPeriod τ = Real.log (4 * π * τ.im * ‖η (τ : ℂ)‖ ^ 4) :=
  (rfl)

/-- The logarithmic period through the Euler product of `η`:
`logPeriod τ = log (4 π) + log (Im τ) - π Im τ / 3 + 4 log |∏ (1 - qⁿ)|`, `q = e^{2 π i τ}`. -/
theorem logPeriod_eq_log_tprod (τ : ℍ) :
    logPeriod τ = Real.log (4 * π) + Real.log τ.im - π * τ.im / 3 +
      4 * Real.log ‖∏' n : ℕ, (1 - eta_q n (τ : ℂ))‖ := by
  have hP : ∏' n : ℕ, (1 - eta_q n (τ : ℂ)) ≠ 0 := eta_tprod_ne_zero τ.im_pos
  have hq : ‖cexp (2 * π * Complex.I * (τ : ℂ) / 24)‖ ^ 4 = Real.exp (-(π * τ.im / 3)) := by
    rw [norm_exp, ← Real.exp_natCast_mul]
    congr 1
    simp only [div_ofNat_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_im, Complex.I_re,
      Complex.I_im, coe_re, coe_im]
    ring
  have hη : η (τ : ℂ) =
      cexp (2 * π * Complex.I * (τ : ℂ) / 24) * ∏' n : ℕ, (1 - eta_q n (τ : ℂ)) := by
    simp [TauCeti.ModularForm.eta_eq_exp_mul_tprod, eta_q_eq_pow]
  have := norm_pos_iff.mpr hP
  have := τ.im_pos
  rw [logPeriod, hη, norm_mul, mul_pow, hq, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (Real.exp_pos _).ne' (by positivity),
    Real.log_exp, Real.log_pow]
  push_cast
  ring

/-- The logarithmic period is invariant under `SL(2, ℤ)`: replacing `τ` by `γ τ` replaces the
lattice `ℤ τ + ℤ` by a homothetic one. -/
theorem logPeriod_smul (γ : SL(2, ℤ)) (τ : ℍ) : logPeriod (γ • τ) = logPeriod τ := by
  have hd : denom γ τ ≠ 0 := denom_ne_zero γ τ
  have hden : (γ 1 0 : ℂ) * τ + γ 1 1 = denom γ τ := by simp [denom]
  have hη : ‖η ((γ • τ : ℍ) : ℂ)‖ ^ 4 = ‖denom γ τ‖ ^ 2 * ‖η (τ : ℂ)‖ ^ 4 := by
    rw [TauCeti.ModularForm.eta_smul, norm_mul, norm_mul, TauCeti.ModularForm.norm_etaMultiplier,
      one_mul, mul_pow, hden, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, ← norm_pow, Complex.sq_sqrt]
  rw [logPeriod, logPeriod, ModularGroup.im_smul_eq_div_normSq, hη, Complex.normSq_eq_norm_sq]
  congr 1
  field_simp

/-! ### The real Epstein zeta function of `ℤ τ + ℤ` -/

/-- The **real Epstein zeta function** of the lattice `ℤ τ + ℤ`, normalised by `Im τ`:
`E(τ, s) = ∑_{(m, n) ≠ (0, 0)} (Im τ / |m τ + n|²) ^ s` for real `s`. The series converges for
`s > 1` (`UpperHalfPlane.hasSum_epsteinZeta`); the term at `(0, 0)` is `0 ^ s = 0` for `s ≠ 0`. -/
def epsteinZeta (τ : ℍ) (s : ℝ) : ℝ :=
  ∑' p : ℤ × ℤ, (τ.im / ‖(p.1 : ℂ) * τ + p.2‖ ^ 2) ^ s

/-- The defining series of `UpperHalfPlane.epsteinZeta`. -/
theorem epsteinZeta_def (τ : ℍ) (s : ℝ) :
    epsteinZeta τ s = ∑' p : ℤ × ℤ, (τ.im / ‖(p.1 : ℂ) * τ + p.2‖ ^ 2) ^ s :=
  (rfl)

/-- For `a > 2`, `|a - b| ≤ 1` and `1 ≤ s ≤ 2`, the values of `t ↦ t^(-2s)` at `a` and `b` differ
by at most `4 (a / 2)^(-3)`, by the mean value theorem. -/
private theorem norm_rpow_sub_rpow_le {a b s : ℝ} (ha : 2 < a) (hab : |a - b| ≤ 1)
    (hs : s ∈ Icc 1 2) : ‖a ^ (-2 * s) - b ^ (-2 * s)‖ ≤ 4 * (2⁻¹ * a) ^ (-3 : ℝ) := by
  obtain ⟨hs_one, hs_two⟩ := hs
  have h_pos (t : ℝ) (ht : t ∈ Ici (2⁻¹ * a)) : 0 < t := by linarith [mem_Ici.1 ht]
  have h_deriv (t : ℝ) (ht : t ∈ Ici (2⁻¹ * a)) :
      ‖-2 * s * t ^ (-2 * s - 1)‖ ≤ 4 * (2⁻¹ * a) ^ (-3 : ℝ) := by
    have h_pow : t ^ (-2 * s - 1) ≤ (2⁻¹ * a) ^ (-3 : ℝ) :=
      (rpow_le_rpow_of_nonpos (by linarith) ht (by linarith)).trans
        (rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
    rw [norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos (h_pos t ht) _)]
    exact mul_le_mul (abs_le.2 ⟨by linarith, by linarith⟩) h_pow
      (rpow_pos_of_pos (h_pos t ht) _).le (by norm_num)
  have hb_mem : b ∈ Ici (2⁻¹ * a) := mem_Ici.2 (by linarith [le_abs_self (a - b)])
  calc ‖a ^ (-2 * s) - b ^ (-2 * s)‖
    _ ≤ 4 * (2⁻¹ * a) ^ (-3 : ℝ) * ‖a - b‖ :=
      (convex_Ici (2⁻¹ * a)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun t ↦ t ^ (-2 * s))
        (fun t ht ↦ (hasDerivAt_rpow_const (.inl (h_pos t ht).ne')).hasDerivWithinAt) h_deriv
        hb_mem (mem_Ici.2 (by linarith))
    _ ≤ 4 * (2⁻¹ * a) ^ (-3 : ℝ) := mul_le_of_le_one_right (by positivity) hab

/-- The factor `√π Γ(s - 1/2) / Γ(s) * y^(1 - 2s)`. For `s > 1/2` it is the value of Euler's beta
integral `∫ |z + t|^(-2s) dt` over the real line when `Im z = y > 0`. -/
private def betaFactor (y s : ℝ) : ℝ :=
  √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * y ^ (1 - 2 * s)

private theorem betaFactor_one (y : ℝ) : betaFactor y 1 = π / y := by
  norm_num [betaFactor, Real.Gamma_one_half_eq, rpow_neg_one, pi_pos.le, div_eq_mul_inv]

/-- The derivative at `s = 1` of the value `√π Γ(s - 1/2) / Γ(s) * y^(1 - 2s)` of Euler's beta
integral; the Euler constants from `Γ'(1/2)` and `Γ'(1)` cancel. -/
private theorem hasDerivAt_betaFactor {y : ℝ} (hy : 0 < y) :
    HasDerivAt (betaFactor y) (-2 * π / y * (Real.log 2 + Real.log y)) 1 := by
  have hΓ : HasDerivAt (fun s : ℝ ↦ Real.Gamma (s - 1 / 2))
      (-√π * (eulerMascheroniConstant + 2 * Real.log 2)) 1 :=
    HasDerivAt.comp_sub_const 1 (1 / 2) (by simpa only [sub_half] using
      Real.hasDerivAt_Gamma_one_half)
  have h_pow : HasDerivAt (fun x : ℝ ↦ y ^ (1 - 2 * x)) (Real.log y * -2 * y ^ ((1 : ℝ) - 2 * 1))
    1 := ((hasDerivAt_const_mul (x := 1) 2).const_sub 1).const_rpow hy
  unfold betaFactor
  refine (((hΓ.const_mul √π).div hasDerivAt_Gamma_one (by simp)).mul h_pow).congr_deriv ?_
  norm_num [Real.Gamma_one_half_eq, rpow_neg_one, ← mul_assoc, Real.mul_self_sqrt, pi_pos.le]
  field

/-- The powers `q^(j+1)` of `q = exp (2 π i τ)` have modulus less than one. -/
private theorem norm_eta_q_lt_one (τ : ℍ) (j : ℕ) : ‖eta_q j (τ : ℂ)‖ < 1 := by
  simpa [eta_q] using pow_lt_one₀ (norm_nonneg _) (norm_qParam_lt_one 1 τ) j.succ_ne_zero

/-- For `q = exp (2 π i τ)`, so that `eta_q m τ = q^(m+1)`, the double series
`∑ q^((m+1)(j+1)) / (m+1)` converges absolutely, and it is minus a logarithm of
`∏ (1 - q^(j+1))`. -/
private theorem tprod_one_sub_eta_q (τ : ℍ) :
    let c (m j : ℕ) : ℂ := eta_q m (τ : ℂ) ^ j.succ / ofReal m.succ
    Summable (uncurry c) ∧
      ∏' j : ℕ, (1 - eta_q j (τ : ℂ)) = cexp (-∑' m : ℕ, ∑' j : ℕ, c m j) := by
  intro c
  have hc : Summable (uncurry c) := by
    refine .of_norm_bounded ((summable_prod_mul_pow 0
      (norm_eta_q_lt_one τ 0)).norm.comp_injective
        (Nat.succPNat_injective.prodMap Nat.succPNat_injective)) fun ⟨a, b⟩ ↦ ?_
    simp only [pow_zero, one_mul, norm_pow, comp_apply, Prod.map_fst, Nat.succPNat_coe,
      Nat.succ_eq_add_one, Prod.map_snd, uncurry_apply_pair, c, norm_div, eta_q, ← pow_mul,
      zero_add, one_mul]
    refine div_le_self (by positivity) ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast Nat.succ_pos a
  have h_log (j : ℕ) : ∑' m : ℕ, c m j = -Complex.log (1 - eta_q j (τ : ℂ)) := by
    simp [c, (hasSum_taylorSeries_neg_log' (norm_eta_q_lt_one τ _)).tsum_eq, pow_right_comm]
  have h_sum : HasSum (fun j : ℕ ↦ Complex.log (1 - eta_q j (τ : ℂ)))
      (-∑' m : ℕ, ∑' j : ℕ, c m j) := by
    rw [← hc.tsum_comm]
    exact hc.prod_symm.prod.hasSum.neg.congr_fun (by simp [h_log])
  exact ⟨hc, (hasProd_of_hasSum_log (one_sub_eta_q_ne_zero · τ.im_pos) h_sum).tprod_eq⟩

/-- The series `∑ |m τ + n| ^ r` over `(m, n) ∈ ℤ²` converges for `r < -2`; its term at `(0, 0)`
is `0`. -/
private theorem summable_norm_mul_add_rpow (τ : ℍ) {r : ℝ} (hr : r < -2) :
    Summable fun p : ℤ × ℤ ↦ ‖p.1 * (τ : ℂ) + p.2‖ ^ r := by
  have h_vec : Summable fun v : Fin 2 → ℤ ↦ ‖v 0 * (τ : ℂ) + v 1‖ ^ (- -r) :=
    .of_nonneg_of_le (fun _ ↦ by positivity)
      (EisensteinSeries.summand_bound τ (by linarith))
      ((EisensteinSeries.summable_one_div_norm_rpow (by linarith)).mul_left _)
  simpa [comp_def] using (finTwoArrowEquiv ℤ).symm.summable_iff.2 h_vec

/-- The term `|m τ + n + u|^(-2s)`, for `p = (m, n)` and a real shift `u`. -/
private def shiftedTerm (τ : ℍ) (p : ℕ+ × ℤ) (s u : ℝ) : ℝ :=
  ‖p.1 * (τ : ℂ) + (ofReal u + p.2)‖ ^ (-2 * s)

/-- The term `|m τ + n|^(-2s)` minus the mean of `|m τ + n + u|^(-2s)` over `u ∈ [0, 1]`. -/
private def meanError (τ : ℍ) (p : ℕ+ × ℤ) (s : ℝ) : ℝ :=
  ∫ u in 0..1, shiftedTerm τ p s 0 - shiftedTerm τ p s u

private theorem continuous_uncurry_shiftedTerm (τ : ℍ) (p : ℕ+ × ℤ) :
    Continuous (uncurry (shiftedTerm τ p)) :=
  .rpow (by fun_prop) (by fun_prop) fun _ ↦ .inl ((im_le_norm _).trans_lt' (by simp [τ.im_pos])).ne'

private theorem continuous_meanError (τ : ℍ) (p : ℕ+ × ℤ) : Continuous (meanError τ p) := by
  have := continuous_uncurry_shiftedTerm τ p
  unfold meanError
  fun_prop

/-- The series of the errors `meanError τ p s` converges uniformly for `s ∈ [1, 2]`. -/
private theorem tendstoUniformlyOn_sum_meanError (τ : ℍ) :
    TendstoUniformlyOn (fun (A : Finset (ℕ+ × ℤ)) (s : ℝ) ↦ ∑ p ∈ A, meanError τ p s)
      (fun s : ℝ ↦ ∑' p : ℕ+ × ℤ, meanError τ p s) .atTop (Icc 1 2) := by
  -- When `|m τ + n| > 2` (all but finitely many terms), the error is at most
  -- `4 (|m τ + n| / 2)^(-3)`.
  let w (p : ℕ+ × ℤ) (u : ℝ) : ℝ := ‖p.1 * (τ : ℂ) + (ofReal u + p.2)‖
  have h_major : Summable fun p : ℕ+ × ℤ ↦ (2⁻¹ * w p 0) ^ (-3 : ℝ) := by
    refine (((summable_norm_mul_add_rpow τ (r := -3) (by norm_num)).comp_injective
      ((Nat.cast_injective.comp PNat.coe_injective).prodMap injective_id)).mul_left
        ((2⁻¹ : ℝ) ^ (-3 : ℝ))).congr fun p ↦ ?_
    rw [mul_rpow (by norm_num) (norm_nonneg _)]
    simp
  have h_bound (p : ℕ+ × ℤ) (hp : (2⁻¹ * w p 0) ^ (-3 : ℝ) < 1) (s : ℝ)
      (hs : s ∈ Icc (1 : ℝ) 2) : ‖meanError τ p s‖ ≤ 4 * (2⁻¹ * w p 0) ^ (-3 : ℝ) * |1 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu ↦ ?_
    have h_far : 2 < w p 0 := by
      have h_pos : 0 < w p 0 := (im_le_norm _).trans_lt' (by simp [τ.im_pos])
      by_contra h_near
      exact hp.not_ge (one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity) (by linarith)
        (by norm_num))
    have h_close : |w p 0 - w p u| ≤ 1 :=
      (abs_norm_sub_norm_le _ _).trans (by simpa using (by grind [abs_le] : |u| ≤ 1))
    exact norm_rpow_sub_rpow_le h_far h_close hs
  exact tendstoUniformlyOn_tsum_of_cofinite_eventually ((h_major.mul_left 4).mul_right _)
    ((h_major.tendsto_cofinite_zero.eventually_lt_const one_pos).mono h_bound)

private theorem summable_meanError (τ : ℍ) {s : ℝ} (hs : s ∈ Icc (1 : ℝ) 2) :
    Summable fun p : ℕ+ × ℤ ↦ meanError τ p s :=
  HasSum.summable ((tendstoUniformlyOn_sum_meanError τ).tendsto_at hs)

private theorem continuousOn_tsum_meanError (τ : ℍ) :
    ContinuousOn (fun s : ℝ ↦ ∑' p : ℕ+ × ℤ, meanError τ p s) (Icc 1 2) :=
  (tendstoUniformlyOn_sum_meanError τ).continuousOn (.of_forall fun _ ↦
    (continuous_finsetSum _ fun p _ ↦ continuous_meanError τ p).continuousOn)

/-- The term `|m τ + t|^(-2s)` as a rescaled Cauchy kernel in `t`, with `m τ = a + b i`. -/
private theorem shiftedTerm_eq (τ : ℍ) (m : ℕ+) (s t : ℝ) :
    shiftedTerm τ (m, 0) s t = ((m * τ.im) ^ 2) ^ (-s) *
      (1 + (t + m * τ.re) ^ 2 / (m * τ.im) ^ 2) ^ (-s) := by
  rw [← mul_rpow (by positivity) (by positivity), mul_add, mul_one,
    mul_div_cancel₀ _ (by positivity), shiftedTerm, show -2 * s = 2 * -s by ring,
    rpow_mul (norm_nonneg _), rpow_two, Complex.sq_norm, normSq_apply]
  congr 1
  simp only [Int.cast_zero, add_zero, mul_re, natCast_re, coe_re, natCast_im, coe_im, zero_mul,
    sub_zero, add_re, ofReal_re, mul_im, add_im, ofReal_im]
  ring

/-- Euler's beta integral along the row `m`: `∫ |m τ + t|^(-2s) dt` over the real line equals
`betaFactor (Im τ) s * m ^ (1 - 2s)`, and the integrand is integrable. -/
private theorem integrable_shiftedTerm_and_integral_eq (τ : ℍ) {s : ℝ} (hs : 1 / 2 < s)
    (m : ℕ+) : Integrable (shiftedTerm τ (m, 0) s) ∧
      ∫ t : ℝ, shiftedTerm τ (m, 0) s t = betaFactor τ.im s * m ^ (1 - 2 * s) := by
  have hb : 0 < (m : ℝ) * τ.im := mul_pos (by positivity) τ.im_pos
  have hν : 0 < ((m : ℝ) * τ.im) ^ 2 := by positivity
  have h_pow : τ.im ^ (1 - 2 * s) * (m : ℝ) ^ (1 - 2 * s) =
      ((m : ℝ) * τ.im) ^ ((2 : ℕ) * -s) * ((m : ℝ) * τ.im) := by
    rw [← mul_rpow τ.im_pos.le (by positivity), mul_comm τ.im, ← rpow_add_one hb.ne']
    push_cast
    ring_nf
  rw [show shiftedTerm τ (m, 0) s = _ from funext (shiftedTerm_eq τ m s)]
  refine ⟨((TauCeti.integrable_one_add_sq_div_rpow hν hs).comp_add_right _).const_mul _, ?_⟩
  rw [MeasureTheory.integral_const_mul, integral_add_right_eq_self
    (fun t ↦ (1 + t ^ 2 / ((m : ℝ) * τ.im) ^ 2) ^ (-s)), TauCeti.integral_one_add_sq_div_rpow hν hs,
    ProbabilityTheory.beta, Real.Gamma_one_half_eq, add_sub_cancel, Real.sqrt_sq hb.le, betaFactor,
    ← rpow_natCast, ← rpow_mul hb.le, mul_assoc _ (τ.im ^ _), h_pow]
  ring

/-- The row `∑ n, |m τ + n|^(-2s)` is the sum of its errors `meanError τ (m, n) s` plus the beta
integral `betaFactor (Im τ) s * m ^ (1 - 2s)`. -/
private theorem hasSum_shiftedTerm (τ : ℍ) {s : ℝ} (hs : s ∈ Icc (1 : ℝ) 2) (m : ℕ+) :
    HasSum (fun n : ℤ ↦ shiftedTerm τ (m, n) s 0)
      (∑' n : ℤ, meanError τ (m, n) s + betaFactor τ.im s * m ^ (1 - 2 * s)) := by
  -- Cutting `ℝ` into unit intervals turns the beta integral into the sum of the means.
  obtain ⟨h_integrable, h_integral⟩ :=
    integrable_shiftedTerm_and_integral_eq τ (one_half_lt_one.trans_le hs.1) m
  have h_cut : HasSum (fun n : ℤ ↦ ∫ u in 0..1, shiftedTerm τ (m, n) s u)
      (betaFactor τ.im s * m ^ (1 - 2 * s)) := by
    rw [← h_integral]
    simpa [shiftedTerm] using h_integrable.hasSum_intervalIntegral_comp_add_int
  refine (((summable_meanError τ hs).prod_factor m).hasSum.add h_cut).congr_fun fun n ↦ ?_
  rw [meanError, intervalIntegral.integral_sub intervalIntegrable_const
    (((continuous_uncurry_shiftedTerm τ (m, n)).uncurry_left s).intervalIntegrable 0 1)]
  simp

/-- Fix the row `m + 1`. The errors `meanError τ (m + 1, n) 1` are `|(m+1) τ + n|^(-2)` minus the
mean of `|(m+1) τ + n + u|^(-2)` over `u ∈ [0, 1]`. Their sum over `n : ℤ` is `2 π / Im τ` times
the real part of `∑ j, q^((m+1)(j+1)) / (m+1)`, where `q = exp (2 π i τ)`, so that
`eta_q m τ = q^(m+1)`. -/
private theorem tsum_meanError_row_one (τ : ℍ) (m : ℕ) :
    ∑' n : ℤ, meanError τ (m.succPNat, n) 1 =
      2 * π / τ.im * (∑' j : ℕ, eta_q m (τ : ℂ) ^ j.succ / ofReal m.succ).re := by
  -- For `z = (m+1) τ`, `im (1 / (z - n) + 1 / (z + n)) = -im z * (|z - n|⁻² + |z + n|⁻²)`, so
  -- `-im z` times the row is the imaginary part of the partial fractions of `π cot (π z)`.
  have hy := τ.im_pos
  let z : ℍ := ⟨m.succ * (τ : ℂ), by simpa [-Nat.cast_add] using hy⟩
  let F (n : ℤ) : ℝ := shiftedTerm τ (m.succPNat, n) 1 0
  let S : ℝ := ∑' n : ℤ, meanError τ (m.succPNat, n) 1
  have h_row : HasSum F (S + π / τ.im * m.succPNat ^ (1 - 2 * 1 : ℝ)) := by
    rw [← betaFactor_one]
    exact hasSum_shiftedTerm τ (by simp) m.succPNat
  have h_pairs : HasSum (fun n : ℕ ↦ F ↑(n + 1) + F (-↑(n + 1)))
      (S + π / τ.im * m.succPNat ^ (1 - 2 * 1 : ℝ) - F 0) := by
    simpa [sub_eq_add_neg] using (hasSum_nat_add_iff' 1).2 h_row.nat_add_neg
  have h_im (n : ℕ) : (cotTerm z n).im = -m.succ * τ.im * (F ↑(n + 1) + F (-↑(n + 1))) := by
    simp [z, F, shiftedTerm, Complex.sq_norm, normSq]
    ring
  have h_sum : (∑' n : ℕ, cotTerm z n).im =
      -m.succ * τ.im * (S + π / τ.im * m.succPNat ^ (1 - 2 * 1 : ℝ) - F 0) := by
    rw [im_tsum (summable_cotTerm z.coe_mem_integerComplement)]
    exact ((h_pairs.mul_left (-m.succ * τ.im)).congr_fun h_im).tsum_eq
  -- Compare with the `q`-expansion of the cotangent: the terms `n = 0` cancel, and the constant
  -- term `-π` is `-im z` times the integral `π / (Im τ (m+1))`.
  rw [← cot_series_rep' z.coe_mem_integerComplement, pi_mul_cot_pi_q_exp] at h_sum
  have hm_norm : ‖(m : ℂ) + 1‖ = m + 1 := by norm_cast
  have hτ_pos : 0 < ‖(τ : ℂ)‖ := hy.trans_le (im_le_norm _)
  let Q : ℝ := (∑' j : ℕ, eta_q m (τ : ℂ) ^ j).re
  have h_key : π - 2 * π * Q + τ.im / ((m + 1) * ‖(τ : ℂ)‖ ^ 2) =
      -(m + 1) * τ.im * (S + π / (τ.im * (m + 1)) - 1 / ((m + 1) * ‖(τ : ℂ)‖) ^ 2) := by
    clear_value S
    norm_num [z, F, shiftedTerm, ← mul_assoc, ← eta_q_eq_cexp, rpow_neg_one, normSq_eq_norm_sq,
      -ofReal_add, hm_norm] at h_sum
    linear_combination (norm := field) h_sum
  rw [show (∑' j : ℕ, eta_q m (τ : ℂ) ^ j.succ / ofReal m.succ).re = (Q - 1) / (m + 1) by
    norm_num [Q, tsum_div_const, geom_series_succ _ (norm_eta_q_lt_one τ m), -ofReal_add]]
  linear_combination (norm := field) ((m + 1) * τ.im)⁻¹ * h_key

/-- At `s = 1` the errors sum to `-2 π / Im τ * log |∏ (1 - q^(j+1))|`, `q = exp (2 π i τ)`. -/
private theorem tsum_meanError_one (τ : ℍ) :
    ∑' p : ℕ+ × ℤ, meanError τ p 1 =
      -2 * π / τ.im * Real.log ‖∏' j : ℕ, (1 - eta_q j (τ : ℂ))‖ := by
  let c (m j : ℕ) : ℂ := eta_q m (τ : ℂ) ^ j.succ / ofReal m.succ
  obtain ⟨hc, h_prod⟩ := tprod_one_sub_eta_q τ
  have h_rows : HasSum (fun m : ℕ+ ↦ ∑' n : ℤ, meanError τ (m, n) 1)
      (2 * π / τ.im * (∑' m : ℕ, ∑' j : ℕ, c m j).re) :=
    Equiv.pnatEquivNat.symm.hasSum_iff.1
      (((hasSum_re hc.prod.hasSum).mul_left _).congr_fun (tsum_meanError_row_one τ))
  rw [(summable_meanError τ (by simp)).tsum_prod, h_rows.tsum_eq, h_prod, norm_exp,
    Real.log_exp, neg_re]
  ring

/-- The part of `∑ |m τ + n|^(-2s)` without a pole at `s = 1`. For `1 < s < 2` it is the sum minus
`betaFactor (Im τ) s / (s - 1)` (`UpperHalfPlane.sub_one_mul_tsum_norm_rpow`). -/
private def regularPart (τ : ℍ) (s : ℝ) : ℝ :=
  2 * (∑' p : ℕ+ × ℤ, meanError τ p s + (2 * s - 1)⁻¹ + (riemannZeta₀ (2 * s)).re +
    betaFactor τ.im s * (riemannZeta₀ (2 * s - 1)).re)

/-- The regular part of the sum is continuous from the right at `s = 1`. -/
private theorem continuousWithinAt_regularPart (τ : ℍ) :
    ContinuousWithinAt (regularPart τ) (Ioi 1) 1 := by
  have h_error : ContinuousWithinAt (fun s : ℝ ↦ ∑' p : ℕ+ × ℤ, meanError τ p s) (Ioi 1) 1 :=
    (continuousOn_tsum_meanError τ 1 (by simp)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT one_lt_two)
  have h_beta : ContinuousAt (betaFactor τ.im) 1 := (hasDerivAt_betaFactor τ.im_pos).continuousAt
  have h_zeta : Continuous riemannZeta₀ := differentiable_riemannZeta₀.continuous
  unfold regularPart
  fun_prop (disch := norm_num)

private theorem regularPart_one (τ : ℍ) :
    regularPart τ 1 = 2 * (-2 * π / τ.im * Real.log ‖∏' j : ℕ, (1 - eta_q j (τ : ℂ))‖ +
      π ^ 2 / 6 + π / τ.im * eulerMascheroniConstant) := by
  norm_num [regularPart, tsum_meanError_one τ, betaFactor_one, riemannZeta₀, riemannZeta_two, sq]

/-- For `1 < s < 2`, the sum `∑ |m τ + n|^(-2s)` over `ℤ²` is
`regularPart τ s + betaFactor (Im τ) s / (s - 1)`, where
`betaFactor y s = √π Γ(s - 1/2) / Γ(s) * y^(1 - 2s)` and `regularPart` is the part without a pole
at `s = 1`; the equation is stated multiplied by `s - 1`. -/
private theorem sub_one_mul_tsum_norm_rpow (τ : ℍ) {s : ℝ} (hs : s ∈ Ioo (1 : ℝ) 2) :
    (s - 1) * ∑' p : ℤ × ℤ, ‖p.1 * (τ : ℂ) + p.2‖ ^ (-2 * s) =
      (s - 1) * regularPart τ s + betaFactor τ.im s := by
  -- Sum by rows: the row `0` is `2 ζ(2s)` (its term `n = 0` is `0 ^ (-2s) = 0`), and the rows
  -- `m` and `-m` are equal.
  obtain ⟨hs_one, hs_two⟩ := hs
  have hs_mem : s ∈ Icc 1 2 := ⟨hs_one.le, hs_two.le⟩
  let f (p : ℤ × ℤ) : ℝ := ‖p.1 * (τ : ℂ) + p.2‖ ^ (-2 * s)
  have hf : Summable f := summable_norm_mul_add_rpow τ (by linarith)
  have h_row_zero : ∑' n : ℤ, f (0, n) = 2 * ((2 * s - 1)⁻¹ + (riemannZeta₀ (2 * s)).re) := by
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (fun n ↦ by simp [f]) (hf.prod_factor 0)]
    simp [f, (TauCeti.hasSum_pnat_rpow_neg_inv_sub_one_add_riemannZeta₀_re (s := 2 * s)
      (by linarith)).tsum_eq, (one_pos.trans hs_one).ne', mul_add]
  have h_rows_pos : HasSum (fun m : ℕ+ ↦ ∑' n : ℤ, f (m, n))
      (∑' p : ℕ+ × ℤ, meanError τ p s +
        betaFactor τ.im s * ((2 * s - 1 - 1)⁻¹ + (riemannZeta₀ (2 * s - 1)).re)) := by
    have h_zeta : HasSum (fun m : ℕ+ ↦ (m : ℝ) ^ (-(2 * s - 1)))
        ((2 * s - 1 - 1)⁻¹ + (riemannZeta₀ (2 * s - 1)).re) := by
      exact_mod_cast TauCeti.hasSum_pnat_rpow_neg_inv_sub_one_add_riemannZeta₀_re
        (s := 2 * s - 1) (by linarith)
    rw [(summable_meanError τ hs_mem).tsum_prod]
    refine ((summable_meanError τ hs_mem).prod.hasSum.add
      (h_zeta.mul_left (betaFactor τ.im s))).congr_fun fun m ↦ ?_
    simpa [f, shiftedTerm] using (hasSum_shiftedTerm τ hs_mem m).tsum_eq
  have h_even : Function.Even fun m : ℤ ↦ ∑' n : ℤ, f (m, n) :=
    fun m ↦ (tsum_comp_neg _).symm.trans (by simp [f, norm_neg_add])
  rw [hf.tsum_prod, tsum_int_eq_zero_add_two_mul_tsum_pnat h_even hf.prod, h_row_zero,
    h_rows_pos.tsum_eq, show 2 * s - 1 - 1 = 2 * (s - 1) by ring, regularPart, two_smul]
  field [sub_ne_zero.2 hs_one.ne']

/-! ### Kronecker's first limit formula -/

private theorem im_div_norm_sq_rpow (τ : ℍ) (w : ℂ) (s : ℝ) :
    (τ.im / ‖w‖ ^ 2) ^ s = τ.im ^ s * ‖w‖ ^ (-2 * s) := by
  rw [div_rpow τ.im_pos.le (by positivity), ← rpow_natCast, ← rpow_mul (norm_nonneg _),
    neg_mul, rpow_neg (norm_nonneg _), div_eq_mul_inv]
  norm_num

/-- The series defining `UpperHalfPlane.epsteinZeta τ s` converges for `s > 1`. -/
theorem hasSum_epsteinZeta (τ : ℍ) {s : ℝ} (hs : 1 < s) :
    HasSum (fun p : ℤ × ℤ ↦ (τ.im / ‖(p.1 : ℂ) * τ + p.2‖ ^ 2) ^ s) (epsteinZeta τ s) := by
  have h : Summable fun p : ℤ × ℤ ↦ (τ.im / ‖(p.1 : ℂ) * τ + p.2‖ ^ 2) ^ s := by
    simp_rw [im_div_norm_sq_rpow]
    exact (summable_norm_mul_add_rpow τ (by linarith)).mul_left _
  exact h.hasSum

/-- **Kronecker's first limit formula.** As `s` decreases to `1`, the real Epstein zeta function
of the lattice `ℤ τ + ℤ` satisfies

`E(τ, s) = π / (s - 1) + π (2 γ + log π - logPeriod τ) + o(1)`,

where `γ` is Euler's constant and `logPeriod τ = log (4 π Im τ |η(τ)|⁴)`. -/
theorem tendsto_epsteinZeta_sub (τ : ℍ) :
    Tendsto (fun s : ℝ ↦ epsteinZeta τ s - π / (s - 1)) (𝓝[>] 1)
      (𝓝 (π * (2 * eulerMascheroniConstant + Real.log π - logPeriod τ))) := by
  -- Write `∑ |m τ + n|^(-2s) = T s + G s / (s - 1)` with `T` right-continuous and `G`
  -- differentiable at `1`; then `E(τ, s) - π / (s - 1) = y^s T s + (h s - h 1) / (s - 1)` for
  -- `h s = y^s G s`, since `h 1 = π`.
  have hy := τ.im_pos
  let T := regularPart τ
  let G := betaFactor τ.im
  let h (s : ℝ) : ℝ := τ.im ^ s * G s
  have hG := hasDerivAt_betaFactor hy
  have hh : HasDerivAt h _ 1 := ((hasDerivAt_id (1 : ℝ)).const_rpow hy).mul hG
  have hT : Tendsto (fun s ↦ τ.im ^ s * T s) (𝓝[>] 1) (𝓝 (τ.im ^ (1 : ℝ) * T 1)) :=
    ((continuous_const_rpow hy.ne').continuousAt.continuousWithinAt.mul
      (continuousWithinAt_regularPart τ)).tendsto
  have h_slope : Tendsto (fun s ↦ (h s - h 1) / (s - 1)) (𝓝[>] 1) (𝓝 (deriv h 1)) := by
    refine (hh.differentiableAt.hasDerivAt.tendsto_slope.mono_left
      (nhdsWithin_mono _ fun s hs ↦ ne_of_gt hs)).congr fun s ↦ ?_
    rw [slope_def_field]
  have h_eq : ∀ s ∈ Ioo (1 : ℝ) 2,
      τ.im ^ s * T s + (h s - h 1) / (s - 1) = epsteinZeta τ s - π / (s - 1) := by
    intro s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs.1.ne'
    have h_tot := sub_one_mul_tsum_norm_rpow τ hs
    have h_one : h 1 = π := by
      simp only [h, G, betaFactor_one, rpow_one]
      field_simp
    rw [epsteinZeta]
    simp_rw [im_div_norm_sq_rpow]
    rw [tsum_mul_left,
      show ∑' p : ℤ × ℤ, ‖(p.1 : ℂ) * τ + p.2‖ ^ (-2 * s) = T s + G s / (s - 1) by
        rw [← mul_right_inj' hs1, h_tot, mul_add, mul_div_cancel₀ _ hs1], h_one]
    simp only [h]
    field_simp
    ring
  have h_lim : Tendsto (fun s ↦ epsteinZeta τ s - π / (s - 1)) (𝓝[>] 1)
      (𝓝 (τ.im ^ (1 : ℝ) * T 1 + deriv h 1)) :=
    (hT.add h_slope).congr' <| by
      filter_upwards [Ioo_mem_nhdsGT one_lt_two] with s hs using h_eq s hs
  convert h_lim using 2
  simp only [hh.deriv, T, G, id]
  rw [regularPart_one, betaFactor_one, logPeriod_eq_log_tprod, rpow_one,
    Real.log_mul (by norm_num) pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  field_simp
  ring

/-- The residue of the real Epstein zeta function of `ℤ τ + ℤ` at `s = 1` is `π`. -/
theorem tendsto_sub_one_mul_epsteinZeta (τ : ℍ) :
    Tendsto (fun s : ℝ ↦ (s - 1) * epsteinZeta τ s) (𝓝[>] 1) (𝓝 π) := by
  have h : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by simpa using (continuous_sub_right (1 : ℝ)).tendsto 1)
  have h_lim := (h.mul (tendsto_epsteinZeta_sub τ)).add_const π
  rw [zero_mul, zero_add] at h_lim
  refine h_lim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  field_simp [sub_ne_zero.2 hs.ne']
  ring

end UpperHalfPlane

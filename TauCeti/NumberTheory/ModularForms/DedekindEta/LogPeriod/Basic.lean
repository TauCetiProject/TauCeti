/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.NumberTheory.ModularForms.DedekindEta.Basic
import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation

/-!
# The logarithmic period

For `τ` in the upper half-plane, the logarithmic period of the lattice `ℤ τ + ℤ` is
`log (4 π Im τ |η(τ)|⁴)`, with `η` the Dedekind eta function. It is the constant term of
Kronecker's first limit formula (`UpperHalfPlane.tendsto_epsteinZeta_sub`).

## Main definitions and results

* `UpperHalfPlane.logPeriod`: the logarithmic period `log (4 π Im τ |η(τ)|⁴)`.
* `UpperHalfPlane.logPeriod_eq_log_tprod`: its expression through the Euler product of `η`.
* `UpperHalfPlane.logPeriod_smul`: it is invariant under `SL(2, ℤ)`, so it only depends on the
  homothety class of the lattice `ℤ τ + ℤ`.
-/

public section

noncomputable section

open Complex Real
open ModularForm hiding eta
open scoped ModularForm MatrixGroups

namespace UpperHalfPlane

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

end UpperHalfPlane

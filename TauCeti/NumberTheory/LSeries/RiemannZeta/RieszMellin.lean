/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.RemainderMellin
public import TauCeti.NumberTheory.LSeries.RiemannZeta.Meromorphic
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Mellin expression for the Riemann zeta Riesz remainder

The constant term after subtracting `-1 / (s - 1)` from `ζ′ / ζ` at `1` is Euler's
constant. This uses Mathlib's `deriv_riemannZeta₁_one` (the derivative of the regularization of
`ζ` at `1`) and fixes the coefficient of the linear main term in the first Riesz remainder.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- The finite part of `ζ′ / ζ` at `1` is the Euler–Mascheroni constant. -/
@[simp] theorem logDerivFinitePart_riemannZeta_one :
    logDerivFinitePart riemannZeta 1 = (Real.eulerMascheroniConstant : ℂ) := by
  have ha := differentiable_riemannZeta₁.analyticAt (z := (1 : ℂ))
  have hlog : AnalyticAt ℂ (logDeriv riemannZeta₁) 1 := ha.deriv.fun_div ha (by simp)
  rw [logDerivFinitePart_eq hlog, logDeriv_apply]
  · simp
  · filter_upwards [self_mem_nhdsWithin (s := ({1} : Set ℂ)ᶜ),
      riemannZeta₁_ne_zero_of_near_one.filter_mono nhdsWithin_le_nhds] with s hs hne
    have hs' : s ≠ 1 := hs
    rw [logDeriv_apply riemannZeta, logDeriv_apply riemannZeta₁,
      deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs', riemannZeta_eq_inv_sub_mul hs']
    simp only [meromorphicOrderAt_riemannZeta_one, WithTop.untop₀_neg, WithTop.untop₀_one,
      Int.cast_neg, Int.cast_one]
    field_simp [sub_ne_zero.mpr hs']
    ring

/-- On the half-plane of absolute convergence, the Riemann zeta function's correction
removes both Laurent terms at `1`, with Euler's constant in the simple-pole term. -/
theorem rieszRemainderMellin_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    rieszRemainderMellin riemannZeta s =
      (s * (Real.eulerMascheroniConstant : ℂ) + (s - 1) -
        (logDeriv riemannZeta s + (s - 1)⁻¹)) /
        (s * (s - 1)) := by
  have hs₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs₁ : s ≠ 1 := by rintro rfl; simp at hs
  have h := (rieszRemainderMellin_eq_and_analyticAt meromorphic_riemannZeta hs₀ hs₁
    (analyticOn_riemannZeta s hs₁) (riemannZeta_ne_zero_of_one_lt_re hs)).1
  simpa [neg_div, sub_neg_eq_add, one_div, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using h

end TauCeti

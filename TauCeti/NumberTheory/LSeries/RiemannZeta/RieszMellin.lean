/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.RemainderMellin
public import TauCeti.NumberTheory.LSeries.RiemannZeta.Meromorphic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne

/-!
# Mellin expression for the Riemann zeta Riesz remainder

The constant term after subtracting `-1 / (s - 1)` from `ζ′ / ζ` at `1` is Euler's
constant (`TauCeti.logDerivFinitePart_riemannZeta_one`). It fixes the coefficient of the linear
main term in the first Riesz remainder.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- On the half-plane of absolute convergence, the Riemann zeta function's correction
removes both Laurent terms at `1`, with Euler's constant in the simple-pole term. -/
theorem rieszRemainderMellin_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    rieszRemainderMellin riemannZeta s =
      (s * (Real.eulerMascheroniConstant : ℂ) + (s - 1) -
        (logDeriv riemannZeta s + (s - 1)⁻¹)) /
        (s * (s - 1)) := by
  have hs₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs₁ : s ≠ 1 := by rintro rfl; simp at hs
  rw [(meromorphic_riemannZeta.rieszRemainderMellin_eq_and_analyticAt hs₀ hs₁
    (analyticOn_riemannZeta s hs₁) (riemannZeta_ne_zero_of_one_lt_re hs)).1,
    logDerivFinitePart_riemannZeta_one, meromorphicOrderAt_riemannZeta_one, WithTop.untop₀_neg,
    WithTop.untop₀_one]
  push_cast
  ring

end TauCeti

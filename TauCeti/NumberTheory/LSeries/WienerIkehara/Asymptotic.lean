/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import TauCeti.Analysis.Fourier.RiemannLebesgue
public import TauCeti.NumberTheory.LSeries.WienerIkehara.Limit

/-!
# The smoothed asymptotic behind Wiener--Ikehara

`TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary_of_contDiff` writes the
difference between a Fourier-weighted Dirichlet series and its pole contribution as an integral
along the line `Re s = 1`, for every scale `x > 0`. That integral carries the oscillating factor
`x ^ (it)`, so the Riemann--Lebesgue lemma makes it vanish as `x → ∞`. This file records the
resulting asymptotic, and then evaluates the pole contribution in the limit.

The pole contribution is `A * ∫ u in Ici (-log x), 𝓕 psi (u / 2π)`. As `x → ∞` the cutoff
`-log x` runs off to `-∞`, so the integral fills up the whole line, where Fourier inversion
evaluates it as `2π * psi 0`. The Fourier-weighted series therefore has the honest limit
`2π * A * psi 0`; the constant `2π` is the Jacobian of the scaling `u ↦ u / 2π` fixed by the
`x ^ (it)` parameterization.

Only the pole-subtracted remainder `G` is assumed continuous on the closed half-plane `Re s ≥ 1`.
Nothing is assumed about `LSeries a` there, where it is a total function with junk values.

## Main results

* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_sub_pole_atTop`: the Fourier-weighted Dirichlet
  series and its pole contribution differ by `o(1)` as the scale `x` tends to infinity.
* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop`: the Fourier-weighted Dirichlet series
  itself tends to `2π * A * psi 0`.

## Provenance

The statement obtained by letting `x → ∞` in the boundary Fourier identity follows `limiting_cor`
in `PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0 `AxiomMath/PrimeNumberTheoremAnd`
repository, revision `2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, the same source as the sibling
files `TauCeti.NumberTheory.LSeries.WienerIkehara.Fourier` and
`TauCeti.NumberTheory.LSeries.WienerIkehara.Limit`. The evaluation of the limiting pole
contribution by Fourier inversion is not in that source, which keeps the truncated integral.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
-/

public section

namespace TauCeti.LSeries

open Complex Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff Topology

variable {a : ℕ → ℂ} {psi : ℝ → ℂ} {G : ℂ → ℂ} {A : ℂ}

/-- As the scale `x` tends to infinity, the Fourier-weighted Dirichlet series on the line
`Re s = 1` and the contribution of the pole term `A / (s - 1)` at `s = 1` differ by `o(1)`.

This is the Riemann--Lebesgue lemma applied to the boundary identity
`tsum_term_mul_fourier_sub_pole_eq_integral_boundary_of_contDiff`, whose right-hand side is an
integral against the oscillating factor `x ^ (it)`. -/
theorem tendsto_tsum_term_mul_fourier_sub_pole_atTop
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma)
    (hpsi : ContDiff ℝ ∞ psi) (hsupp : HasCompactSupport psi)
    (hFsum : ∀ x : ℝ, 0 < x → LSeriesSummable
      (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) 1) :
    Tendsto (fun x : ℝ ↦
        (∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) -
          A * ∫ u in Ici (-Real.log x), 𝓕 psi (u / (2 * π))) atTop (𝓝 0) := by
  refine Tendsto.congr' ?_
    (tendsto_integral_mul_cpow_mul_I_atTop fun t : ℝ ↦ G (1 + t * I) * psi t)
  filter_upwards [eventually_gt_atTop 0] with x hx
  exact (tsum_term_mul_fourier_sub_pole_eq_integral_boundary_of_contDiff hx hG hG' hsum hpsi hsupp
    (hFsum x hx)).symm

/-- **The smoothed Wiener--Ikehara asymptotic.** The Fourier-weighted Dirichlet series on the line
`Re s = 1` tends to `2π * A * psi 0`, where `A` is the coefficient of the pole term `A / (s - 1)`
that the continuous boundary remainder `G` subtracts off. The hypotheses allow `A = 0`, in which
case no pole is asserted and the limit is `0`.

The factor `2π` is the Jacobian of the scaling `u ↦ u / 2π` that the parameterization
`s = 1 + it` forces on the Fourier variable; by Fourier inversion the limiting pole contribution
is `A * ∫ u : ℝ, 𝓕 psi (u / 2π) = 2π * A * psi 0`. -/
theorem tendsto_tsum_term_mul_fourier_atTop
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma)
    (hpsi : ContDiff ℝ ∞ psi) (hsupp : HasCompactSupport psi)
    (hFsum : ∀ x : ℝ, 0 < x → LSeriesSummable
      (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * Real.log (n / x))) 1) :
    Tendsto (fun x : ℝ ↦
        ∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * Real.log (n / x)))
      atTop (𝓝 (2 * (π : ℂ) * A * psi 0)) := by
  have hint : Integrable fun u : ℝ ↦ 𝓕 psi (u / (2 * π)) :=
    (integrable_fourier_of_contDiff_of_hasCompactSupport hpsi hsupp).comp_div (by positivity)
  have hIci : Tendsto (fun x : ℝ ↦ ∫ u in Ici (-Real.log x), 𝓕 psi (u / (2 * π))) atTop
      (𝓝 (∫ u : ℝ, 𝓕 psi (u / (2 * π)))) :=
    AECover.integral_tendsto_of_countably_generated
      (aecover_Ici (tendsto_neg_atTop_atBot.comp Real.tendsto_log_atTop)) hint
  have htotal : (∫ v : ℝ, 𝓕 psi v) = psi 0 := by
    have hinv : 𝓕⁻ (𝓕 psi) 0 = psi 0 :=
      (hpsi.continuous.integrable_of_hasCompactSupport hsupp).fourierInv_fourier_eq
        (integrable_fourier_of_contDiff_of_hasCompactSupport hpsi hsupp)
        hpsi.continuous.continuousAt
    rw [Real.fourierInv_eq] at hinv
    simpa using hinv
  have hvalue : (∫ u : ℝ, 𝓕 psi (u / (2 * π))) = 2 * (π : ℂ) * psi 0 := by
    rw [Measure.integral_comp_div, htotal, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
      real_smul]
    push_cast
    ring
  have hconst : 2 * (π : ℂ) * A * psi 0 = A * ∫ u : ℝ, 𝓕 psi (u / (2 * π)) := by
    rw [hvalue]
    ring
  have hpole : Tendsto (fun x : ℝ ↦ A * ∫ u in Ici (-Real.log x), 𝓕 psi (u / (2 * π))) atTop
      (𝓝 (2 * (π : ℂ) * A * psi 0)) := by
    rw [hconst]
    exact hIci.const_mul A
  simpa using
    (tendsto_tsum_term_mul_fourier_sub_pole_atTop hG hG' hsum hpsi hsupp hFsum).add hpole

end TauCeti.LSeries

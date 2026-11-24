/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The Schläfli–Laplace amplitude and Hankel's coefficients

Because `cosh(p ξ)` is an even function of `ξ`, the square-root branch point of `arcosh z` at
`z = 1` cancels in `cosh(p arcosh z)`, leaving only the branch cut along `(-∞, -1]`. Under the
shift `z = 1 + w`, the amplitude `h_p(w) = cosh(p arcosh(1 + w)) / (w + 2)^{1/2}` arising in the
Laplace transformation `τ = cosh u - 1` of Schläfli's integral is therefore holomorphic on the cut
plane `{w : ℂ | w + 2 ∈ Complex.slitPlane}`, which contains both `Complex.slitPlane` and the open
disc `Metric.ball 0 2`.

This file defines the holomorphic continuation `coshMulArcosh p` on
`{z : ℂ | z + 1 ∈ Complex.slitPlane}`, the Schläfli–Laplace amplitude `schlafliAmplitude p` on
`{w : ℂ | w + 2 ∈ Complex.slitPlane}`, and Hankel's asymptotic coefficients `hankelCoeff p k`
(DLMF 10.17.1). It establishes Chebyshev's differential equation for `coshMulArcosh p`, the
two-term hypergeometric differential equation for `schlafliAmplitude p`, uniform polynomial growth
bounds, and the Maclaurin series expansion of `schlafliAmplitude p` on `Metric.ball 0 2` in terms
of `hankelCoeff p k`.

## Main definitions

* `TauCeti.coshMulArcosh`: the analytic continuation of `z ↦ cosh(p arcosh z)` to
  `{z : ℂ | z + 1 ∈ Complex.slitPlane}`.
* `TauCeti.schlafliAmplitude`: the Schläfli–Laplace amplitude
  `h_p(w) = coshMulArcosh p (1 + w) / (w + 2) ^ (1 / 2 : ℂ)`.
* `TauCeti.hankelCoeff`: Hankel's asymptotic coefficient
  `a_k(p) = (∏_{j < k} (4 p² - (2 j + 1)²)) / (8 ^ k * k!)` (DLMF 10.17.1).
* `TauCeti.schlafliAmplitudeCoeff` and `TauCeti.schlafliAmplitudeSeries`: the Maclaurin
  coefficients `2 ^ (-1 / 2 : ℂ) * a_k(p) / (1 / 2)_k` and formal power series of
  `schlafliAmplitude p` at `0`.

## Main statements

* `TauCeti.differentiableOn_coshMulArcosh`, `TauCeti.analyticOnNhd_coshMulArcosh`,
  `TauCeti.coshMulArcosh_ode`, and `TauCeti.norm_coshMulArcosh_le`: holomorphy,
  Chebyshev's differential equation `(z² - 1) f''(z) + z f'(z) = p² f(z)` on
  `{z : ℂ | z + 1 ∈ Complex.slitPlane}`, and global growth bound for `coshMulArcosh p`.
* `TauCeti.differentiableOn_schlafliAmplitude`, `TauCeti.analyticOnNhd_schlafliAmplitude`, and
  `TauCeti.schlafliAmplitude_ode`: holomorphy and the hypergeometric differential equation
  `w (w + 2) h''(w) + (2 w + 1) h'(w) + (1 / 4 - p²) h(w) = 0` on
  `{w : ℂ | w + 2 ∈ Complex.slitPlane}`.
* `TauCeti.hasFPowerSeriesOnBall_schlafliAmplitude`, `TauCeti.hasSum_schlafliAmplitude`, and
  `TauCeti.Gamma_add_half_mul_schlafliAmplitudeCoeff`: the Maclaurin expansion of
  `schlafliAmplitude p` on `Metric.ball 0 2` and its Gamma–Pochhammer relation to `hankelCoeff`.

## References

* NIST Digital Library of Mathematical Functions, §§9.13(i)–(ii), 10.17(i), 10.32(ii), 10.40(i),
  <https://dlmf.nist.gov/9.13>, <https://dlmf.nist.gov/10.17>, <https://dlmf.nist.gov/10.32>,
  <https://dlmf.nist.gov/10.40>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 4 and §7.4.
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., Cambridge University
  Press, 1944, §§6.22, 7.2.
-/

public section

noncomputable section

open Complex Filter Polynomial Set
open scoped Nat Topology

namespace TauCeti

/-! ### The holomorphic Chebyshev–arcosh function -/

/-- The holomorphic continuation of `z ↦ cosh(p arcosh z)` to the cut plane
`{z : ℂ | z + 1 ∈ Complex.slitPlane}`, expressed symmetrically in the two reciprocal roots
`((z + 1) / 2) ^ (1 / 2) ± ((z - 1) / 2) ^ (1 / 2)`. -/
def coshMulArcosh (p z : ℂ) : ℂ :=
  ((((z + 1) / 2) ^ (1 / 2 : ℂ) + ((z - 1) / 2) ^ (1 / 2 : ℂ)) ^ (2 * p) +
    (((z + 1) / 2) ^ (1 / 2 : ℂ) - ((z - 1) / 2) ^ (1 / 2 : ℂ)) ^ (2 * p)) / 2

/-- The defining formula for `coshMulArcosh`. -/
theorem coshMulArcosh_def (p z : ℂ) :
    coshMulArcosh p z =
      ((((z + 1) / 2) ^ (1 / 2 : ℂ) + ((z - 1) / 2) ^ (1 / 2 : ℂ)) ^ (2 * p) +
        (((z + 1) / 2) ^ (1 / 2 : ℂ) - ((z - 1) / 2) ^ (1 / 2 : ℂ)) ^ (2 * p)) / 2 := (rfl)

private def arcoshRoot (z : ℂ) : ℂ :=
  ((z + 1) / 2) ^ (1 / 2 : ℂ) + ((z - 1) / 2) ^ (1 / 2 : ℂ)

private def arcoshConjRoot (z : ℂ) : ℂ :=
  ((z + 1) / 2) ^ (1 / 2 : ℂ) - ((z - 1) / 2) ^ (1 / 2 : ℂ)

private theorem arcoshRoot_def (z : ℂ) :
    arcoshRoot z = ((z + 1) / 2) ^ (1 / 2 : ℂ) + ((z - 1) / 2) ^ (1 / 2 : ℂ) := rfl

private theorem arcoshConjRoot_def (z : ℂ) :
    arcoshConjRoot z = ((z + 1) / 2) ^ (1 / 2 : ℂ) - ((z - 1) / 2) ^ (1 / 2 : ℂ) := rfl

private theorem coshMulArcosh_eq_roots (p z : ℂ) :
    coshMulArcosh p z = (arcoshRoot z ^ (2 * p) + arcoshConjRoot z ^ (2 * p)) / 2 := rfl

private theorem arcoshRoot_mul_conjRoot (z : ℂ) :
    arcoshRoot z * arcoshConjRoot z = 1 := by
  rw [arcoshRoot_def, arcoshConjRoot_def, ← sq_sub_sq]
  simp only [one_div, cpow_ofNat_inv_pow]
  ring

private theorem arcoshRoot_ne_zero (z : ℂ) : arcoshRoot z ≠ 0 :=
  left_ne_zero_of_mul_eq_one (arcoshRoot_mul_conjRoot z)

private theorem arcoshRoot_re_nonneg (z : ℂ) : 0 ≤ (arcoshRoot z).re := by
  have hre (w : ℂ) : 0 ≤ (w ^ (1 / 2 : ℂ)).re := by rw [one_div, cpow_inv_two_re]; positivity
  exact add_nonneg (hre _) (hre _)

private theorem arcoshRoot_mem_slitPlane (z : ℂ) : arcoshRoot z ∈ Complex.slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra! h
  exact arcoshRoot_ne_zero z (Complex.ext (le_antisymm h.1 (arcoshRoot_re_nonneg z)) h.2)

private theorem arcoshConjRoot_eq_inv (z : ℂ) : arcoshConjRoot z = (arcoshRoot z)⁻¹ :=
  eq_inv_of_mul_eq_one_right (arcoshRoot_mul_conjRoot z)

private theorem arcoshConjRoot_re_nonneg (z : ℂ) : 0 ≤ (arcoshConjRoot z).re := by
  rw [arcoshConjRoot_eq_inv, inv_re]
  exact div_nonneg (arcoshRoot_re_nonneg z) (normSq_nonneg _)

private theorem arcoshConjRoot_ne_zero (z : ℂ) : arcoshConjRoot z ≠ 0 :=
  right_ne_zero_of_mul_eq_one (arcoshRoot_mul_conjRoot z)

private theorem arcoshConjRoot_mem_slitPlane (z : ℂ) :
    arcoshConjRoot z ∈ Complex.slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra! h
  exact arcoshConjRoot_ne_zero z
    (Complex.ext (le_antisymm h.1 (arcoshConjRoot_re_nonneg z)) h.2)

/-- Expresses `coshMulArcosh p z` as `Complex.cosh` of `2 * p` times the logarithm of the
upper quadratic root, unconditionally for all `p z : ℂ`. -/
theorem coshMulArcosh_eq_cosh_two_mul_log (p z : ℂ) :
    coshMulArcosh p z =
      Complex.cosh (2 * p * Complex.log (((z + 1) / 2) ^ (1 / 2 : ℂ) +
        ((z - 1) / 2) ^ (1 / 2 : ℂ))) := by
  have h0 : arcoshRoot z ≠ 0 := arcoshRoot_ne_zero z
  have hpi : (arcoshRoot z).arg ≠ Real.pi := slitPlane_arg_ne_pi (arcoshRoot_mem_slitPlane z)
  rw [coshMulArcosh_eq_roots, arcoshConjRoot_eq_inv, cpow_def_of_ne_zero h0,
    cpow_def_of_ne_zero (inv_ne_zero h0), log_inv _ hpi, Complex.cosh, arcoshRoot_def]
  congr 2 <;> ring_nf

/-- At order `0`, `coshMulArcosh 0 z` is identically `1`. -/
@[simp]
theorem coshMulArcosh_zero_left (z : ℂ) : coshMulArcosh 0 z = 1 := by
  simp [coshMulArcosh_eq_cosh_two_mul_log]

/-- At `z = 1`, `coshMulArcosh p 1 = 1` for every order `p`. -/
@[simp]
theorem coshMulArcosh_one_right (p : ℂ) : coshMulArcosh p 1 = 1 := by
  simp [coshMulArcosh_def]

/-- `coshMulArcosh p z` is an even function of the order parameter `p`. -/
@[simp]
theorem coshMulArcosh_neg_left (p z : ℂ) : coshMulArcosh (-p) z = coshMulArcosh p z := by
  rw [coshMulArcosh_eq_cosh_two_mul_log, coshMulArcosh_eq_cosh_two_mul_log]
  simp [neg_mul, mul_neg]

/-- At order `2⁻¹`, `coshMulArcosh 2⁻¹ z = ((z + 1) / 2) ^ (1 / 2 : ℂ)` everywhere on `ℂ`. -/
theorem coshMulArcosh_inv_two_left (z : ℂ) :
    coshMulArcosh 2⁻¹ z = ((z + 1) / 2) ^ (1 / 2 : ℂ) := by
  rw [coshMulArcosh_def, mul_inv_cancel₀ two_ne_zero, cpow_one, cpow_one]
  ring

/-- At order `1`, `coshMulArcosh 1 z = z` everywhere on `ℂ`. -/
@[simp]
theorem coshMulArcosh_one_left (z : ℂ) : coshMulArcosh 1 z = z := by
  rw [coshMulArcosh_def, mul_one, cpow_two, cpow_two]
  have h1 : (((z + 1) / 2) ^ (1 / 2 : ℂ)) ^ 2 = (z + 1) / 2 := by simp [one_div]
  have h2 : (((z - 1) / 2) ^ (1 / 2 : ℂ)) ^ 2 = (z - 1) / 2 := by simp [one_div]
  linear_combination h1 + h2

/-- The product-to-sum identity for `coshMulArcosh` in the order parameter. -/
theorem two_mul_coshMulArcosh_mul_coshMulArcosh (p q z : ℂ) :
    2 * coshMulArcosh p z * coshMulArcosh q z =
      coshMulArcosh (p + q) z + coshMulArcosh (p - q) z := by
  simp only [coshMulArcosh_eq_cosh_two_mul_log]
  set L := Complex.log (((z + 1) / 2) ^ (1 / 2 : ℂ) + ((z - 1) / 2) ^ (1 / 2 : ℂ))
  have h1 : 2 * (p + q) * L = 2 * p * L + 2 * q * L := by ring
  have h2 : 2 * (p - q) * L = 2 * p * L - 2 * q * L := by ring
  rw [h1, h2, Complex.cosh_add, Complex.cosh_sub]
  ring

/-- The three-term Chebyshev recurrence for `coshMulArcosh`. -/
theorem coshMulArcosh_add_one_add_sub_one (p z : ℂ) :
    coshMulArcosh (p + 1) z + coshMulArcosh (p - 1) z = 2 * z * coshMulArcosh p z := by
  simpa [coshMulArcosh_one_left, mul_assoc, mul_left_comm, mul_comm] using
    (two_mul_coshMulArcosh_mul_coshMulArcosh p 1 z).symm

/-- At integer orders, `coshMulArcosh` agrees everywhere on `ℂ` with the Chebyshev polynomial of
the first kind `Polynomial.Chebyshev.T`. -/
theorem coshMulArcosh_intCast (n : ℤ) (z : ℂ) :
    coshMulArcosh n z = (Polynomial.Chebyshev.T ℂ n).eval z := by
  set L := 2 * Complex.log (((z + 1) / 2) ^ (1 / 2 : ℂ) + ((z - 1) / 2) ^ (1 / 2 : ℂ))
  have hz : z = Complex.cosh L := by
    simpa [L, one_mul] using (coshMulArcosh_one_left z).symm.trans
      (coshMulArcosh_eq_cosh_two_mul_log 1 z)
  conv_rhs => rw [hz, Polynomial.Chebyshev.T_complex_cosh]
  rw [coshMulArcosh_eq_cosh_two_mul_log]
  congr 1; dsimp [L]; ring

/-- At natural-number orders, `coshMulArcosh` agrees everywhere on `ℂ` with the Chebyshev
polynomial of the first kind `Polynomial.Chebyshev.T`. -/
theorem coshMulArcosh_natCast (n : ℕ) (z : ℂ) :
    coshMulArcosh n z = (Polynomial.Chebyshev.T ℂ n).eval z := by
  simpa using coshMulArcosh_intCast (n : ℤ) z

/-- On `[1, ∞)`, `coshMulArcosh p x` agrees with `Complex.cosh (p * Real.arcosh x)`. -/
theorem coshMulArcosh_ofReal_eq_cosh_mul_arcosh (p : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    coshMulArcosh p x = Complex.cosh (p * Real.arcosh x) := by
  set u := Real.arcosh x
  have hch := Real.cosh_two_mul (u / 2)
  have hsh := Real.cosh_sq_sub_sinh_sq (u / 2)
  rw [mul_div_cancel₀ u two_ne_zero, Real.cosh_arcosh hx] at hch
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
  have hsqrt (y : ℝ) (hy : 0 ≤ y) : ((y ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = y := by
    rw [hhalf, ← ofReal_cpow (sq_nonneg y), ← Real.sqrt_eq_rpow, Real.sqrt_sq hy]
  have hx1 : ((x : ℂ) + 1) / 2 = ((Real.cosh (u / 2) ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast (by linarith : (x + 1) / 2 = Real.cosh (u / 2) ^ 2)
  have h1 : (((x : ℂ) + 1) / 2) ^ (1 / 2 : ℂ) = Real.cosh (u / 2) := by
    rw [hx1]; exact hsqrt _ (Real.cosh_pos _).le
  have hx2 : ((x : ℂ) - 1) / 2 = ((Real.sinh (u / 2) ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast (by linarith : (x - 1) / 2 = Real.sinh (u / 2) ^ 2)
  have h2 : (((x : ℂ) - 1) / 2) ^ (1 / 2 : ℂ) = Real.sinh (u / 2) := by
    rw [hx2]; exact hsqrt _ (Real.sinh_nonneg_iff.mpr (by linarith [Real.arcosh_nonneg hx]))
  rw [coshMulArcosh_eq_cosh_two_mul_log, h1, h2]
  have hexp : (Real.cosh (u / 2) : ℂ) + Real.sinh (u / 2) = Real.exp (u / 2) := by
    norm_cast; exact Real.cosh_add_sinh (u / 2)
  rw [hexp, ← ofReal_log (Real.exp_pos _).le, Real.log_exp]
  congr 1; push_cast; ring

/-- For every real `u`, `coshMulArcosh p (Complex.cosh u) = Complex.cosh (p * u)`. -/
@[simp]
theorem coshMulArcosh_cosh_ofReal (p : ℂ) (u : ℝ) :
    coshMulArcosh p (Complex.cosh u) = Complex.cosh (p * u) := by
  rw [← Complex.ofReal_cosh, coshMulArcosh_ofReal_eq_cosh_mul_arcosh p (Real.one_le_cosh u)]
  rcases le_total 0 u with hu | hu
  · rw [Real.arcosh_cosh hu]
  · rw [← Real.cosh_neg u, Real.arcosh_cosh (by linarith), ofReal_neg, mul_neg, Complex.cosh_neg]

/-- For fixed `z`, `p ↦ coshMulArcosh p z` is an entire function. -/
@[fun_prop]
theorem differentiable_coshMulArcosh_left (z : ℂ) :
    Differentiable ℂ (fun p : ℂ ↦ coshMulArcosh p z) := by
  simp_rw [coshMulArcosh_eq_cosh_two_mul_log]
  fun_prop

private theorem norm_arcoshRoot_le (z : ℂ) :
    ‖arcoshRoot z‖ ≤ 1 + Real.sqrt (2 * ‖z - 1‖) ∧
      ‖arcoshConjRoot z‖ ≤ 1 + Real.sqrt (2 * ‖z - 1‖) := by
  have hhalf (u : ℂ) : ‖u ^ (1 / 2 : ℂ)‖ = Real.sqrt ‖u‖ := by
    simpa [Real.sqrt_eq_rpow] using norm_cpow_real u (1 / 2)
  have hsum_le : ‖((z + 1) / 2) ^ (1 / 2 : ℂ)‖ + ‖((z - 1) / 2) ^ (1 / 2 : ℂ)‖ ≤
      1 + Real.sqrt (2 * ‖z - 1‖) := by
    have hz_shift : (z + 1) / 2 = 1 + (z - 1) / 2 := by ring
    rw [hhalf, hhalf, hz_shift]
    have h1 : Real.sqrt ‖1 + (z - 1) / 2‖ ≤ 1 + Real.sqrt (‖z - 1‖ / 2) := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      have htri : ‖1 + (z - 1) / 2‖ ≤ 1 + ‖z - 1‖ / 2 :=
        (norm_add_le 1 ((z - 1) / 2)).trans (by simp)
      rw [add_sq, one_pow, mul_one, Real.sq_sqrt (by positivity)]
      linarith [Real.sqrt_nonneg (‖z - 1‖ / 2)]
    have h2 : 2 * Real.sqrt (‖z - 1‖ / 2) = Real.sqrt (2 * ‖z - 1‖) := by
      have hscale : 2 * ‖z - 1‖ = 2 ^ 2 * (‖z - 1‖ / 2) := by ring
      rw [hscale, Real.sqrt_mul (by norm_num), Real.sqrt_sq zero_le_two]
    simp only [norm_div, norm_ofNat] at h1 ⊢
    linarith
  exact ⟨(norm_add_le _ _).trans hsum_le, (norm_sub_le _ _).trans hsum_le⟩

/-- Uniform growth bound for `coshMulArcosh p z` across all `p z : ℂ`. -/
theorem norm_coshMulArcosh_le (p z : ℂ) :
    ‖coshMulArcosh p z‖ ≤
      (1 + Real.sqrt (2 * ‖z - 1‖)) ^ (2 * |p.re|) * Real.exp (Real.pi * |p.im|) := by
  suffices h_nonneg : ∀ q : ℂ, 0 ≤ q.re → ‖coshMulArcosh q z‖ ≤
      (1 + Real.sqrt (2 * ‖z - 1‖)) ^ (2 * q.re) * Real.exp (Real.pi * |q.im|) by
    rcases le_total 0 p.re with hp | hp
    · simpa [abs_of_nonneg hp] using h_nonneg p hp
    · simpa [coshMulArcosh_neg_left, abs_of_nonpos hp] using
        h_nonneg (-p) (by simp; linarith)
  intro q hq
  have hroot : ∀ s : ℂ, s ≠ 0 → 0 ≤ s.re → ‖s‖ ≤ 1 + Real.sqrt (2 * ‖z - 1‖) →
      ‖s ^ (2 * q)‖ ≤ (1 + Real.sqrt (2 * ‖z - 1‖)) ^ (2 * q.re) * Real.exp (Real.pi * |q.im|) := by
    intro s hs0 hs_re hs_le
    have hq_re : (2 * q).re = 2 * q.re := by simp
    have hq_im : (2 * q).im = 2 * q.im := by simp
    rw [norm_cpow_of_ne_zero hs0, div_eq_mul_inv, ← Real.exp_neg, hq_re, hq_im]
    have harg : |s.arg| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_iff.mpr hs_re
    have hexp : -(s.arg * (2 * q.im)) ≤ Real.pi * |q.im| :=
      calc -(s.arg * (2 * q.im)) ≤ |-(s.arg * (2 * q.im))| := le_abs_self _
        _ = 2 * |s.arg| * |q.im| := by simp [abs_mul]; ring
        _ ≤ 2 * (Real.pi / 2) * |q.im| := by gcongr
        _ = Real.pi * |q.im| := by ring
    exact mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) hs_le (by positivity))
      (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
  obtain ⟨hr1, hr2⟩ := norm_arcoshRoot_le z
  have hb1 := hroot _ (arcoshRoot_ne_zero _) (arcoshRoot_re_nonneg _) hr1
  have hb2 := hroot _ (arcoshConjRoot_ne_zero _) (arcoshConjRoot_re_nonneg _) hr2
  rw [coshMulArcosh_eq_roots, norm_div, norm_ofNat]
  linarith [norm_add_le (arcoshRoot z ^ (2 * q)) (arcoshConjRoot z ^ (2 * q))]

/-! ### Holomorphy and Chebyshev differential equation of `coshMulArcosh` -/

private theorem coshMulArcosh_eq_alt (p z : ℂ) :
    coshMulArcosh p z =
      ((((z + 1) / 2) ^ (1 / 2 : ℂ) + I * ((1 - z) / 2) ^ (1 / 2 : ℂ)) ^ (2 * p) +
        (((z + 1) / 2) ^ (1 / 2 : ℂ) - I * ((1 - z) / 2) ^ (1 / 2 : ℂ)) ^ (2 * p)) / 2 := by
  have h := Complex.neg_cpow_half_eq_or_eq_neg ((1 - z) / 2)
  rw [← neg_div, neg_sub] at h
  rcases h with h | h
  · rw [coshMulArcosh_def, h]
  · rw [coshMulArcosh_def, h, sub_neg_eq_add, ← sub_eq_add_neg, add_comm]

private theorem differentiableAt_coshMulArcosh_of_sub_one (p : ℂ) {z : ℂ}
    (hz : z - 1 ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (coshMulArcosh p) z := by
  have hz_add : z + 1 ∈ Complex.slitPlane := by
    convert ofReal_add_mem_slitPlane hz zero_le_two using 1; push_cast; ring
  have hz1 : (z + 1) / 2 ∈ Complex.slitPlane := by
    simpa using div_ofReal_mem_slitPlane hz_add zero_lt_two
  have hz2 : (z - 1) / 2 ∈ Complex.slitPlane := by
    simpa using div_ofReal_mem_slitPlane hz zero_lt_two
  have hd1 : DifferentiableAt ℂ (fun w : ℂ ↦ ((w + 1) / 2) ^ (1 / 2 : ℂ)) z :=
    ((differentiableAt_id.add_const 1).div_const 2).cpow_const hz1
  have hd2 : DifferentiableAt ℂ (fun w : ℂ ↦ ((w - 1) / 2) ^ (1 / 2 : ℂ)) z :=
    ((differentiableAt_id.sub_const 1).div_const 2).cpow_const hz2
  exact (((hd1.add hd2).cpow_const (arcoshRoot_mem_slitPlane z) (c := 2 * p)).add
    ((hd1.sub hd2).cpow_const (arcoshConjRoot_mem_slitPlane z) (c := 2 * p))).div_const 2

private theorem differentiableAt_coshMulArcosh_of_re_lt_one (p : ℂ) {z : ℂ}
    (hz : z + 1 ∈ Complex.slitPlane) (hre : z.re < 1) :
    DifferentiableAt ℂ (coshMulArcosh p) z := by
  have hz1 : (z + 1) / 2 ∈ Complex.slitPlane := by
    simpa using div_ofReal_mem_slitPlane hz zero_lt_two
  have hz2 : (1 - z) / 2 ∈ Complex.slitPlane := by
    simpa using div_ofReal_mem_slitPlane (Or.inl (by simp; linarith)) zero_lt_two
  have hmem :
      ((z + 1) / 2) ^ (1 / 2 : ℂ) + I * ((1 - z) / 2) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane ∧
      ((z + 1) / 2) ^ (1 / 2 : ℂ) - I * ((1 - z) / 2) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane := by
    have h := Complex.neg_cpow_half_eq_or_eq_neg ((1 - z) / 2)
    rw [← neg_div, neg_sub] at h
    rcases h with h | h
    · rw [← h]; exact ⟨arcoshRoot_mem_slitPlane z, arcoshConjRoot_mem_slitPlane z⟩
    · have h' := neg_eq_iff_eq_neg.mp h.symm
      rw [h', ← sub_eq_add_neg, sub_neg_eq_add]
      exact ⟨arcoshConjRoot_mem_slitPlane z, arcoshRoot_mem_slitPlane z⟩
  have hd1 : DifferentiableAt ℂ (fun w : ℂ ↦ ((w + 1) / 2) ^ (1 / 2 : ℂ)) z :=
    ((differentiableAt_id.add_const 1).div_const 2).cpow_const hz1
  have hd2 : DifferentiableAt ℂ (fun w : ℂ ↦ I * ((1 - w) / 2) ^ (1 / 2 : ℂ)) z :=
    (((differentiableAt_const 1).sub differentiableAt_id).div_const 2).cpow_const hz2 |>.const_mul I
  have hd := (((hd1.add hd2).cpow_const hmem.1 (c := 2 * p)).add
    ((hd1.sub hd2).cpow_const hmem.2 (c := 2 * p))).div_const 2
  exact hd.congr_of_eventuallyEq (Eventually.of_forall (coshMulArcosh_eq_alt p))

private theorem continuousAt_coshMulArcosh_one (p : ℂ) :
    ContinuousAt (coshMulArcosh p) 1 := by
  have ha : Tendsto (fun z : ℂ ↦ ((z + 1) / 2) ^ (1 / 2 : ℂ)) (𝓝 1) (𝓝 1) := by
    simpa using (((differentiableAt_id (x := (1 : ℂ))).add_const 1).div_const 2).cpow_const
      (by simp [one_mem_slitPlane]) |>.continuousAt.tendsto
  have hb : Tendsto (fun z : ℂ ↦ ((z - 1) / 2) ^ (1 / 2 : ℂ)) (𝓝 1) (𝓝 0) := by
    have hc0 : ContinuousAt (fun w : ℂ ↦ w ^ (1 / 2 : ℂ)) 0 :=
      continuousAt_cpow_const_of_re_pos (Or.inl le_rfl) (by norm_num)
    have hlin : Tendsto (fun z : ℂ ↦ (z - 1) / 2) (𝓝 1) (𝓝 0) := by
      simpa using ((continuous_sub_right (1 : ℂ)).div_const (2 : ℂ)).tendsto 1
    simpa [Function.comp_def] using hc0.tendsto.comp hlin
  have hcpow : ContinuousAt (fun w : ℂ ↦ w ^ (2 * p)) 1 :=
    (differentiableAt_id.cpow_const one_mem_slitPlane).continuousAt
  have hroot : Tendsto arcoshRoot (𝓝 1) (𝓝 1) := by
    rw [funext arcoshRoot_def]
    simpa using ha.add hb
  have hconj : Tendsto arcoshConjRoot (𝓝 1) (𝓝 1) := by
    rw [funext arcoshConjRoot_def]
    simpa using ha.sub hb
  have hplus : Tendsto (fun z : ℂ ↦ arcoshRoot z ^ (2 * p)) (𝓝 1) (𝓝 1) := by
    simpa [Function.comp_def] using hcpow.tendsto.comp hroot
  have hminus : Tendsto (fun z : ℂ ↦ arcoshConjRoot z ^ (2 * p)) (𝓝 1) (𝓝 1) := by
    simpa [Function.comp_def] using hcpow.tendsto.comp hconj
  rw [ContinuousAt, coshMulArcosh_one_right, funext (coshMulArcosh_eq_roots p)]
  simpa using (hplus.add hminus).div_const (2 : ℂ)

/-- `coshMulArcosh p` is holomorphic on `{z : ℂ | z + 1 ∈ Complex.slitPlane}`. -/
theorem differentiableOn_coshMulArcosh (p : ℂ) :
    DifferentiableOn ℂ (coshMulArcosh p) {z : ℂ | z + 1 ∈ Complex.slitPlane} := by
  -- The branch cut of `((z - 1) / 2) ^ (1 / 2)` along `(-1, 1]` cancels between the two summands,
  -- and the isolated point `z = 1` is removable by continuity.
  have hopen : IsOpen {z : ℂ | z + 1 ∈ Complex.slitPlane} :=
    isOpen_slitPlane.preimage (continuous_add_const 1)
  rw [← differentiableOn_compl_singleton_and_continuousAt_iff
    (hopen.mem_nhds (by simp [mem_slitPlane_iff] : (1 : ℂ) ∈ _))]
  refine ⟨fun z ⟨hz_slit, hz_ne⟩ ↦ ?_, continuousAt_coshMulArcosh_one p⟩
  suffices DifferentiableAt ℂ (coshMulArcosh p) z from this.differentiableWithinAt
  by_cases hsub : z - 1 ∈ Complex.slitPlane
  · exact differentiableAt_coshMulArcosh_of_sub_one p hsub
  · refine differentiableAt_coshMulArcosh_of_re_lt_one p hz_slit ?_
    rw [mem_slitPlane_iff] at hsub; push Not at hsub
    refine lt_of_le_of_ne (by simpa using hsub.1) fun heq ↦ hz_ne (Complex.ext heq ?_)
    simpa using hsub.2

/-- `coshMulArcosh p` is complex analytic on `{z : ℂ | z + 1 ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_coshMulArcosh (p : ℂ) :
    AnalyticOnNhd ℂ (coshMulArcosh p) {z : ℂ | z + 1 ∈ Complex.slitPlane} :=
  (differentiableOn_coshMulArcosh p).analyticOnNhd
    (isOpen_slitPlane.preimage (continuous_add_const 1))

private def arcoshDenom (z : ℂ) : ℂ :=
  2 * ((z + 1) / 2) ^ (1 / 2 : ℂ) * ((z - 1) / 2) ^ (1 / 2 : ℂ)

private theorem arcoshDenom_def (z : ℂ) :
    arcoshDenom z = 2 * ((z + 1) / 2) ^ (1 / 2 : ℂ) * ((z - 1) / 2) ^ (1 / 2 : ℂ) := rfl

private theorem arcoshDenom_sq (z : ℂ) : arcoshDenom z ^ 2 = z ^ 2 - 1 := by
  calc arcoshDenom z ^ 2
    _ = 4 * (((z + 1) / 2) ^ (1 / 2 : ℂ)) ^ 2 * (((z - 1) / 2) ^ (1 / 2 : ℂ)) ^ 2 := by
        rw [arcoshDenom_def]; ring
    _ = z ^ 2 - 1 := by simp only [one_div, cpow_ofNat_inv_pow]; ring

private theorem arcoshDenom_ne_zero {z : ℂ} (hz : z - 1 ∈ Complex.slitPlane) :
    arcoshDenom z ≠ 0 := by
  intro h0
  have hsq := arcoshDenom_sq z; rw [h0, zero_pow two_ne_zero] at hsq
  have hz_add : z + 1 ∈ Complex.slitPlane := by
    convert ofReal_add_mem_slitPlane hz zero_le_two using 1; push_cast; ring
  have hprod : (z + 1) * (z - 1) = 0 := by linear_combination -hsq
  rcases mul_eq_zero.mp hprod with hp | hm
  · exact slitPlane_ne_zero hz_add hp
  · exact slitPlane_ne_zero hz hm

private theorem hasDerivAt_arcoshRoot_log {z : ℂ} (hz : z - 1 ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ ↦ Complex.log (arcoshRoot w)) ((2 * arcoshDenom z)⁻¹) z := by
  set a := ((z + 1) / 2) ^ (1 / 2 : ℂ) with ha_def
  set b := ((z - 1) / 2) ^ (1 / 2 : ℂ) with hb_def
  have hroot_eq : arcoshRoot z = a + b := arcoshRoot_def z
  have hden_eq : arcoshDenom z = 2 * a * b := arcoshDenom_def z
  have hz_add : z + 1 ∈ Complex.slitPlane := by
    convert ofReal_add_mem_slitPlane hz zero_le_two using 1; push_cast; ring
  have hz1 : (z + 1) / 2 ∈ Complex.slitPlane := by
    simpa using div_ofReal_mem_slitPlane hz_add zero_lt_two
  have hz2 : (z - 1) / 2 ∈ Complex.slitPlane := by
    simpa using div_ofReal_mem_slitPlane hz zero_lt_two
  have hden := arcoshDenom_ne_zero hz
  have ha0 : a ≠ 0 := fun h0 ↦ hden (by rw [hden_eq, h0]; ring)
  have hb0 : b ≠ 0 := fun h0 ↦ hden (by rw [hden_eq, h0]; ring)
  have hda : HasDerivAt (fun w : ℂ ↦ ((w + 1) / 2) ^ (1 / 2 : ℂ)) ((4 * a)⁻¹) z := by
    refine ((((hasDerivAt_id' z).add_const 1).div_const 2).cpow_half hz1).congr_deriv ?_
    rw [← ha_def]; field_simp [ha0]; norm_num
  have hdb : HasDerivAt (fun w : ℂ ↦ ((w - 1) / 2) ^ (1 / 2 : ℂ)) ((4 * b)⁻¹) z := by
    refine ((((hasDerivAt_id' z).sub_const 1).div_const 2).cpow_half hz2).congr_deriv ?_
    rw [← hb_def]; field_simp [hb0]; norm_num
  have hd_root : HasDerivAt arcoshRoot ((4 * a)⁻¹ + (4 * b)⁻¹) z :=
    (hda.add hdb).congr_of_eventuallyEq (Eventually.of_forall arcoshRoot_def)
  refine (HasDerivAt.clog hd_root (arcoshRoot_mem_slitPlane z)).congr_deriv ?_
  have hab : a + b ≠ 0 := by rw [← hroot_eq]; exact arcoshRoot_ne_zero z
  rw [hroot_eq, hden_eq]
  field_simp [ha0, hb0, hab]; ring

private theorem hasDerivAt_arcoshDenom {z : ℂ} (hz : z - 1 ∈ Complex.slitPlane) :
    HasDerivAt arcoshDenom (z / arcoshDenom z) z := by
  have hz_add : z + 1 ∈ Complex.slitPlane := by
    convert ofReal_add_mem_slitPlane hz zero_le_two using 1; push_cast; ring
  have hz1 : (z + 1) / 2 ∈ Complex.slitPlane := by
    simpa using div_ofReal_mem_slitPlane hz_add zero_lt_two
  have hz2 : (z - 1) / 2 ∈ Complex.slitPlane := by
    simpa using div_ofReal_mem_slitPlane hz zero_lt_two
  have hdr : DifferentiableAt ℂ arcoshDenom z :=
    ((((differentiableAt_id (x := z)).add_const 1).div_const 2).cpow_const hz1 |>.const_mul 2).mul
      (((differentiableAt_id (x := z)).sub_const 1).div_const 2 |>.cpow_const hz2)
  have h1 : HasDerivAt (arcoshDenom ^ 2) (2 * arcoshDenom z * deriv arcoshDenom z) z := by
    simpa [pow_one] using hdr.hasDerivAt.pow 2
  have h2 : HasDerivAt (fun w : ℂ ↦ w ^ 2 - 1) (2 * z) z := by
    simpa using ((hasDerivAt_id' z).pow 2).sub_const 1
  have hfun : (arcoshDenom ^ 2 : ℂ → ℂ) = fun w : ℂ ↦ w ^ 2 - 1 := funext arcoshDenom_sq
  have heq : 2 * arcoshDenom z * deriv arcoshDenom z = 2 * z := h1.unique (hfun ▸ h2)
  refine hdr.hasDerivAt.congr_deriv ?_
  field_simp [arcoshDenom_ne_zero hz]; linear_combination heq / 2

private theorem coshMulArcosh_ode_of_sub_one (p : ℂ) {z : ℂ} (hz : z - 1 ∈ Complex.slitPlane) :
    (z ^ 2 - 1) * deriv (deriv (coshMulArcosh p)) z + z * deriv (coshMulArcosh p) z =
      p ^ 2 * coshMulArcosh p z := by
  have hcongr : coshMulArcosh p = fun u ↦ Complex.cosh (2 * p * Complex.log (arcoshRoot u)) :=
    funext (coshMulArcosh_eq_cosh_two_mul_log p)
  have hev : (fun w ↦ arcoshDenom w * deriv (coshMulArcosh p) w) =ᶠ[𝓝 z]
      fun w ↦ p * Complex.sinh (2 * p * Complex.log (arcoshRoot w)) := by
    filter_upwards [(isOpen_slitPlane.preimage (continuous_sub_right 1)).mem_nhds hz] with w hw
    have hcosh : HasDerivAt (fun u ↦ Complex.cosh (2 * p * Complex.log (arcoshRoot u)))
        (Complex.sinh (2 * p * Complex.log (arcoshRoot w)) *
          (2 * p * (2 * arcoshDenom w)⁻¹)) w :=
      (Complex.hasDerivAt_cosh _).comp w ((hasDerivAt_arcoshRoot_log hw).const_mul (2 * p))
    rw [hcongr, hcosh.deriv]; field_simp [arcoshDenom_ne_zero hw]
  have hz_add : z + 1 ∈ Complex.slitPlane := by
    convert ofReal_add_mem_slitPlane hz zero_le_two using 1; push_cast; ring
  have hL := (hasDerivAt_arcoshDenom hz).mul
    ((analyticOnNhd_coshMulArcosh p).deriv _ hz_add).differentiableAt.hasDerivAt
  have hR : HasDerivAt (fun w ↦ p * Complex.sinh (2 * p * Complex.log (arcoshRoot w)))
      (p ^ 2 * coshMulArcosh p z / arcoshDenom z) z := by
    refine (((Complex.hasDerivAt_sinh _).comp z
      ((hasDerivAt_arcoshRoot_log hz).const_mul (2 * p))).const_mul p).congr_deriv ?_
    rw [arcoshRoot_def, ← coshMulArcosh_eq_cosh_two_mul_log p z]
    field_simp [arcoshDenom_ne_zero hz]
  have hkey := (hL.congr_of_eventuallyEq hev.symm).unique hR
  rw [← arcoshDenom_sq z]
  field_simp [arcoshDenom_ne_zero hz] at hkey
  linear_combination hkey

/-- Chebyshev's differential equation `(z² - 1) f''(z) + z f'(z) = p² f(z)` holds for
`coshMulArcosh p` throughout `{z : ℂ | z + 1 ∈ Complex.slitPlane}`. -/
theorem coshMulArcosh_ode (p : ℂ) {z : ℂ} (hz : z + 1 ∈ Complex.slitPlane) :
    (z ^ 2 - 1) * deriv (deriv (coshMulArcosh p)) z + z * deriv (coshMulArcosh p) z =
      p ^ 2 * coshMulArcosh p z := by
  set U := {w : ℂ | w + 1 ∈ Complex.slitPlane}
  have hf := analyticOnNhd_coshMulArcosh p
  have hL : AnalyticOnNhd ℂ
      (fun w ↦ (w ^ 2 - 1) * deriv (deriv (coshMulArcosh p)) w + w * deriv (coshMulArcosh p) w) U :=
    (((analyticOnNhd_id.pow 2).sub analyticOnNhd_const).mul hf.deriv.deriv).add
      (analyticOnNhd_id.mul hf.deriv)
  have hR : AnalyticOnNhd ℂ (fun w ↦ p ^ 2 * coshMulArcosh p w) U :=
    analyticOnNhd_const.mul hf
  have hpre : IsPreconnected U := by
    have heq : U = (· - 1) '' Complex.slitPlane := by ext w; simp [U, sub_eq_iff_eq_add]
    rw [heq]
    have hpc := starConvex_one_slitPlane.isPathConnected one_mem_slitPlane
    exact hpc.isConnected.isPreconnected.image _ (Continuous.continuousOn (by fun_prop))
  have hev : (fun w ↦ (w ^ 2 - 1) * deriv (deriv (coshMulArcosh p)) w +
      w * deriv (coshMulArcosh p) w) =ᶠ[𝓝 (2 : ℂ)] fun w ↦ p ^ 2 * coshMulArcosh p w := by
    have hopen : IsOpen {w : ℂ | w - 1 ∈ Complex.slitPlane} :=
      isOpen_slitPlane.preimage (by fun_prop)
    filter_upwards [hopen.mem_nhds (by simp [mem_slitPlane_iff])] with w hw
    exact coshMulArcosh_ode_of_sub_one p hw
  have h2U : (2 : ℂ) ∈ U := by simp [U, mem_slitPlane_iff]; norm_num
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR hpre h2U hev hz

/-- The derivative of `coshMulArcosh p` at `z = 1` is `p²`. -/
@[simp]
theorem deriv_coshMulArcosh_one (p : ℂ) : deriv (coshMulArcosh p) 1 = p ^ 2 := by
  have h := coshMulArcosh_ode p (z := 1) (by simp [mem_slitPlane_iff])
  simpa [coshMulArcosh_one_right] using h

/-! ### The Schläfli–Laplace amplitude and its differential equation -/

/-- The Schläfli–Laplace amplitude `h_p(w) = coshMulArcosh p (1 + w) / (w + 2) ^ (1 / 2 : ℂ)`,
which transforms Schläfli's integral under `τ = cosh u - 1` into a Laplace integral on `(0, ∞)`. -/
def schlafliAmplitude (p w : ℂ) : ℂ :=
  coshMulArcosh p (1 + w) / (w + 2) ^ (1 / 2 : ℂ)

/-- The defining formula for `schlafliAmplitude`. -/
theorem schlafliAmplitude_def (p w : ℂ) :
    schlafliAmplitude p w = coshMulArcosh p (1 + w) / (w + 2) ^ (1 / 2 : ℂ) := (rfl)

/-- At `w = 0`, `schlafliAmplitude p 0 = 2 ^ (-1 / 2 : ℂ)`. -/
@[simp]
theorem schlafliAmplitude_zero_right (p : ℂ) :
    schlafliAmplitude p 0 = (2 : ℂ) ^ (-(1 / 2 : ℂ)) := by
  rw [schlafliAmplitude_def, add_zero, zero_add, coshMulArcosh_one_right, one_div, cpow_neg]

/-- `schlafliAmplitude p w` is an even function of the order parameter `p`. -/
@[simp]
theorem schlafliAmplitude_neg_left (p w : ℂ) :
    schlafliAmplitude (-p) w = schlafliAmplitude p w := by
  simp [schlafliAmplitude_def]

/-- At order `0`, `schlafliAmplitude 0 w = (w + 2) ^ (-1 / 2 : ℂ)`. -/
@[simp]
theorem schlafliAmplitude_zero_left (w : ℂ) :
    schlafliAmplitude 0 w = (w + 2) ^ (-(1 / 2 : ℂ)) := by
  rw [schlafliAmplitude_def, coshMulArcosh_zero_left, one_div, cpow_neg]

/-- At order `2⁻¹`, `schlafliAmplitude 2⁻¹ w` is the constant `2 ^ (-1 / 2 : ℂ)` away from
`w = -2`. -/
theorem schlafliAmplitude_inv_two_left {w : ℂ} (hw : w + 2 ≠ 0) :
    schlafliAmplitude 2⁻¹ w = (2 : ℂ) ^ (-(1 / 2 : ℂ)) := by
  have h1 : (1 + w + 1) / 2 = ((2⁻¹ : ℝ) : ℂ) * (w + 2) := by push_cast; ring
  have h2 : ((2⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (2 : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [ofReal_inv, inv_cpow_ofReal_nonneg zero_le_two, ofReal_ofNat, ← cpow_neg]
  rw [schlafliAmplitude_def, coshMulArcosh_inv_two_left, h1,
    ofReal_mul_cpow (by positivity) (w + 2) (1 / 2 : ℂ), h2,
    mul_div_cancel_right₀ _ (by simp [hw])]

/-- For fixed `w`, `p ↦ schlafliAmplitude p w` is an entire function. -/
@[fun_prop]
theorem differentiable_schlafliAmplitude_left (w : ℂ) :
    Differentiable ℂ (fun p : ℂ ↦ schlafliAmplitude p w) := by
  simp_rw [schlafliAmplitude_def]
  fun_prop

/-- On `[0, ∞)`, `schlafliAmplitude p τ` equals `cosh(p arcosh(1 + τ)) / √(τ + 2)`. -/
theorem schlafliAmplitude_ofReal (p : ℂ) {τ : ℝ} (hτ : 0 ≤ τ) :
    schlafliAmplitude p τ =
      Complex.cosh (p * Real.arcosh (1 + τ)) / (Real.sqrt (τ + 2) : ℂ) := by
  have h1 : (1 : ℂ) + τ = ((1 + τ : ℝ) : ℂ) := by push_cast; ring
  have h2 : (τ : ℂ) + 2 = ((τ + 2 : ℝ) : ℂ) := by push_cast; ring
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [schlafliAmplitude_def, h1, coshMulArcosh_ofReal_eq_cosh_mul_arcosh p (by linarith),
    h2, hhalf, ← ofReal_cpow (by linarith), Real.sqrt_eq_rpow]

/-- Under `τ = cosh u - 1`, `schlafliAmplitude p (cosh u - 1)` simplifies to
`cosh(p u) / √(cosh u + 1)`. -/
theorem schlafliAmplitude_ofReal_cosh_sub_one (p : ℂ) (u : ℝ) :
    schlafliAmplitude p (Real.cosh u - 1 : ℝ) =
      Complex.cosh (p * u) / (Real.sqrt (Real.cosh u + 1) : ℂ) := by
  have hτ : 0 ≤ Real.cosh u - 1 := sub_nonneg.mpr (Real.one_le_cosh u)
  have h2 : Real.cosh u - 1 + 2 = Real.cosh u + 1 := by ring
  rw [schlafliAmplitude_ofReal p hτ, add_sub_cancel, h2,
    ← coshMulArcosh_ofReal_eq_cosh_mul_arcosh p (Real.one_le_cosh u), ofReal_cosh,
    coshMulArcosh_cosh_ofReal]

/-- `schlafliAmplitude p` is holomorphic on `{w : ℂ | w + 2 ∈ Complex.slitPlane}`. -/
theorem differentiableOn_schlafliAmplitude (p : ℂ) :
    DifferentiableOn ℂ (schlafliAmplitude p) {w : ℂ | w + 2 ∈ Complex.slitPlane} := by
  intro w hw
  have hw2 : w + 2 ∈ Complex.slitPlane := hw
  have h1w : (1 + w) + 1 ∈ Complex.slitPlane := by convert hw2 using 1; ring
  have hopen : IsOpen {z : ℂ | z + 1 ∈ Complex.slitPlane} :=
    isOpen_slitPlane.preimage (continuous_add_const 1)
  have hnum : DifferentiableAt ℂ (fun z : ℂ ↦ coshMulArcosh p (1 + z)) w :=
    ((differentiableOn_coshMulArcosh p).differentiableAt (hopen.mem_nhds h1w)).comp w
      (differentiableAt_id.const_add 1)
  have hden : DifferentiableAt ℂ (fun z : ℂ ↦ (z + 2) ^ (1 / 2 : ℂ)) w :=
    (differentiableAt_id.add_const 2).cpow_const hw2
  exact (hnum.div hden (by simp [slitPlane_ne_zero hw2])).differentiableWithinAt

/-- `schlafliAmplitude p` is holomorphic on `Complex.slitPlane`. -/
theorem differentiableOn_schlafliAmplitude_slitPlane (p : ℂ) :
    DifferentiableOn ℂ (schlafliAmplitude p) Complex.slitPlane :=
  (differentiableOn_schlafliAmplitude p).mono fun _ hw ↦ by
    simpa [add_comm] using ofReal_add_mem_slitPlane hw zero_le_two

/-- `schlafliAmplitude p` is complex analytic on `{w : ℂ | w + 2 ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_schlafliAmplitude (p : ℂ) :
    AnalyticOnNhd ℂ (schlafliAmplitude p) {w : ℂ | w + 2 ∈ Complex.slitPlane} :=
  (differentiableOn_schlafliAmplitude p).analyticOnNhd
    (isOpen_slitPlane.preimage (continuous_add_const 2))

/-- `schlafliAmplitude p` is complex analytic at the origin. -/
theorem analyticAt_schlafliAmplitude_zero (p : ℂ) :
    AnalyticAt ℂ (schlafliAmplitude p) 0 :=
  analyticOnNhd_schlafliAmplitude p 0 (by simp [mem_slitPlane_iff])

private theorem hasDerivAt_coshMulArcosh_one_add (p : ℂ) {w : ℂ}
    (hw : w + 2 ∈ Complex.slitPlane) :
    HasDerivAt (fun u ↦ coshMulArcosh p (1 + u))
      ((w + 2) ^ (1 / 2 : ℂ) * deriv (schlafliAmplitude p) w +
        (2 * (w + 2) ^ (1 / 2 : ℂ))⁻¹ * schlafliAmplitude p w) w := by
  have hdr : HasDerivAt (fun z : ℂ ↦ (z + 2) ^ (1 / 2 : ℂ))
      ((2 * (w + 2) ^ (1 / 2 : ℂ))⁻¹) w := by
    simpa [one_div] using ((hasDerivAt_id' w).add_const 2).cpow_half hw
  have hd := hdr.mul (analyticOnNhd_schlafliAmplitude p w hw).differentiableAt.hasDerivAt
  have hev : (fun u ↦ coshMulArcosh p (1 + u)) =ᶠ[𝓝 w]
      fun u ↦ (u + 2) ^ (1 / 2 : ℂ) * schlafliAmplitude p u := by
    filter_upwards [(isOpen_slitPlane.preimage (continuous_add_const 2)).mem_nhds hw] with z hz
    rw [schlafliAmplitude_def, mul_div_cancel₀ _ (by simp [slitPlane_ne_zero hz])]
  exact (hd.congr_of_eventuallyEq hev).congr_deriv (by ring)

private theorem deriv2_coshMulArcosh_one_add (p : ℂ) {w : ℂ}
    (hw : w + 2 ∈ Complex.slitPlane) :
    deriv (deriv (coshMulArcosh p)) (1 + w) =
      (w + 2) ^ (1 / 2 : ℂ) * deriv (deriv (schlafliAmplitude p)) w +
        ((w + 2) ^ (1 / 2 : ℂ))⁻¹ * deriv (schlafliAmplitude p) w -
          (4 * ((w + 2) ^ (1 / 2 : ℂ)) ^ 3)⁻¹ * schlafliAmplitude p w := by
  set r : ℂ → ℂ := fun z ↦ (z + 2) ^ (1 / 2 : ℂ)
  have hw0 : r w ≠ 0 := by simp [r, slitPlane_ne_zero hw]
  have hdr : HasDerivAt r ((2 * r w)⁻¹) w := by
    simpa [r, one_div] using ((hasDerivAt_id' w).add_const 2).cpow_half hw
  have hd_inv : HasDerivAt (fun z ↦ (2 * r z)⁻¹) (-(4 * r w ^ 3)⁻¹) w := by
    refine ((hdr.const_mul (2 : ℂ)).inv (mul_ne_zero two_ne_zero hw0)).congr_deriv ?_
    field_simp [hw0]; ring
  have hh_an := analyticOnNhd_schlafliAmplitude p
  have hsum := (hdr.mul (hh_an.deriv w hw).differentiableAt.hasDerivAt).add
    (hd_inv.mul (hh_an w hw).differentiableAt.hasDerivAt)
  have hev : deriv (fun u ↦ coshMulArcosh p (1 + u)) =ᶠ[𝓝 w]
      fun z ↦ r z * deriv (schlafliAmplitude p) z + (2 * r z)⁻¹ * schlafliAmplitude p z :=
    Filter.Eventually.mono ((isOpen_slitPlane.preimage (continuous_add_const 2)).mem_nhds hw)
      fun z hz ↦ (hasDerivAt_coshMulArcosh_one_add p hz).deriv
  have hc1 : deriv (fun u ↦ coshMulArcosh p (1 + u)) = fun u ↦ deriv (coshMulArcosh p) (1 + u) :=
    funext (deriv_comp_const_add (coshMulArcosh p) 1)
  rw [← deriv_comp_const_add (deriv (coshMulArcosh p)) 1 w, ← hc1,
    (hsum.congr_of_eventuallyEq hev).deriv]
  dsimp [r]; field_simp [hw0]; ring

/-- `schlafliAmplitude p` satisfies the two-term hypergeometric differential equation
`w (w + 2) h''(w) + (2 w + 1) h'(w) + (1 / 4 - p²) h(w) = 0` on
`{w : ℂ | w + 2 ∈ Complex.slitPlane}`. -/
theorem schlafliAmplitude_ode (p : ℂ) {w : ℂ} (hw : w + 2 ∈ Complex.slitPlane) :
    w * (w + 2) * deriv (deriv (schlafliAmplitude p)) w +
      (2 * w + 1) * deriv (schlafliAmplitude p) w +
        (1 / 4 - p ^ 2) * schlafliAmplitude p w = 0 := by
  set h := schlafliAmplitude p
  set r := (w + 2) ^ (1 / 2 : ℂ)
  have hrsq : r ^ 2 = w + 2 := by simp [r, one_div]
  have hw2 : w + 2 ≠ 0 := slitPlane_ne_zero hw
  have hr0 : r ≠ 0 := by simp [r, hw2]
  have hd1 : deriv (coshMulArcosh p) (1 + w) = r * deriv h w + (2 * r)⁻¹ * h w := by
    rw [← deriv_comp_const_add (coshMulArcosh p) 1 w, (hasDerivAt_coshMulArcosh_one_add p hw).deriv]
  have hd2 : deriv (deriv (coshMulArcosh p)) (1 + w) =
      r * deriv (deriv h) w + r⁻¹ * deriv h w - (4 * r ^ 3)⁻¹ * h w :=
    deriv2_coshMulArcosh_one_add p hw
  have hfg : coshMulArcosh p (1 + w) = r * h w := by
    dsimp [h, r]; rw [schlafliAmplitude_def, mul_div_cancel₀ _ hr0]
  have hode := coshMulArcosh_ode p (z := 1 + w) (by convert hw using 1; ring)
  rw [hd1, hd2, hfg] at hode
  have hode' : ((1 + w) ^ 2 - 1) * (4 * (r ^ 2) ^ 2 * deriv (deriv h) w + 4 * r ^ 2 * deriv h w -
      h w) + (1 + w) * (4 * (r ^ 2) ^ 2 * deriv h w + 2 * r ^ 2 * h w) -
        4 * p ^ 2 * (r ^ 2) ^ 2 * h w = 0 := by
    field_simp [hr0] at hode; linear_combination hode / 2
  rw [hrsq] at hode'
  have hmul : 4 * (w + 2) ^ 2 * (w * (w + 2) * deriv (deriv h) w +
      (2 * w + 1) * deriv h w + (1 / 4 - p ^ 2) * h w) = 0 := by linear_combination hode'
  exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero 2 hw2))

/-! ### Hankel's coefficients and the Maclaurin series of `schlafliAmplitude` -/

/-- Hankel's asymptotic coefficient `a_k(p) = (∏_{j < k} (4 p² - (2 j + 1)²)) / (8 ^ k * k!)`
(DLMF 10.17.1). -/
def hankelCoeff (p : ℂ) (k : ℕ) : ℂ :=
  (∏ j ∈ Finset.range k, (4 * p ^ 2 - (2 * (j : ℂ) + 1) ^ 2)) / ((8 : ℂ) ^ k * (k ! : ℂ))

/-- The defining formula for `hankelCoeff`. -/
theorem hankelCoeff_def (p : ℂ) (k : ℕ) :
    hankelCoeff p k =
      (∏ j ∈ Finset.range k, (4 * p ^ 2 - (2 * (j : ℂ) + 1) ^ 2)) /
        ((8 : ℂ) ^ k * (k ! : ℂ)) := (rfl)

/-- The `0`-th Hankel coefficient is `1`. -/
@[simp]
theorem hankelCoeff_zero (p : ℂ) : hankelCoeff p 0 = 1 := by
  simp [hankelCoeff_def]

/-- The first Hankel coefficient is `(4 p² - 1) / 8`. -/
theorem hankelCoeff_one (p : ℂ) : hankelCoeff p 1 = (4 * p ^ 2 - 1) / 8 := by
  simp [hankelCoeff_def]

/-- First-order recurrence for Hankel's asymptotic coefficients `hankelCoeff p k`. -/
theorem hankelCoeff_succ (p : ℂ) (k : ℕ) :
    hankelCoeff p (k + 1) =
      hankelCoeff p k * (4 * p ^ 2 - (2 * (k : ℂ) + 1) ^ 2) / (8 * ((k : ℂ) + 1)) := by
  simp only [hankelCoeff_def, Finset.prod_range_succ, pow_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

/-- `hankelCoeff p k` is an even function of `p`. -/
@[simp]
theorem hankelCoeff_neg (p : ℂ) (k : ℕ) : hankelCoeff (-p) k = hankelCoeff p k := by
  simp [hankelCoeff_def]

/-- At positive half-integer orders `m + 2⁻¹`, Hankel's coefficients `hankelCoeff (m + 2⁻¹) k`
vanish for all `k > m`, reflecting the finite termination of Hankel's expansion for half-integer
Bessel functions. -/
theorem hankelCoeff_natCast_add_inv_two_of_lt {m k : ℕ} (hmk : m < k) :
    hankelCoeff ((m : ℂ) + 2⁻¹) k = 0 := by
  rw [hankelCoeff_def, Finset.prod_eq_zero (Finset.mem_range.mpr hmk), zero_div]
  field_simp
  ring

/-- At order `p = 2⁻¹`, all positive-index Hankel coefficients vanish, reflecting the exact
exponential form of `K_{1/2}`. -/
@[simp]
theorem hankelCoeff_inv_two_succ (k : ℕ) : hankelCoeff 2⁻¹ (k + 1) = 0 := by
  simpa using hankelCoeff_natCast_add_inv_two_of_lt (Nat.zero_lt_succ k)

/-- The `k`-th Maclaurin coefficient `2 ^ (-1 / 2 : ℂ) * hankelCoeff p k / (1 / 2)_k` of
`schlafliAmplitude p` at `w = 0`. -/
def schlafliAmplitudeCoeff (p : ℂ) (k : ℕ) : ℂ :=
  (2 : ℂ) ^ (-(1 / 2 : ℂ)) * hankelCoeff p k / (ascPochhammer ℂ k).eval (1 / 2 : ℂ)

/-- The defining formula for `schlafliAmplitudeCoeff`. -/
theorem schlafliAmplitudeCoeff_def (p : ℂ) (k : ℕ) :
    schlafliAmplitudeCoeff p k =
      (2 : ℂ) ^ (-(1 / 2 : ℂ)) * hankelCoeff p k / (ascPochhammer ℂ k).eval (1 / 2 : ℂ) := (rfl)

/-- The formal power series of `schlafliAmplitude p` centered at `0`. -/
def schlafliAmplitudeSeries (p : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (schlafliAmplitudeCoeff p)

/-- The defining formula for `schlafliAmplitudeSeries`. -/
theorem schlafliAmplitudeSeries_def (p : ℂ) :
    schlafliAmplitudeSeries p =
      FormalMultilinearSeries.ofScalars ℂ (schlafliAmplitudeCoeff p) := (rfl)

/-- The constant Maclaurin coefficient of `schlafliAmplitude p` is `2 ^ (-1 / 2 : ℂ)`. -/
@[simp]
theorem schlafliAmplitudeCoeff_zero (p : ℂ) :
    schlafliAmplitudeCoeff p 0 = (2 : ℂ) ^ (-(1 / 2 : ℂ)) := by
  simp [schlafliAmplitudeCoeff_def]

/-- The linear Maclaurin coefficient of `schlafliAmplitude p` is
`2 ^ (-1 / 2 : ℂ) * (p² - 1 / 4)`. -/
theorem schlafliAmplitudeCoeff_one (p : ℂ) :
    schlafliAmplitudeCoeff p 1 = (2 : ℂ) ^ (-(1 / 2 : ℂ)) * (p ^ 2 - 1 / 4) := by
  rw [schlafliAmplitudeCoeff_def, hankelCoeff_one, ascPochhammer_one, Polynomial.eval_X]
  ring

/-- First-order recurrence for the Maclaurin coefficients `schlafliAmplitudeCoeff p k`. -/
theorem schlafliAmplitudeCoeff_succ (p : ℂ) (k : ℕ) :
    schlafliAmplitudeCoeff p (k + 1) =
      schlafliAmplitudeCoeff p k * (4 * p ^ 2 - (2 * (k : ℂ) + 1) ^ 2) /
        (4 * ((k : ℂ) + 1) * (2 * (k : ℂ) + 1)) := by
  have hp0 : (ascPochhammer ℂ k).eval (1 / 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, ascPochhammer_eval_eq_zero_iff, not_exists, not_and]
    exact fun m _ hm ↦ Complex.ne_neg_natCast_of_re_pos (b := (1 / 2 : ℂ)) (by norm_num) m
      (neg_eq_iff_eq_neg.mp hm.symm)
  have hk1 : (k : ℂ) + 1 ≠ 0 := mod_cast Nat.succ_ne_zero k
  have hk2 : 2 * (k : ℂ) + 1 ≠ 0 := mod_cast Nat.succ_ne_zero (2 * k)
  rw [schlafliAmplitudeCoeff_def, schlafliAmplitudeCoeff_def, hankelCoeff_succ,
    ascPochhammer_succ_eval]
  have heq : (1 / 2 : ℂ) + k = (2 * (k : ℂ) + 1) / 2 := by ring
  rw [heq]
  field_simp [hk1, hk2, hp0]
  ring

/-- `schlafliAmplitudeCoeff p k` is an even function of `p`. -/
@[simp]
theorem schlafliAmplitudeCoeff_neg (p : ℂ) (k : ℕ) :
    schlafliAmplitudeCoeff (-p) k = schlafliAmplitudeCoeff p k := by
  simp [schlafliAmplitudeCoeff_def]

/-- At positive half-integer orders `m + 2⁻¹`, the Maclaurin coefficients
`schlafliAmplitudeCoeff (m + 2⁻¹) k` vanish for all `k > m`. -/
theorem schlafliAmplitudeCoeff_natCast_add_inv_two_of_lt {m k : ℕ} (hmk : m < k) :
    schlafliAmplitudeCoeff ((m : ℂ) + 2⁻¹) k = 0 := by
  simp [schlafliAmplitudeCoeff_def, hankelCoeff_natCast_add_inv_two_of_lt hmk]

/-- At order `p = 2⁻¹`, all positive-index Maclaurin coefficients of `schlafliAmplitude` vanish. -/
@[simp]
theorem schlafliAmplitudeCoeff_inv_two_succ (k : ℕ) :
    schlafliAmplitudeCoeff 2⁻¹ (k + 1) = 0 := by
  simpa using schlafliAmplitudeCoeff_natCast_add_inv_two_of_lt (Nat.zero_lt_succ k)

/-- The `k`-th scalar coefficient of `schlafliAmplitudeSeries p` is `schlafliAmplitudeCoeff p k`. -/
@[simp]
theorem coeff_schlafliAmplitudeSeries (p : ℂ) (k : ℕ) :
    (schlafliAmplitudeSeries p).coeff k = schlafliAmplitudeCoeff p k := by
  simp [schlafliAmplitudeSeries_def]

/-- The `N`-th partial sum of `schlafliAmplitudeSeries p` at `w` is
`∑ k ∈ Finset.range N, schlafliAmplitudeCoeff p k * w ^ k`. -/
theorem partialSum_schlafliAmplitudeSeries (p : ℂ) (N : ℕ) (w : ℂ) :
    (schlafliAmplitudeSeries p).partialSum N w =
      ∑ k ∈ Finset.range N, schlafliAmplitudeCoeff p k * w ^ k := by
  simp [FormalMultilinearSeries.partialSum, schlafliAmplitudeSeries_def, mul_comm]

/-- `schlafliAmplitudeSeries p` is an even function of `p`. -/
@[simp]
theorem schlafliAmplitudeSeries_neg (p : ℂ) :
    schlafliAmplitudeSeries (-p) = schlafliAmplitudeSeries p := by
  ext k; simp [schlafliAmplitudeSeries_def]

/-- Multiplying the `k`-th Maclaurin coefficient `schlafliAmplitudeCoeff p k` by `Γ(k + 1 / 2)`
recovers `(√(π / 2) : ℂ) * hankelCoeff p k`. -/
theorem Gamma_add_half_mul_schlafliAmplitudeCoeff (p : ℂ) (k : ℕ) :
    Complex.Gamma ((k : ℂ) + 1 / 2) * schlafliAmplitudeCoeff p k =
      (Real.sqrt (Real.pi / 2) : ℂ) * hankelCoeff p k := by
  have hno_pole : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -(m : ℂ) :=
    Complex.ne_neg_natCast_of_re_pos (by norm_num)
  have hpoch0 : (ascPochhammer ℂ k).eval (1 / 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, ascPochhammer_eval_eq_zero_iff, not_exists, not_and]
    exact fun m _ hm ↦ hno_pole m (neg_eq_iff_eq_neg.mp hm.symm)
  have hgam : Complex.Gamma ((k : ℂ) + 1 / 2) =
      Complex.Gamma (1 / 2 : ℂ) * (ascPochhammer ℂ k).eval (1 / 2 : ℂ) := by
    rw [add_comm, ← Complex.Gamma_add_nat_div_Gamma_eq (n := k) (1 / 2 : ℂ) hno_pole,
      mul_div_cancel₀ _ (Complex.Gamma_ne_zero hno_pole)]
  have h2 : (2 : ℂ) ^ (-(1 / 2 : ℂ)) = ((Real.sqrt 2)⁻¹ : ℝ) := by
    rw [cpow_neg, ofReal_inv, Real.sqrt_eq_rpow, ofReal_cpow zero_le_two]; push_cast; rfl
  have hpi : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℝ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; rfl
  have hsqrt : (Real.sqrt Real.pi : ℂ) * ((Real.sqrt 2)⁻¹ : ℝ) = Real.sqrt (Real.pi / 2) := by
    norm_cast; rw [Real.sqrt_div Real.pi_pos.le, div_eq_mul_inv]
  rw [schlafliAmplitudeCoeff_def, hgam, Complex.Gamma_one_half_eq, hpi, h2, ← hsqrt]
  field_simp [hpoch0]

private theorem iteratedDeriv_schlafliAmplitude_recurrence (p : ℂ) (k : ℕ) :
    (2 * (k : ℂ) + 1) * iteratedDeriv (k + 1) (schlafliAmplitude p) 0 +
      ((k : ℂ) * ((k : ℂ) - 1) + 2 * (k : ℂ) + (1 / 4 - p ^ 2)) *
        iteratedDeriv k (schlafliAmplitude p) 0 = 0 := by
  set h := schlafliAmplitude p
  have han : AnalyticAt ℂ h 0 := analyticAt_schlafliAmplitude_zero p
  have hc1 : ContDiffAt ℂ k (iteratedDeriv 1 h) 0 := by
    simpa [iteratedDeriv_one] using han.deriv.contDiffAt
  have hc2 : ContDiffAt ℂ k (iteratedDeriv 2 h) 0 := by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using han.deriv.deriv.contDiffAt
  have hm2 : ContDiffAt ℂ k (fun w : ℂ ↦ w ^ 2 * iteratedDeriv 2 h w) 0 :=
    (contDiffAt_id.pow 2).mul hc2
  have hm12 : ContDiffAt ℂ k (fun w : ℂ ↦ 2 * (w * iteratedDeriv 2 h w)) 0 :=
    contDiffAt_const.mul (contDiffAt_id.mul hc2)
  have hm11 : ContDiffAt ℂ k (fun w : ℂ ↦ 2 * (w * iteratedDeriv 1 h w)) 0 :=
    contDiffAt_const.mul (contDiffAt_id.mul hc1)
  have hev : (fun w : ℂ ↦ (w ^ 2 * iteratedDeriv 2 h w + 2 * (w * iteratedDeriv 2 h w)) +
      (2 * (w * iteratedDeriv 1 h w) + iteratedDeriv 1 h w) + (1 / 4 - p ^ 2) * h w) =ᶠ[𝓝 (0 : ℂ)]
      0 := by
    filter_upwards [(isOpen_slitPlane.preimage (continuous_add_const 2)).mem_nhds (by simp)]
      with w hw
    dsimp [Pi.zero_apply]; rw [iteratedDeriv_succ, iteratedDeriv_one]
    linear_combination schlafliAmplitude_ode p hw
  have hit0 := hev.iteratedDeriv_eq k (x := 0)
  rw [iteratedDeriv_const_zero,
    iteratedDeriv_fun_add ((hm2.add hm12).add (hm11.add hc1)) (contDiffAt_const.mul han.contDiffAt),
    iteratedDeriv_fun_add (hm2.add hm12) (hm11.add hc1),
    iteratedDeriv_fun_add hm2 hm12, iteratedDeriv_fun_add hm11 hc1] at hit0
  simp only [iteratedDeriv_const_mul_field] at hit0
  have h22 : iteratedDeriv k (fun w : ℂ ↦ w ^ 2 * iteratedDeriv 2 h w) 0 =
      (k : ℂ) * ((k : ℂ) - 1) * iteratedDeriv k h 0 := by
    have h2 : iteratedDeriv k (fun w : ℂ ↦ w ^ 2 * iteratedDeriv 2 h w) 0 =
        ((k - 1 : ℕ) : ℂ) * (k : ℂ) * iteratedDeriv k h 0 := by
      simpa [sub_zero, nsmul_eq_mul] using
        iteratedDeriv_pow_sub_smul_iteratedDeriv k 2 2 (a := (0 : ℂ)) hc2
    rw [h2]; cases k with | zero => simp | succ m => push_cast; ring
  have h12 : iteratedDeriv k (fun w : ℂ ↦ w * iteratedDeriv 2 h w) 0 =
      (k : ℂ) * iteratedDeriv (k + 1) h 0 := by
    simpa [sub_zero, nsmul_eq_mul] using
      iteratedDeriv_pow_sub_smul_iteratedDeriv k 1 2 (a := (0 : ℂ)) hc2
  have h11 : iteratedDeriv k (fun w : ℂ ↦ w * iteratedDeriv 1 h w) 0 =
      (k : ℂ) * iteratedDeriv k h 0 := by
    simpa [sub_zero, nsmul_eq_mul] using
      iteratedDeriv_pow_sub_smul_iteratedDeriv k 1 1 (a := (0 : ℂ)) hc1
  have h1_iter : iteratedDeriv k (iteratedDeriv 1 h) 0 = iteratedDeriv (k + 1) h 0 := by
    simp [iteratedDeriv_eq_iterate]
  rw [h22, h12, h11, h1_iter] at hit0
  linear_combination hit0

/-- The `k`-th derivative of `schlafliAmplitude p` at `0` equals
`k! * schlafliAmplitudeCoeff p k`. -/
theorem iteratedDeriv_schlafliAmplitude_zero (p : ℂ) (k : ℕ) :
    iteratedDeriv k (schlafliAmplitude p) 0 = (k ! : ℂ) * schlafliAmplitudeCoeff p k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hrec := iteratedDeriv_schlafliAmplitude_recurrence p k
    rw [ih] at hrec
    have hk1 : (k : ℂ) + 1 ≠ 0 := mod_cast Nat.succ_ne_zero k
    have hk2 : 2 * (k : ℂ) + 1 ≠ 0 := mod_cast Nat.succ_ne_zero (2 * k)
    rw [schlafliAmplitudeCoeff_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hk2)
    have hrhs : 4 * (2 * (k : ℂ) + 1) * (((k : ℂ) + 1) * (k ! : ℂ) *
        (schlafliAmplitudeCoeff p k * (4 * p ^ 2 - (2 * (k : ℂ) + 1) ^ 2) /
          (4 * ((k : ℂ) + 1) * (2 * (k : ℂ) + 1)))) =
        (k ! : ℂ) * schlafliAmplitudeCoeff p k * (4 * p ^ 2 - (2 * (k : ℂ) + 1) ^ 2) := by
      field_simp [hk1, hk2]
    rw [hrhs]
    linear_combination 4 * hrec

/-- The derivative of `schlafliAmplitude p` at `0` is `2 ^ (-1 / 2 : ℂ) * (p² - 1 / 4)`. -/
@[simp]
theorem deriv_schlafliAmplitude_zero (p : ℂ) :
    deriv (schlafliAmplitude p) 0 = (2 : ℂ) ^ (-(1 / 2 : ℂ)) * (p ^ 2 - 1 / 4) := by
  simpa [schlafliAmplitudeCoeff_one] using iteratedDeriv_schlafliAmplitude_zero p 1

/-- `schlafliAmplitude p` is represented by `schlafliAmplitudeSeries p` on the open disc
`Metric.ball 0 2`. -/
theorem hasFPowerSeriesOnBall_schlafliAmplitude (p : ℂ) :
    HasFPowerSeriesOnBall (schlafliAmplitude p) (schlafliAmplitudeSeries p) 0 2 := by
  have heq_series : FormalMultilinearSeries.ofScalars ℂ
      (fun k ↦ iteratedDeriv k (schlafliAmplitude p) 0 / (k ! : ℂ)) =
      schlafliAmplitudeSeries p := by
    rw [schlafliAmplitudeSeries_def]; congr 1; ext k
    rw [iteratedDeriv_schlafliAmplitude_zero,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))]
  have hr_ball (r : NNReal) (hr0 : 0 < r) (hr2 : (r : ℝ) < 2) :
      HasFPowerSeriesOnBall (schlafliAmplitude p) (schlafliAmplitudeSeries p) 0 r := by
    have hsub : Metric.closedBall (0 : ℂ) r ⊆ {w : ℂ | w + 2 ∈ Complex.slitPlane} := fun w hw ↦ by
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      exact mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [neg_abs_le w.re, abs_re_le_norm w]))
    have hcau := ((differentiableOn_schlafliAmplitude p).mono hsub).hasFPowerSeriesOnBall hr0
    rwa [hcau.hasFPowerSeriesAt.eq_formalMultilinearSeries
      (heq_series ▸ (analyticAt_schlafliAmplitude_zero p).hasFPowerSeriesAt)] at hcau
  refine ⟨ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_, by norm_num, fun {y} hy ↦ ?_⟩
  · rcases eq_or_ne r 0 with rfl | hr0
    · simp
    · exact (hr_ball r (pos_iff_ne_zero.mpr hr0) (by exact_mod_cast hr)).r_le
  · rw [← ENNReal.coe_ofNat, Metric.eball_coe, Metric.mem_ball, dist_zero_right,
      NNReal.coe_ofNat] at hy
    let r : NNReal := (‖y‖₊ + 2) / 2
    have hyr : y ∈ Metric.eball (0 : ℂ) r := by
      rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right]; dsimp [r]; linarith
    simpa using (hr_ball r (by positivity) (by dsimp [r]; linarith)).hasSum hyr

/-- The radius of convergence of `schlafliAmplitudeSeries p` is at least `2`. -/
theorem two_le_radius_schlafliAmplitudeSeries (p : ℂ) :
    2 ≤ (schlafliAmplitudeSeries p).radius :=
  (hasFPowerSeriesOnBall_schlafliAmplitude p).r_le

/-- For every `w` with `‖w‖ < 2`, the Maclaurin series of `schlafliAmplitude p` converges to
`schlafliAmplitude p w`. -/
theorem hasSum_schlafliAmplitude (p : ℂ) {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 2) :
    HasSum (fun k : ℕ ↦ schlafliAmplitudeCoeff p k * w ^ k) (schlafliAmplitude p w) := by
  have hmem : w ∈ Metric.eball (0 : ℂ) 2 := by
    rwa [← ENNReal.coe_ofNat, Metric.eball_coe, NNReal.coe_ofNat]
  simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff, mul_comm] using
    (hasFPowerSeriesOnBall_schlafliAmplitude p).hasSum hmem

end TauCeti

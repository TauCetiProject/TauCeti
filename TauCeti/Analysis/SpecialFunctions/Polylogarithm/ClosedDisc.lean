/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Polylogarithms on the closed unit disc

For a natural weight `n ≥ 2`, the principal polylogarithm `Liₙ = TauCeti.Polylog.polylog n` is
the sum of its power series `∑_{k ≥ 1} z ^ k / k ^ n` at every point of the **closed** unit disc,
and the series converges absolutely and uniformly there. At the boundary point `z = 1` this gives
the zeta value `Liₙ(1) = ζ(n)`, and on the unit circle `Liₙ(e^{2πia})` is Mathlib's exponential
zeta function `HurwitzZeta.expZeta a n`. Splitting the series at `z = -1` into even and odd
terms gives `Liₙ(-1) = (2 ^ (1 - n) - 1) ζ(n)`. In weight two, `Li₂(1) = π² / 6` and
`Li₂(-1) = -π² / 12`.

The series comes from the logarithmic radial integral that defines `Liₙ`. The substitution
`t = exp (-u)` turns it into `(1 / (n - 2)!) ∫₀^∞ u ^ (n - 2) (-Log (1 - e^{-u} z)) du`. For
`u > 0` and `‖z‖ ≤ 1` the logarithm is the sum of its Taylor series in `e^{-u} z`, and the
termwise integrals are the Gamma integrals `∫₀^∞ u ^ k e^{-ju} du = k! / j ^ (k + 1)`. Their
norms are at most `k! / j ^ (k + 2)`, which is summable, so the sum and the integral commute.
No limit from inside the disc is taken, so the boundary values are those of the defining
integral itself.

## Main declarations

* `TauCeti.Polylog.hasSum_polylog_of_norm_le_one`: the series on the closed unit disc.
* `TauCeti.Polylog.hasSumUniformlyOn_polylog_closedBall`: its uniform convergence there.
* `TauCeti.Polylog.polylog_exp_eq_expZeta`: the values on the unit circle.
* `TauCeti.Polylog.polylog_natCast_one_eq_riemannZeta`: the zeta value at `1`.
* `TauCeti.Polylog.polylog_natCast_neg_one_eq_mul_riemannZeta`: the value at `-1`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.1, (1), p. 50, and §1.4, p. 51.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics, and
  Geometry II (2007), Part I, §1, pp. 6–7.
-/

public section

open MeasureTheory Set Complex
open scoped Real

namespace TauCeti.Polylog

/-- After the substitution `t = exp (-u)`, the logarithmic radial integral of weight `k + 2` is
an integral over `(0, ∞)`. -/
private lemma integral_radialIntegrand_eq_integral_Ioi (k : ℕ) (z : ℂ) :
    (∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - t * z)) / t) =
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ k * (-Complex.log (1 - Real.exp (-u) * z)) := by
  rw [← TauCeti.integral_comp_exp_neg_Ioi]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
  have hu : (Real.exp (-u) : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.exp_pos _).ne'
  rw [Real.log_exp, neg_neg, Complex.real_smul]
  field_simp

/-- For `u > 0` and `‖z‖ ≤ 1`, the Taylor series of `-Log (1 - e^{-u} z)`, multiplied by
`u ^ k`, written with the real Laplace kernels `u ^ k e^{-(j + 1) u}`. -/
private lemma hasSum_pow_mul_neg_log (k : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) {u : ℝ} (hu : 0 < u) :
    HasSum (fun j : ℕ ↦ ((u ^ k * Real.exp (-((j + 1) * u)) : ℝ) : ℂ) * (z ^ (j + 1) / (j + 1)))
      ((u : ℂ) ^ k * (-Complex.log (1 - Real.exp (-u) * z))) := by
  have hw : ‖(Real.exp (-u) : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-u) * ‖z‖ ≤ Real.exp (-u) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact Real.exp_lt_one_iff.2 (neg_neg_iff_pos.2 hu)
  convert (Complex.hasSum_taylorSeries_neg_log' hw).mul_left ((u : ℂ) ^ k) using 2 with j
  have hexp : Real.exp (-((j + 1) * u)) = Real.exp (-u) ^ (j + 1) := by
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [hexp]
  push_cast
  ring

/-- On the closed unit disc the terms of the weight-`n` series are at most `1 / (k + 1) ^ n`. -/
private lemma norm_pow_succ_div_le {n : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1) (k : ℕ) :
    ‖z ^ (k + 1) / ((k : ℂ) + 1) ^ n‖ ≤ 1 / (((k + 1 : ℕ) : ℝ)) ^ n := by
  rw [norm_div, norm_pow, norm_pow, show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring,
    Complex.norm_natCast]
  gcongr
  exact pow_le_one₀ (norm_nonneg z) hz

/-- For `n ≥ 2` the dominating series `∑ 1 / (k + 1) ^ n` converges. -/
private lemma summable_one_div_succ_pow {n : ℕ} (hn : 2 ≤ n) :
    Summable fun k : ℕ ↦ 1 / (((k + 1 : ℕ) : ℝ)) ^ n :=
  (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega))

/-- For `n ≥ 2` the series of `Liₙ` converges absolutely on the closed unit disc. -/
theorem summable_norm_polylog_series_of_norm_le_one {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable fun k : ℕ ↦ ‖z ^ (k + 1) / ((k : ℂ) + 1) ^ n‖ :=
  (summable_one_div_succ_pow hn).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_pow_succ_div_le hz)

/-- **The polylogarithm on the closed unit disc.** For a natural weight `n ≥ 2` and `‖z‖ ≤ 1`,
`Liₙ(z) = ∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n`. On the boundary circle this is the value of the
defining radial integral, not a limit from inside the disc. -/
theorem hasSum_polylog_of_norm_le_one {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun k : ℕ ↦ z ^ (k + 1) / ((k : ℂ) + 1) ^ n) (polylog n z) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  set F : ℕ → ℝ → ℂ := fun j u ↦
    ((u ^ k * Real.exp (-((j + 1) * u)) : ℝ) : ℂ) * (z ^ (j + 1) / (j + 1)) with hF
  have hr (j : ℕ) : (0 : ℝ) < j + 1 := by positivity
  have hint (j : ℕ) : IntegrableOn (F j) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg_mul_Ioi k (hr j)).ofReal.mul_const _
  have hnorm (j : ℕ) : ∫ u in Ioi (0 : ℝ), ‖F j u‖ =
      k.factorial * ‖z ^ (j + 1) / ((j : ℂ) + 1) ^ (k + 2)‖ := by
    have hj : ‖(j : ℂ) + 1‖ = (j : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (j + 1)
    calc ∫ u in Ioi (0 : ℝ), ‖F j u‖
        = ∫ u in Ioi (0 : ℝ),
            u ^ k * Real.exp (-((j + 1) * u)) * (‖z‖ ^ (j + 1) / ((j : ℝ) + 1)) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) ↦ ?_
          simp only [hF, norm_mul, norm_div, norm_pow, Complex.norm_real, hj,
            Real.norm_of_nonneg (by positivity : 0 ≤ u ^ k * Real.exp (-((j + 1) * u)))]
      _ = _ := by
          rw [integral_mul_const, integral_pow_mul_exp_neg_mul_Ioi k (hr j), norm_div, norm_pow,
            norm_pow, hj]
          field_simp
          ring
  have hsum : Summable fun j ↦ ∫ u in Ioi (0 : ℝ), ‖F j u‖ := by
    simpa only [hnorm] using (summable_norm_polylog_series_of_norm_le_one hn hz).mul_left _
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  rw [setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) ↦
      (hasSum_pow_mul_neg_log k hz hu).tsum_eq, ← integral_radialIntegrand_eq_integral_Ioi] at h
  rw [polylog_nat_add_two]
  convert h.mul_left ((k.factorial : ℂ)⁻¹) using 1
  ext j
  rw [hF, integral_mul_const, integral_complex_ofReal, integral_pow_mul_exp_neg_mul_Ioi k (hr j)]
  have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  push_cast
  field_simp
  ring

/-- For `n ≥ 2` the series of `Liₙ` converges to `Liₙ` uniformly on the closed unit disc. -/
theorem hasSumUniformlyOn_polylog_closedBall {n : ℕ} (hn : 2 ≤ n) :
    HasSumUniformlyOn (fun k : ℕ ↦ fun z : ℂ ↦ z ^ (k + 1) / ((k : ℂ) + 1) ^ n) (polylog n)
      (Metric.closedBall 0 1) :=
  (HasSumUniformlyOn.of_norm_le_summable (summable_one_div_succ_pow hn) fun k _ hz ↦
    norm_pow_succ_div_le (mem_closedBall_zero_iff.1 hz) k).congr_right fun _ hz ↦
      (hasSum_polylog_of_norm_le_one hn (mem_closedBall_zero_iff.1 hz)).tsum_eq

/-- **The polylogarithm on the unit circle.** For `n ≥ 2` and real `a`, `Liₙ(e^{2πia})` is
Mathlib's exponential zeta function `expZeta a n = ∑_{k ≥ 1} e^{2πiak} / k ^ n`. -/
theorem polylog_exp_eq_expZeta {n : ℕ} (hn : 2 ≤ n) (a : ℝ) :
    polylog n (cexp (2 * π * I * a)) = HurwitzZeta.expZeta a n := by
  have hs : 1 < (n : ℂ).re := by simp only [natCast_re]; exact_mod_cast hn
  have h := (hasSum_nat_add_iff' 1).2 (HurwitzZeta.hasSum_expZeta_of_one_lt_re a hs)
  have hnorm : ‖cexp (2 * π * I * a)‖ = 1 := by
    rw [show 2 * π * I * a = ((2 * π * a : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  refine (hasSum_polylog_of_norm_le_one hn hnorm.le).unique ?_
  have hn0 : n ≠ 0 := by omega
  convert h using 1
  · ext k
    rw [cpow_natCast, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  · simp [hn0]

/-- **The zeta value.** For `n ≥ 2`, `Liₙ(1) = ζ(n)`. -/
theorem polylog_natCast_one_eq_riemannZeta {n : ℕ} (hn : 2 ≤ n) : polylog n 1 = riemannZeta n := by
  simpa [HurwitzZeta.expZeta_zero] using polylog_exp_eq_expZeta hn 0

/-- **The value at `-1`.** For `n ≥ 2`, `Liₙ(-1) = (2 ^ (1 - n) - 1) ζ(n)`, the alternating
zeta value `-∑_{k ≥ 1} (-1) ^ (k + 1) / k ^ n` expressed through `ζ(n)`. -/
theorem polylog_natCast_neg_one_eq_mul_riemannZeta {n : ℕ} (hn : 2 ≤ n) :
    polylog n (-1) = (2 / 2 ^ n - 1) * riemannZeta n := by
  have h1 := hasSum_polylog_of_norm_le_one hn (z := 1) (by simp)
  rw [polylog_natCast_one_eq_riemannZeta hn] at h1
  -- The terms of `Liₙ(1) + Liₙ(-1)` vanish at even `k`; at `k = 2 j + 1` they are
  -- `2 / (2 j + 2) ^ n`.
  have hodd : HasSum (fun j : ℕ ↦ (1 + (-1) ^ (2 * j + 1 + 1)) / (((2 * j + 1 : ℕ) : ℂ) + 1) ^ n)
      (2 / 2 ^ n * riemannZeta n) := by
    convert h1.mul_left (2 / 2 ^ n) using 2 with j
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul]
    push_cast
    rw [show (2 : ℂ) * j + 1 + 1 = 2 * (j + 1) by ring, mul_pow]
    field_simp
    norm_num
  have hsum := (Function.Injective.hasSum_iff (f := fun k : ℕ ↦
      (1 + (-1) ^ (k + 1)) / ((k : ℂ) + 1) ^ n) (g := fun j : ℕ ↦ 2 * j + 1)
      (fun a b hab ↦ by simpa using hab) fun k hk ↦ ?_).1 hodd
  · have h := h1.add (hasSum_polylog_of_norm_le_one hn (z := -1) (by simp))
    have h' : HasSum (fun k : ℕ ↦ 1 ^ (k + 1) / ((k : ℂ) + 1) ^ n +
        (-1) ^ (k + 1) / ((k : ℂ) + 1) ^ n) (2 / 2 ^ n * riemannZeta n) := by
      convert hsum using 2 with k
      rw [one_pow, add_div]
    linear_combination h.unique h'
  · obtain ⟨j, rfl⟩ : Even k := by
      rcases Nat.even_or_odd k with he | ⟨j, rfl⟩
      · exact he
      · exact absurd ⟨j, rfl⟩ hk
    simp [← two_mul, pow_succ, pow_mul]

/-- **Euler's value.** `Li₂(1) = π² / 6`. -/
theorem polylog_two_one : polylog 2 1 = (π : ℂ) ^ 2 / 6 := by
  simpa [riemannZeta_two] using polylog_natCast_one_eq_riemannZeta (n := 2) le_rfl

/-- **The dilogarithm at `-1`.** `Li₂(-1) = -π² / 12`. -/
theorem polylog_two_neg_one : polylog 2 (-1) = -((π : ℂ) ^ 2 / 12) := by
  have h := polylog_natCast_neg_one_eq_mul_riemannZeta (n := 2) le_rfl
  norm_num [riemannZeta_two] at h
  linear_combination h

end TauCeti.Polylog

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Bochner.Markov
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Pow.Summable
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Probability.Moments.GrowingOrder
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Upper spectral bounds from growing even moments

For a random matrix that is almost surely Hermitian with integrable real even trace, the measure
of the set where its operator norm is at least `r > 0` is at most the expected real trace of its
`2 * k`-th power divided by `r ^ (2 * k)`. This bounds the outer measure when the set is not
measurable.

At a norm threshold `r > s > 0`, where `s` is the exponential scale of the trace bound,
a sufficiently large multiple of `log (n + 1)` in the half-exponent `k n` of the even trace
power `2 * k n` offsets a polynomial prefactor in the sequence index `n`. If the matrices are
eventually almost surely Hermitian with integrable real even traces, and the trace bound holds
eventually, then the norm tails have a summable eventual majorant.
Full-series summability also requires finite tail measures at the initial indices where
Hermiticity and trace integrability are not assumed. The Borel–Cantelli step applies
without independence across indices. For the almost-sure bound below every threshold above a
level, each threshold may use its own positive scale below it.

For a positive-semidefinite matrix `S`, `‖S‖` is its largest eigenvalue and `‖S‖ ^ k ≤ tr (S ^ k)`
for every `k`, not only for even `k`. Hence for eventually almost surely positive-semidefinite
matrices, such as sample covariance matrices, a bound `E tr (S n ^ k n) ≤ C n ^ a r ^ k n` for
every `r > s`, with orders `k n` of any parity growing faster than `log n`, gives almost surely
`limsup ‖S n‖ ≤ s`. For sample covariance matrices, combined with a growing-moment bound
`E tr (S ^ k) ≤ C n ^ a ((1 + √y)² + ε) ^ k`, which is not proved here, this gives the upper half
of the limit `λ_max(XX*/n) → (1 + √y)²`.

## References

* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), §2.3.
* Z. Bai and J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  2nd ed., Springer (2010), Chapter 5.
* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), §2.2.
-/

public section

open Filter MeasureTheory
open scoped Topology ENNReal Matrix.Norms.L2Operator ComplexOrder

namespace TauCeti.Probability

open Matrix

variable {Ω 𝕜 ι : Type*} [MeasurableSpace Ω] [RCLike 𝕜] {P : Measure Ω}

/-- For a random matrix that is almost surely Hermitian with integrable real `2 * k`-th trace,
the measure of the set where its Euclidean operator norm is at least `r > 0` is at most the
expected real trace of its `2 * k`-th power divided by `r ^ (2 * k)`. The set need not be
measurable, in which case this bounds its outer measure. -/
theorem meas_l2_opNorm_ge_le_integral_re_trace_pow_two_mul_div_pow
    [Fintype ι] [DecidableEq ι] {A : Ω → Matrix ι ι 𝕜}
    (hA : ∀ᵐ ω ∂P, (A ω).IsHermitian) (k : ℕ)
    (hint : Integrable (fun ω ↦ RCLike.re ((A ω) ^ (2 * k)).trace) P) {r : ℝ} (hr : 0 < r) :
    P {ω | r ≤ ‖A ω‖} ≤ ENNReal.ofReal
      ((∫ ω, RCLike.re ((A ω) ^ (2 * k)).trace ∂P) / r ^ (2 * k)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hnorm (ω : Ω) : ‖A ω‖ = 0 := by
      rw [Subsingleton.elim (A ω) (0 : Matrix ι ι 𝕜), norm_zero]
    simp [hnorm, not_le_of_gt hr]
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ RCLike.re ((A ω) ^ (2 * k)).trace :=
    hA.mono fun ω hω ↦ (by positivity : 0 ≤ ‖A ω‖ ^ (2 * k)).trans
      (hω.l2_opNorm_pow_two_mul_le_re_trace_pow_two_mul k fun _ ↦ hι)
  have hsub : {ω | r ≤ ‖A ω‖} ≤ᵐ[P] {ω | r ^ (2 * k) ≤ RCLike.re ((A ω) ^ (2 * k)).trace} :=
    hA.mono fun _ hω h ↦ (pow_le_pow_left₀ hr.le h _).trans
      (hω.l2_opNorm_pow_two_mul_le_re_trace_pow_two_mul k fun _ ↦ hι)
  refine (measure_mono_ae hsub).trans ?_
  simpa only [pow_one] using meas_ge_le_integral_pow_div_pow
    (Y := fun ω ↦ RCLike.re ((A ω) ^ (2 * k)).trace) 1 (by simpa only [pow_one] using hint)
    (by simpa only [pow_one] using hnonneg) (pow_pos hr _)

variable {m : ℕ → Type*} [∀ n, Fintype (m n)] [∀ n, DecidableEq (m n)]
  {A : (n : ℕ) → Ω → Matrix (m n) (m n) 𝕜} {k : ℕ → ℕ}

/-- At a threshold `r > s > 0`, an eventual bound on the expected real trace of the
`2 * k n`-th powers, with exponential scale `s` and polynomial prefactor of degree `d`, gives a
summable eventual majorant for the norm tails. The matrices must eventually be almost surely
Hermitian with integrable real `2 * k n`-th traces. The trace exponent is `2 * k n`, and it
suffices that `k n ≥ B * log (n + 1)` eventually and `d + 1 < 2 * B * log (r / s)`. -/
theorem exists_tsum_lt_top_and_eventually_meas_l2_opNorm_ge_le_of_integral_re_trace_pow_two_mul_le
    (hA : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, (A n ω).IsHermitian)
    (hint : ∀ᶠ n in atTop, Integrable (fun ω ↦ RCLike.re ((A n ω) ^ (2 * k n)).trace) P)
    {s r : ℝ} (hs : 0 < s) (hr : s < r) {B C d : ℝ} (hB : d + 1 < 2 * B * Real.log (r / s))
    (hk : ∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ (k n : ℝ))
    (hbound : ∀ᶠ n : ℕ in atTop, (∫ ω, RCLike.re ((A n ω) ^ (2 * k n)).trace ∂P) ≤
      C * (n + 1 : ℝ) ^ d * s ^ (2 * k n)) :
    ∃ b : ℕ → ℝ≥0∞, (∑' n, b n) < ∞ ∧ ∀ᶠ n in atTop, P {ω | r ≤ ‖A n ω‖} ≤ b n := by
  have hr₀ := hs.trans hr
  let e := d + 2 * B * Real.log (s / r)
  have he : e < -1 := by
    dsimp only [e]
    rw [Real.log_div hs.ne' hr₀.ne']
    rw [Real.log_div hr₀.ne' hs.ne'] at hB
    linarith
  let b (n : ℕ) := |C| * (n + 1 : ℝ) ^ e
  refine ⟨fun n ↦ ENNReal.ofReal (b n), tsum_ofReal_mul_natCast_add_one_rpow_lt_top |C| he, ?_⟩
  filter_upwards [hA, hint, hbound, hk] with n hh hi hn hk'
  refine (meas_l2_opNorm_ge_le_integral_re_trace_pow_two_mul_div_pow hh _ hi hr₀).trans ?_
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ |C| * ((n + 1 : ℝ) ^ d * (s / r) ^ (2 * k n)) := by
      have habs : C * (n + 1 : ℝ) ^ d * s ^ (2 * k n) ≤
          |C| * (n + 1 : ℝ) ^ d * s ^ (2 * k n) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) (by positivity)
      refine (div_le_div_of_nonneg_right (hn.trans habs) (by positivity)).trans_eq ?_
      rw [div_pow]
      ring
    _ ≤ b n := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
      apply rpow_mul_pow_le_rpow_of_log_le (B := 2 * B)
        (le_add_of_nonneg_left (Nat.cast_nonneg _)) (div_pos hs hr₀) ((div_le_one hr₀).2 hr.le)
        _ le_rfl
      push_cast
      linarith

/-- An eventual even trace bound with polynomial prefactor `(n + 1)^d` in the sequence index
gives summable norm tails at `r > s` when `k n ≥ B * log (n + 1)` eventually and
`2 * B * log (r / s) > d + 1`. The prefix before the Hermiticity and integrability
hypotheses take effect must have finite tail measures. -/
theorem tsum_meas_l2_opNorm_ge_lt_top_of_integral_re_trace_pow_two_mul_le {N : ℕ}
    (hA : ∀ n ≥ N, ∀ᵐ ω ∂P, (A n ω).IsHermitian)
    (hint : ∀ n ≥ N, Integrable (fun ω ↦ RCLike.re ((A n ω) ^ (2 * k n)).trace) P)
    {s r : ℝ} (hs : 0 < s) (hr : s < r) {B C d : ℝ} (hB : d + 1 < 2 * B * Real.log (r / s))
    (hk : ∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ (k n : ℝ))
    (hbound : ∀ᶠ n : ℕ in atTop, (∫ ω, RCLike.re ((A n ω) ^ (2 * k n)).trace ∂P) ≤
      C * (n + 1 : ℝ) ^ d * s ^ (2 * k n))
    (hfinite : ∀ n < N, P {ω | r ≤ ‖A n ω‖} ≠ ∞) :
    (∑' n, P {ω | r ≤ ‖A n ω‖}) < ∞ := by
  obtain ⟨b, hb, h⟩ :=
    exists_tsum_lt_top_and_eventually_meas_l2_opNorm_ge_le_of_integral_re_trace_pow_two_mul_le
      (eventually_atTop.2 ⟨N, hA⟩) (eventually_atTop.2 ⟨N, hint⟩) hs hr hB hk hbound
  refine Filter.EventuallyLE.ennreal_tsum_lt_top (f := fun n ↦ P {ω | r ≤ ‖A n ω‖})
    (Nat.cofinite_eq_atTop ▸ h) (fun n ↦ ?_) hb
  rcases lt_or_ge n N with hn | hn
  · exact hfinite n hn
  · have hle := meas_l2_opNorm_ge_le_integral_re_trace_pow_two_mul_div_pow (hA n hn) _
      (hint n hn) (hs.trans hr)
    exact (hle.trans_lt ENNReal.ofReal_lt_top).ne

/-- Let the matrices be eventually almost surely Hermitian. If, for each threshold `r > s`, the
real even traces of some sufficiently large logarithmic order are eventually integrable and
eventually satisfy a trace estimate at some exponential scale `0 < t < r`, the norms are almost
surely eventually below every threshold `r > s`. The scale, moment orders and polynomial
prefactors may depend on the threshold. -/
theorem ae_eventually_l2_opNorm_lt_of_integral_re_trace_pow_two_mul_le
    (hA : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, (A n ω).IsHermitian) {s : ℝ}
    (htrace : ∀ r > s, ∃ (t B C d : ℝ) (k : ℕ → ℕ), 0 < t ∧ t < r ∧
      d + 1 < 2 * B * Real.log (r / t) ∧
      (∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ (k n : ℝ)) ∧
      (∀ᶠ n in atTop, Integrable (fun ω ↦ RCLike.re ((A n ω) ^ (2 * k n)).trace) P) ∧
      (∀ᶠ n : ℕ in atTop, (∫ ω, RCLike.re ((A n ω) ^ (2 * k n)).trace ∂P) ≤
        C * (n + 1 : ℝ) ^ d * t ^ (2 * k n))) :
    ∀ᵐ ω ∂P, ∀ r > s, ∀ᶠ n in atTop, ‖A n ω‖ < r := by
  refine TauCeti.MeasureTheory.ae_forall_eventually_lt_of_eventually_measure_le fun r hr ↦ ?_
  obtain ⟨t, B, C, d, k, ht, htr, hB, hk, hi, hb⟩ := htrace r hr
  exact exists_tsum_lt_top_and_eventually_meas_l2_opNorm_ge_le_of_integral_re_trace_pow_two_mul_le
    hA hi ht htr hB hk hb

/-- **Trace method for positive-semidefinite random matrices.** Let the matrices be eventually
almost surely positive semidefinite, with eventually integrable real traces
of their `k n`-th powers, where the orders `k n` have any parity and grow faster than `log n`. If
for every `r > s ≥ 0` there are constants `C` and `a` with `E tr (A n ^ k n) ≤ C n ^ a r ^ k n`
for all large `n`, then almost surely the norms, that is the largest eigenvalues
(`Matrix.PosSemidef.l2_opNorm_eq_eigenvalues₀_zero`), are eventually below every `r > s`. -/
theorem ae_eventually_l2_opNorm_lt_of_integral_re_trace_pow_le
    (hA : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, (A n ω).PosSemidef)
    (hk : Tendsto (fun n ↦ (k n : ℝ) / Real.log n) atTop atTop)
    (hint : ∀ᶠ n in atTop, Integrable (fun ω ↦ RCLike.re (A n ω ^ k n).trace) P) {s : ℝ}
    (hs : 0 ≤ s) (hmom : ∀ r > s, ∃ C : ℝ, ∃ a : ℕ, ∀ᶠ n : ℕ in atTop,
      ∫ ω, RCLike.re (A n ω ^ k n).trace ∂P ≤ C * n ^ a * r ^ k n) :
    ∀ᵐ ω ∂P, ∀ r > s, ∀ᶠ n in atTop, ‖A n ω‖ < r := by
  -- Orders growing faster than `log n` are eventually nonzero.
  have hk₀ : ∀ᶠ n in atTop, k n ≠ 0 :=
    (hk.eventually_gt_atTop 0).mono fun n hn hkn ↦ by simp [hkn] at hn
  exact ae_forall_eventually_lt_of_integral_le_mul_pow hs
    ((hA.and hk₀).mono fun n hn ↦ hn.1.mono fun ω hω ↦ by
      rw [abs_norm]
      exact hω.l2_opNorm_pow_le_re_trace_pow (k n) fun h ↦ absurd h hn.2)
    hint hk hmom

end TauCeti.Probability

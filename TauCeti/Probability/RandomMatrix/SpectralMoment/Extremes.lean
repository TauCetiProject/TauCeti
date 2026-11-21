/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Upper spectral bounds from growing even moments

At a norm threshold `r > s > 0`, where `s` is the exponential scale of the trace bound,
a sufficiently large multiple of `log (n + 1)` in the moment order offsets a polynomial
prefactor in the sequence index `n`. The norm tails have a summable eventual majorant.
Full-series summability also requires finite tail measures at the initial indices where
Hermiticity and trace integrability are not assumed. The Borel–Cantelli step applies
without independence across indices.

## References

* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), §2.3.
-/

public section

open Filter MeasureTheory
open scoped Topology ENNReal Matrix.Norms.L2Operator

namespace TauCeti.Probability

open Matrix

variable {Ω 𝕜 ι : Type*} [MeasurableSpace Ω] [RCLike 𝕜] {P : Measure Ω}

/-- For a random Hermitian matrix, Markov's inequality with the even trace power
controls the upper tail of its Euclidean operator norm. -/
theorem meas_l2_opNorm_ge_le_integral_re_trace_pow_two_mul
    [Fintype ι] [DecidableEq ι] {A : Ω → Matrix ι ι 𝕜}
    (hA : ∀ᵐ ω ∂P, (A ω).IsHermitian) (k : ℕ)
    (hint : Integrable (fun ω ↦ RCLike.re ((A ω) ^ (2 * k)).trace) P) {r : ℝ} (hr : 0 < r) :
    P {ω | r ≤ ‖A ω‖} ≤ ENNReal.ofReal
      ((∫ ω, RCLike.re ((A ω) ^ (2 * k)).trace ∂P) / r ^ (2 * k)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hnorm (ω : Ω) : ‖A ω‖ = 0 := by
      rw [Subsingleton.elim (A ω) (0 : Matrix ι ι 𝕜), norm_zero]
    simp [hnorm, not_le_of_gt hr]
  have hnonneg : 0 ≤ᵐ[P] fun ω ↦ RCLike.re ((A ω) ^ (2 * k)).trace :=
    hA.mono fun ω hω ↦ (by positivity : 0 ≤ ‖A ω‖ ^ (2 * k)).trans
      (hω.l2_opNorm_pow_two_mul_le_re_trace_pow_two_mul k)
  have hsub : {ω | r ≤ ‖A ω‖} ≤ᵐ[P] {ω | r ^ (2 * k) ≤ RCLike.re ((A ω) ^ (2 * k)).trace} :=
    hA.mono fun _ hω h ↦
      (pow_le_pow_left₀ hr.le h _).trans (hω.l2_opNorm_pow_two_mul_le_re_trace_pow_two_mul k)
  exact (measure_mono_ae hsub).trans (hint.measure_ge_le_ofReal_integral_div hnonneg (pow_pos hr _))

variable {m : ℕ → Type*} [∀ n, Fintype (m n)] [∀ n, DecidableEq (m n)]
  {A : (n : ℕ) → Ω → Matrix (m n) (m n) 𝕜} {k : ℕ → ℕ}

/-- At a threshold `r > s > 0`, an eventual even trace bound with exponential scale `s`
and polynomial prefactor of degree `d` gives a summable eventual majorant for the norm tails.
It suffices that the moment order is eventually at least `B * log (n + 1)` and
`d + 1 < 2 * B * log (r / s)`. -/
theorem exists_tsum_lt_top_meas_l2_opNorm_ge_le_of_integral_re_trace_pow_two_mul_le
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
  have hsum := ((Real.summable_nat_rpow (p := e)).2 he)
  have hsum' : Summable b := by
    simpa only [b, Nat.cast_add, Nat.cast_one] using ((summable_nat_add_iff 1).2 hsum).mul_left |C|
  refine ⟨fun n ↦ ENNReal.ofReal (b n), hsum'.tsum_ofReal_lt_top, ?_⟩
  filter_upwards [hA, hint, hbound, hk] with n hh hi hn hk'
  refine (meas_l2_opNorm_ge_le_integral_re_trace_pow_two_mul hh _ hi hr₀).trans ?_
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
    exists_tsum_lt_top_meas_l2_opNorm_ge_le_of_integral_re_trace_pow_two_mul_le
      (eventually_atTop.2 ⟨N, hA⟩) (eventually_atTop.2 ⟨N, hint⟩) hs hr hB hk hbound
  refine Filter.EventuallyLE.ennreal_tsum_lt_top (f := fun n ↦ P {ω | r ≤ ‖A n ω‖}) h
    (fun n ↦ ?_) hb
  rcases lt_or_ge n N with hn | hn
  · exact hfinite n hn
  · have hle :=
      meas_l2_opNorm_ge_le_integral_re_trace_pow_two_mul (hA n hn) _ (hint n hn) (hs.trans hr)
    exact (hle.trans_lt ENNReal.ofReal_lt_top).ne

/-- For each threshold `r > s > 0`, a trace estimate of sufficiently large logarithmic order
at exponential scale `s ≤ t < r` gives an almost-sure eventual upper norm bound.
The scale, moment orders and polynomial prefactors may depend on the threshold. -/
theorem ae_eventually_l2_opNorm_lt_of_integral_re_trace_pow_two_mul_le
    (hA : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, (A n ω).IsHermitian)
    {s : ℝ} (hs : 0 < s)
    (htrace : ∀ r > s, ∃ (t B C d : ℝ) (k : ℕ → ℕ), s ≤ t ∧ t < r ∧
      d + 1 < 2 * B * Real.log (r / t) ∧
      (∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ (k n : ℝ)) ∧
      (∀ᶠ n in atTop, Integrable (fun ω ↦ RCLike.re ((A n ω) ^ (2 * k n)).trace) P) ∧
      (∀ᶠ n : ℕ in atTop, (∫ ω, RCLike.re ((A n ω) ^ (2 * k n)).trace ∂P) ≤
        C * (n + 1 : ℝ) ^ d * t ^ (2 * k n))) :
    ∀ᵐ ω ∂P, ∀ r > s, ∀ᶠ n in atTop, ‖A n ω‖ < r := by
  have h (j : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ‖A n ω‖ < s + 1 / (j + 1) := by
    have hr : s < s + 1 / (j + 1) := lt_add_of_pos_right _ (by positivity)
    obtain ⟨t, B, C, d, k, hst, htr, hB, hk, hi, hb⟩ := htrace _ hr
    obtain ⟨b, hsum, h⟩ :=
      exists_tsum_lt_top_meas_l2_opNorm_ge_le_of_integral_re_trace_pow_two_mul_le
        hA hi (hs.trans_le hst) htr hB hk hb
    simpa only [Set.mem_ofPred_eq, not_le] using
      TauCeti.MeasureTheory.ae_eventually_notMem_of_eventually_measure_le hsum h
  filter_upwards [ae_all_iff.2 h] with ω hω
  intro r hr
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 hr)
  exact (hω j).mono fun _ hn ↦ hn.trans (by linarith)

end TauCeti.Probability

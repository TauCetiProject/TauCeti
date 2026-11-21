/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.TraceBound
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.PSeries
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Upper spectral bounds from growing even moments

A polynomial prefactor in an expected trace bound can be absorbed into the Markov
bound if the degree grows faster than the logarithm of the size. The resulting norm
tails are summable. The Borel–Cantelli step requires no independence across sizes.

## References

* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), §2.3.
-/

public section

open Filter MeasureTheory
open scoped Topology ENNReal Matrix.Norms.L2Operator

namespace Matrix

variable {Ω 𝕜 ι : Type*} [MeasurableSpace Ω] [RCLike 𝕜] {P : Measure Ω}

/-- For a random Hermitian matrix, Markov's inequality with the even trace power
controls the upper tail of its Euclidean operator norm. -/
theorem measure_le_l2_opNorm_le_integral_re_trace_pow
    [Fintype ι] [DecidableEq ι] [Nonempty ι] {A : Ω → Matrix ι ι 𝕜}
    (hA : ∀ ω, (A ω).IsHermitian) (k : ℕ)
    (hint : Integrable (fun ω ↦ RCLike.re ((A ω) ^ (2 * k)).trace) P) {r : ℝ} (hr : 0 < r) :
    P {ω | r ≤ ‖A ω‖} ≤ ENNReal.ofReal
      ((∫ ω, RCLike.re ((A ω) ^ (2 * k)).trace ∂P) / r ^ (2 * k)) := by
  have hnonneg (ω : Ω) : 0 ≤ RCLike.re ((A ω) ^ (2 * k)).trace :=
    (by positivity : 0 ≤ ‖A ω‖ ^ (2 * k)).trans ((hA ω).l2_opNorm_pow_le_re_trace_pow k)
  have hr' : 0 < r ^ (2 * k) := pow_pos hr _
  have hsub : {ω | r ≤ ‖A ω‖} ⊆
      {ω | ENNReal.ofReal (r ^ (2 * k)) ≤ ENNReal.ofReal (RCLike.re ((A ω) ^ (2 * k)).trace)} :=
    fun ω h ↦ ENNReal.ofReal_le_ofReal
      ((pow_le_pow_left₀ hr.le h _).trans ((hA ω).l2_opNorm_pow_le_re_trace_pow k))
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div hint.aemeasurable.ennreal_ofReal
    (ENNReal.ofReal_pos.2 hr').ne' ENNReal.ofReal_ne_top).trans_eq ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hint (.of_forall hnonneg),
    ENNReal.ofReal_div_of_pos hr']

private theorem eventually_rpow_mul_pow_le_rpow_neg_two {k : ℕ → ℕ}
    (hk : ∀ B > (0 : ℝ), ∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ (k n : ℝ))
    {q : ℝ} (hq : 0 < q) (hq' : q < 1) (d : ℝ) :
    ∀ᶠ n : ℕ in atTop, (n + 1 : ℝ) ^ d * q ^ (2 * k n) ≤ (n + 1 : ℝ) ^ (-2 : ℝ) := by
  have hlq := Real.log_neg hq hq'
  let B := (|d| + 2) / (-2 * Real.log q)
  have hD : 0 < |d| + 2 := by positivity
  have hL : 0 < -2 * Real.log q := by linarith
  have hB : 0 < B := div_pos hD hL
  filter_upwards [hk B hB] with n hn
  have hn₀ : 0 < (n + 1 : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (n + 1 : ℝ) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have he := mul_le_mul_of_nonneg_right hn hL.le
  have hBL : B * (-2 * Real.log q) = |d| + 2 := div_mul_cancel₀ _ hL.ne'
  rw [mul_right_comm, hBL] at he
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hn₀, Real.rpow_def_of_pos hq,
    ← Real.exp_add, Real.rpow_def_of_pos hn₀, Real.exp_le_exp]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right (le_abs_self d) hlog]

variable {m : ℕ → Type*} [∀ n, Fintype (m n)] [∀ n, DecidableEq (m n)] [∀ n, Nonempty (m n)]
  {A : (n : ℕ) → Ω → Matrix (m n) (m n) 𝕜} {k : ℕ → ℕ}

private theorem eventually_measure_le_l2_opNorm_le_rpow_neg_two
    (hA : ∀ n ω, (A n ω).IsHermitian)
    (hk : ∀ B > (0 : ℝ), ∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ (k n : ℝ))
    (hint : ∀ᶠ n in atTop, Integrable (fun ω ↦ RCLike.re ((A n ω) ^ (2 * k n)).trace) P)
    {s : ℝ} (hs : 0 < s) {C d : ℝ}
    (hbound : ∀ᶠ n : ℕ in atTop, (∫ ω, RCLike.re ((A n ω) ^ (2 * k n)).trace ∂P) ≤
      C * (n + 1 : ℝ) ^ d * s ^ (2 * k n)) {r : ℝ} (hr : s < r) :
    ∀ᶠ n : ℕ in atTop, P {ω | r ≤ ‖A n ω‖} ≤ ENNReal.ofReal (|C| * (n + 1 : ℝ) ^ (-2 : ℝ)) := by
  have hr₀ := hs.trans hr
  have hsmall := eventually_rpow_mul_pow_le_rpow_neg_two hk (div_pos hs hr₀)
    ((div_lt_one hr₀).2 hr) d
  filter_upwards [hint, hbound, hsmall] with n hi hn he
  refine (measure_le_l2_opNorm_le_integral_re_trace_pow (hA n) _ hi hr₀).trans ?_
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
    _ ≤ _ := mul_le_mul_of_nonneg_left he (abs_nonneg C)

/-- If an even trace bound grows as a polynomial in the size times `s^(2*k n)`, and
`k n` eventually dominates each constant multiple of `log (n+1)`, the upper norm tail
at every fixed threshold `r > s` is summable. -/
theorem tsum_measure_le_l2_opNorm_lt_top_of_integral_re_trace_pow_le [IsFiniteMeasure P]
    (hA : ∀ n ω, (A n ω).IsHermitian)
    (hk : ∀ B > (0 : ℝ), ∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ (k n : ℝ))
    (hint : ∀ᶠ n in atTop, Integrable (fun ω ↦ RCLike.re ((A n ω) ^ (2 * k n)).trace) P)
    {s : ℝ} (hs : 0 < s) {C d : ℝ}
    (hbound : ∀ᶠ n : ℕ in atTop, (∫ ω, RCLike.re ((A n ω) ^ (2 * k n)).trace ∂P) ≤
      C * (n + 1 : ℝ) ^ d * s ^ (2 * k n)) {r : ℝ} (hr : s < r) :
    (∑' n, P {ω | r ≤ ‖A n ω‖}) < ∞ := by
  let f (n : ℕ) := P {ω | r ≤ ‖A n ω‖}
  let b (n : ℕ) := |C| * (n + 1 : ℝ) ^ (-2 : ℝ)
  have hsum₀ : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ)) :=
    (Real.summable_nat_rpow (p := -2)).2 (by norm_num)
  have hsum' : Summable (fun n : ℕ ↦ (n + 1 : ℝ) ^ (-2 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hsum₀
  have hsum : Summable b := hsum'.mul_left |C|
  have hf (n : ℕ) : f n ≠ ∞ := measure_ne_top P _
  have htail : ∀ᶠ n in atTop, f n ≤ ENNReal.ofReal (b n) :=
    eventually_measure_le_l2_opNorm_le_rpow_neg_two hA hk hint hs hbound hr
  exact ENNReal.tsum_lt_top_of_eventually_le_ofReal hf
    (fun n ↦ by dsimp only [b]; positivity) hsum htail

/-- The same growing trace estimate gives an almost-sure asymptotic upper norm bound.
There is no coupling restriction between the matrices at different sizes. -/
theorem ae_eventually_l2_opNorm_lt_of_integral_re_trace_pow_le [IsFiniteMeasure P]
    (hA : ∀ n ω, (A n ω).IsHermitian)
    (hk : ∀ B > (0 : ℝ), ∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ (k n : ℝ))
    (hint : ∀ᶠ n in atTop, Integrable (fun ω ↦ RCLike.re ((A n ω) ^ (2 * k n)).trace) P)
    {s : ℝ} (hs : 0 < s) {C d : ℝ}
    (hbound : ∀ᶠ n : ℕ in atTop, (∫ ω, RCLike.re ((A n ω) ^ (2 * k n)).trace ∂P) ≤
      C * (n + 1 : ℝ) ^ d * s ^ (2 * k n)) :
    ∀ᵐ ω ∂P, ∀ r > s, ∀ᶠ n in atTop, ‖A n ω‖ < r := by
  have h (j : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ‖A n ω‖ < s + 1 / (j + 1) := by
    have hsum := tsum_measure_le_l2_opNorm_lt_top_of_integral_re_trace_pow_le hA hk hint hs hbound
      (r := s + 1 / (j + 1)) (lt_add_of_pos_right _ (by positivity))
    simpa only [Set.mem_ofPred_eq, not_le] using ae_eventually_notMem hsum.ne
  filter_upwards [ae_all_iff.2 h] with ω hω
  intro r hr
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 hr)
  exact (hω j).mono fun _ hn ↦ hn.trans (by linarith)

end Matrix

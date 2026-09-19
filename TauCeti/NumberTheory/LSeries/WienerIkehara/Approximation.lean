/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import TauCeti.NumberTheory.LSeries.WienerIkehara.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SumIntegralComparisons
import TauCeti.Algebra.Order.BigOperators.Sum.ByParts
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Asymptotics.SumWindow

/-!
# Approximating the test function in the smoothed Wiener--Ikehara asymptotic

`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg` evaluates the limit of
`∑ a n / n * 𝓕 psi (log (n / x) / 2π)` for a *smooth compactly supported* test function `psi`.
The Tauberian step of Wiener--Ikehara needs the same limit for weights `W` that are not of this
form. A nonzero smooth compactly supported weight `W` is one: it is the Fourier transform of a
Schwartz function, but never of a compactly supported one, since a nonzero function and its
Fourier transform cannot both have compact support. This file passes the limit from `𝓕 psi` to
any weight `W` that such transforms approximate in the weighted sup norm
`sup_v (1 + v ^ 2) ‖W v - 𝓕 psi v‖`.

The approximation step rests on a uniform bound. If the partial sums of `‖a‖` satisfy the
Chebyshev bound `∑_{1 ≤ n ≤ N} ‖a n‖ ≤ C N`, then
`∑ ‖a n‖ / n * (1 + (log (n / x) / 2π) ^ 2)⁻¹ ≤ C (1 + 2π²)` for every scale `x > 0`.
The weight `t ↦ (t (1 + (log (t / x) / 2π) ^ 2))⁻¹` is antitone on `t > 0`, so Abel's inequality
`TauCeti.sum_range_mul_le_sum_range_mul` bounds the weighted sum by `C` times the sum of the
weight, and the integral test bounds the latter by `1 + ∫ = 1 + 2π (arctan - arctan) ≤ 1 + 2π²`.
Consequently a weight `W` with `‖W v‖ ≤ M (1 + v ^ 2)⁻¹` gives a series of size at most
`M C (1 + 2π²)`, uniformly in `x`, and a small error in the weighted sup norm costs little in the
limit. For nonnegative coefficients with Wiener--Ikehara boundary data the Chebyshev bound is
`TauCeti.LSeries.isBigO_sum_Icc_norm_id_of_boundary`.

## Main results

* `TauCeti.LSeries.tsum_norm_term_mul_inv_one_add_sq_le`: the uniform bound on the
  logarithmically weighted series, from a Chebyshev bound.
* `TauCeti.LSeries.LSeriesSummable_mul_comp_log_div` and
  `TauCeti.LSeries.norm_tsum_term_mul_comp_log_div_le`: summability and the uniform bound for a
  weight `W` with `‖W v‖ ≤ M (1 + v ^ 2)⁻¹`.
* `TauCeti.LSeries.tendsto_tsum_term_mul_atTop_of_approx_fourier`: the smoothed Wiener--Ikehara
  asymptotic for a weight `W` approximable by Fourier transforms of smooth compactly supported
  functions `psi` whose values `psi 0` approximate `L`; the limit is `2π A L`.

## Provenance

The uniform bound and the truncation argument follow `bound_sum_log`, `bound_I1` and
`limiting_cor_W21` in `PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0
`AxiomMath/PrimeNumberTheoremAnd` repository, revision
`2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, the same source as the sibling files in this
directory. Here the summation by parts is the general `TauCeti.sum_range_mul_le_sum_range_mul`,
the integral of the weight is bounded on finite intervals by the fundamental theorem of calculus
rather than evaluated on `(0, ∞)`, and the approximation hypothesis is stated for an arbitrary
weight `W` instead of a fixed truncation of a `W^{2,1}` function. For a Schwartz function `g`
(`limiting_cor_schwartz` there) the approximants are the truncations `χ (R⁻¹ • ·) • g`, which
converge to `g` in the Schwartz topology (`SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop`);
the weighted sup norm of a Fourier transform is bounded by two Schwartz seminorms, so it is the
continuity of the Fourier transform on `𝓢(ℝ, ℂ)` that makes the truncation error small.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
-/

public section

namespace TauCeti.LSeries

open Complex Filter FourierTransform Real Set
open scoped ComplexOrder ContDiff SchwartzMap Topology

variable {a : ℕ → ℂ} {C x : ℝ}

/-! ### The logarithmic weight -/

/-- The weight `(t (1 + (log (t / x) / 2π) ^ 2))⁻¹` against which the coefficients are summed. -/
private noncomputable def logWeight (x t : ℝ) : ℝ :=
  (t * (1 + (1 / (2 * π) * Real.log (t / x)) ^ 2))⁻¹

private lemma one_div_two_pi_pos : (0 : ℝ) < 1 / (2 * π) := by positivity

private lemma one_div_two_pi_le_one : 1 / (2 * π) ≤ 1 := by
  rw [div_le_one (by positivity)]
  linarith [Real.two_le_pi]

private lemma hasDerivAt_log_div (hx : 0 < x) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t ↦ Real.log (t / x)) t⁻¹ t := by
  convert ((hasDerivAt_id' t).div_const x).log (div_pos ht hx).ne' using 1
  field_simp

/-- `t (1 + (log (t / x) / 2π) ^ 2)` has derivative `1 + b² L² + 2 b² L` at `t > 0`, where
`b = 1 / 2π` and `L = log (t / x)`. -/
private lemma hasDerivAt_logWeight_denom (hx : 0 < x) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t ↦ t * (1 + (1 / (2 * π) * Real.log (t / x)) ^ 2))
      (1 + (1 / (2 * π) * Real.log (t / x)) ^ 2 +
        2 * (1 / (2 * π)) ^ 2 * Real.log (t / x)) t := by
  refine ((hasDerivAt_id' t).mul
    ((((hasDerivAt_log_div hx ht).const_mul (1 / (2 * π))).pow 2).const_add 1)).congr_deriv ?_
  have := Real.pi_pos.ne'
  simp only [Pi.pow_apply, Nat.cast_ofNat]
  set L := Real.log (t / x)
  field_simp
  have h : π * L * π⁻¹ = L := by field_simp
  linear_combination 2 * h

private lemma logWeight_denom_pos (hx : 0 < x) {t : ℝ} (ht : 0 < t) :
    0 < t * (1 + (1 / (2 * π) * Real.log (t / x)) ^ 2) := by
  have := hx
  positivity

/-- The logarithmic weight is antitone on `t > 0`: the derivative `1 + b² L² + 2 b² L` of its
reciprocal equals `b² (L + 1) ^ 2 + (1 - b²)`, which is nonnegative because `b = 1 / 2π ≤ 1`. -/
private lemma antitoneOn_logWeight (hx : 0 < x) : AntitoneOn (logWeight x) (Ioi 0) := by
  have hmono : MonotoneOn (fun t ↦ t * (1 + (1 / (2 * π) * Real.log (t / x)) ^ 2)) (Ioi 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
      (fun t ht ↦ (hasDerivAt_logWeight_denom hx ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hasDerivAt_logWeight_denom hx
        (by simpa only [interior_Ioi, mem_Ioi] using ht)).hasDerivWithinAt) fun t _ ↦ ?_
    have hb0 := one_div_two_pi_pos
    have hb1 := one_div_two_pi_le_one
    nlinarith [sq_nonneg (Real.log (t / x) + 1), mul_le_mul hb1 hb1 hb0.le zero_le_one]
  intro s hs t ht hst
  exact inv_anti₀ (logWeight_denom_pos hx hs) (hmono hs ht hst)

private lemma logWeight_nonneg (hx : 0 < x) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ logWeight x t := by
  have := hx
  unfold logWeight
  positivity

/-- On a finite interval `[1, T]` the integral of the logarithmic weight is at most `2π²`: its
antiderivative `2π arctan (log (t / x) / 2π)` varies by less than `2π · π`. -/
private lemma integral_logWeight_le (hx : 0 < x) {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in (1 : ℝ)..T, logWeight x t ≤ 2 * π ^ 2 := by
  have hderiv : ∀ t ∈ uIcc (1 : ℝ) T, HasDerivAt
      (fun t ↦ 2 * π * Real.arctan (1 / (2 * π) * Real.log (t / x))) (logWeight x t) t := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    refine ((((hasDerivAt_log_div hx ht0).const_mul (1 / (2 * π))).arctan).const_mul
      (2 * π)).congr_deriv ?_
    simp only [logWeight]
    field_simp
  have hint : IntervalIntegrable (logWeight x) MeasureTheory.volume 1 T :=
    ((antitoneOn_logWeight hx).mono fun t ht ↦ by
      rw [uIcc_of_le hT] at ht
      exact lt_of_lt_of_le one_pos ht.1).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, ← mul_sub]
  have h1 := Real.arctan_lt_pi_div_two (1 / (2 * π) * Real.log (T / x))
  have h2 := Real.neg_pi_div_two_lt_arctan (1 / (2 * π) * Real.log (1 / x))
  nlinarith [Real.pi_pos]

/-- The weight summed over `1 ≤ n ≤ N` is at most `1 + 2π²`, uniformly in `N` and `x > 0`. -/
private lemma sum_range_logWeight_le (hx : 0 < x) (N : ℕ) :
    ∑ i ∈ Finset.range N, logWeight x (i + 1 : ℕ) ≤ 1 + 2 * π ^ 2 := by
  rcases N with _ | M
  · simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  rw [Finset.sum_range_succ']
  have hfirst : logWeight x ((0 + 1 : ℕ) : ℝ) ≤ 1 := by
    simp only [logWeight, zero_add, Nat.cast_one, one_mul]
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg _))
  have hanti : AntitoneOn (logWeight x) (Icc 1 (1 + (M : ℝ))) :=
    (antitoneOn_logWeight hx).mono fun t ht ↦ lt_of_lt_of_le one_pos ht.1
  have hsum := hanti.sum_le_integral
  have hint := integral_logWeight_le hx (T := 1 + M) (by linarith [M.cast_nonneg (α := ℝ)])
  have hrw : ∀ i ∈ Finset.range M, logWeight x ((i + 1 + 1 : ℕ) : ℝ) =
      logWeight x (1 + ((i + 1 : ℕ) : ℝ)) := fun i _ ↦ by
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hrw]
  linarith

/-! ### The uniform bound -/

/-- The logarithmically weighted norm series, written against the weight. -/
private lemma norm_term_mul_inv_one_add_sq_eq (n : ℕ) :
    ‖_root_.LSeries.term a 1 n‖ * (1 + (1 / (2 * π) * Real.log (n / x)) ^ 2)⁻¹ =
      ‖a n‖ * logWeight x n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [logWeight]
  simp only [_root_.LSeries.norm_term_eq, hn, ↓reduceIte, Complex.one_re, Real.rpow_one,
    logWeight, mul_inv, div_eq_mul_inv, mul_assoc]

private lemma norm_term_mul_inv_one_add_sq_nonneg (n : ℕ) :
    0 ≤ ‖_root_.LSeries.term a 1 n‖ * (1 + (1 / (2 * π) * Real.log (n / x)) ^ 2)⁻¹ := by
  positivity

/-- The partial sums of the logarithmically weighted norm series are at most `C (1 + 2π²)`. -/
private lemma sum_range_norm_term_mul_inv_one_add_sq_le
    (hC : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ C * N) (hx : 0 < x) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        ‖_root_.LSeries.term a 1 n‖ * (1 + (1 / (2 * π) * Real.log (n / x)) ^ 2)⁻¹ ≤
      C * (1 + 2 * π ^ 2) := by
  have hC0 : 0 ≤ C := by
    have h := hC 1
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, mul_one] at h
    exact (norm_nonneg _).trans h
  -- Enlarge the range by one and drop the vanishing `n = 0` term.
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 N.le_succ)
    fun n _ _ ↦ norm_term_mul_inv_one_add_sq_nonneg n) ?_
  rw [Finset.sum_range_succ']
  simp only [norm_term_mul_inv_one_add_sq_eq]
  have hlogWeight_zero : logWeight x ((0 : ℕ) : ℝ) = 0 := by simp [logWeight]
  rw [hlogWeight_zero, mul_zero, add_zero]
  -- Abel's inequality against the constant sequence `C`.
  have hpartial : ∀ k ≤ N, ∑ i ∈ Finset.range k, ‖a (i + 1)‖ ≤
      ∑ _i ∈ Finset.range k, C := fun k _ ↦ by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
    convert hC k using 1
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun n ↦ ‖a n‖) 0 k 1]
    rfl
  have habel := sum_range_mul_le_sum_range_mul (w := fun i ↦ logWeight x (i + 1 : ℕ)) hpartial
    (fun i _ ↦ antitoneOn_logWeight hx (by simp only [mem_Ioi]; positivity)
      (by simp only [mem_Ioi]; positivity) (by push_cast; linarith))
    (logWeight_nonneg hx (Nat.cast_nonneg _))
  calc ∑ i ∈ Finset.range N, ‖a (i + 1)‖ * logWeight x (i + 1 : ℕ)
      = ∑ i ∈ Finset.range N, logWeight x (i + 1 : ℕ) * ‖a (i + 1)‖ :=
        Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
    _ ≤ ∑ i ∈ Finset.range N, logWeight x (i + 1 : ℕ) * C := habel
    _ = C * ∑ i ∈ Finset.range N, logWeight x (i + 1 : ℕ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
    _ ≤ C * (1 + 2 * π ^ 2) := mul_le_mul_of_nonneg_left (sum_range_logWeight_le hx N) hC0

/-- Under a Chebyshev bound the logarithmically weighted norm series converges at every scale
`x > 0`. -/
theorem summable_norm_term_mul_inv_one_add_sq
    (hC : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ C * N) (hx : 0 < x) :
    Summable fun n : ℕ ↦
      ‖_root_.LSeries.term a 1 n‖ * (1 + (1 / (2 * π) * Real.log (n / x)) ^ 2)⁻¹ :=
  summable_of_sum_range_le (fun _ ↦ norm_term_mul_inv_one_add_sq_nonneg _)
    (sum_range_norm_term_mul_inv_one_add_sq_le hC hx)

/-- **The uniform logarithmic bound.** If `∑_{1 ≤ n ≤ N} ‖a n‖ ≤ C N` for every `N`, then
`∑ ‖a n‖ / n * (1 + (log (n / x) / 2π) ^ 2)⁻¹ ≤ C (1 + 2π²)` for every scale `x > 0`. -/
theorem tsum_norm_term_mul_inv_one_add_sq_le
    (hC : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ C * N) (hx : 0 < x) :
    ∑' n : ℕ, ‖_root_.LSeries.term a 1 n‖ * (1 + (1 / (2 * π) * Real.log (n / x)) ^ 2)⁻¹ ≤
      C * (1 + 2 * π ^ 2) :=
  Real.tsum_le_of_sum_range_le (fun _ ↦ norm_term_mul_inv_one_add_sq_nonneg _)
    (sum_range_norm_term_mul_inv_one_add_sq_le hC hx)

/-! ### Weights with quadratic decay -/

variable {W : ℝ → ℂ} {M : ℝ}

private lemma term_mul_comp_log_div :
    _root_.LSeries.term (fun n ↦ a n * W (1 / (2 * π) * Real.log (n / x))) 1 =
      fun n ↦ _root_.LSeries.term a 1 n * W (1 / (2 * π) * Real.log (n / x)) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [_root_.LSeries.term_of_ne_zero hn, _root_.LSeries.term_of_ne_zero hn]
  ring

private lemma norm_term_mul_le (hW : ∀ v, ‖W v‖ ≤ M * (1 + v ^ 2)⁻¹) (n : ℕ) :
    ‖_root_.LSeries.term a 1 n * W (1 / (2 * π) * Real.log (n / x))‖ ≤
      M * (‖_root_.LSeries.term a 1 n‖ * (1 + (1 / (2 * π) * Real.log (n / x)) ^ 2)⁻¹) := by
  rw [norm_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hW _) (norm_nonneg _)

/-- Under a Chebyshev bound, a weight `W` with `‖W v‖ ≤ M (1 + v ^ 2)⁻¹` gives a Dirichlet series
`∑ a n W (log (n / x) / 2π) n⁻ˢ` that converges at `s = 1`, at every scale `x > 0`. -/
theorem LSeriesSummable_mul_comp_log_div
    (hC : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ C * N)
    (hW : ∀ v, ‖W v‖ ≤ M * (1 + v ^ 2)⁻¹) (hx : 0 < x) :
    LSeriesSummable (fun n : ℕ ↦ a n * W (1 / (2 * π) * Real.log (n / x))) 1 := by
  rw [LSeriesSummable, term_mul_comp_log_div]
  exact ((summable_norm_term_mul_inv_one_add_sq hC hx).mul_left M).of_norm_bounded
    (norm_term_mul_le hW)

/-- **The uniform bound for a decaying weight.** Under a Chebyshev bound
`∑_{1 ≤ n ≤ N} ‖a n‖ ≤ C N`, a weight `W` with `‖W v‖ ≤ M (1 + v ^ 2)⁻¹` gives
`‖∑ a n / n * W (log (n / x) / 2π)‖ ≤ M C (1 + 2π²)` for every scale `x > 0`. -/
theorem norm_tsum_term_mul_comp_log_div_le
    (hC : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ C * N)
    (hW : ∀ v, ‖W v‖ ≤ M * (1 + v ^ 2)⁻¹) (hx : 0 < x) :
    ‖∑' n : ℕ, _root_.LSeries.term a 1 n * W (1 / (2 * π) * Real.log (n / x))‖ ≤
      M * (C * (1 + 2 * π ^ 2)) := by
  have hbound := (summable_norm_term_mul_inv_one_add_sq hC hx).mul_left M
  have hnorm := hbound.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_term_mul_le hW)
  have hM : 0 ≤ M := (norm_nonneg _).trans ((hW 0).trans (by simp))
  refine (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum (norm_term_mul_le hW)
    hbound).trans ?_)
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tsum_norm_term_mul_inv_one_add_sq_le hC hx) hM

/-! ### Passing the smoothed asymptotic to approximable weights -/

variable {G : ℂ → ℂ} {A L : ℂ}

/-- **The smoothed Wiener--Ikehara asymptotic for an approximable weight.** Let `a` be
nonnegative, with Dirichlet series summable on `Re s > 1` and a boundary remainder
`G = LSeries a - A / (s - 1)` continuous on `Re s ≥ 1`. Suppose that for every `ε > 0` some smooth
compactly supported `psi` satisfies `‖W v - 𝓕 psi v‖ ≤ ε (1 + v ^ 2)⁻¹` for all `v` and
`‖L - psi 0‖ ≤ ε`. Then `∑ a n / n * W (log (n / x) / 2π) → 2π A L` as `x → ∞`.

For `W = 𝓕 psi` itself this is `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg`
with `L = psi 0`; the point is that `W` need not be the Fourier transform of a compactly
supported function. -/
theorem tendsto_tsum_term_mul_atTop_of_approx_fourier (ha : 0 ≤ a)
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma)
    (happrox : ∀ ε > 0, ∃ psi : ℝ → ℂ, ContDiff ℝ ∞ psi ∧ HasCompactSupport psi ∧
      (∀ v, ‖W v - 𝓕 psi v‖ ≤ ε * (1 + v ^ 2)⁻¹) ∧ ‖L - psi 0‖ ≤ ε) :
    Tendsto (fun x : ℝ ↦
        ∑' n : ℕ, _root_.LSeries.term a 1 n * W (1 / (2 * π) * Real.log (n / x)))
      atTop (𝓝 (2 * (π : ℂ) * A * L)) := by
  obtain ⟨C₀, hC⟩ :=
    exists_sum_Icc_le_mul_of_isBigO (isBigO_sum_Icc_norm_id_of_boundary ha hG hG' hsum)
  set C := max C₀ 0
  replace hC : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ≤ C * N := fun N ↦
    (hC N).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) N.cast_nonneg)
  -- The size of the error: `δ` in the weighted sup norm costs at most `δ K` in the limit.
  set K : ℝ := C * (1 + 2 * π ^ 2) + ‖2 * (π : ℂ) * A‖ + 1 with hK
  have hK0 : 0 < K := by
    have : 0 ≤ C := le_max_right _ _
    positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨psi, hpsi, hsupp, hW, hL⟩ := happrox (ε / (2 * K)) (by positivity)
  obtain ⟨x₀, hx₀⟩ := Metric.tendsto_atTop.1
    (tendsto_tsum_term_mul_fourier_atTop_of_nonneg ha hG hG' hsum hpsi hsupp) (ε / 2)
    (by positivity)
  refine ⟨max x₀ 1, fun x hx ↦ ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx)
  have hmain := hx₀ x ((le_max_left _ _).trans hx)
  -- Split the series into the compactly supported part and the error.
  have hsumpsi : Summable fun n : ℕ ↦
      _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * Real.log (n / x)) := by
    have := LSeriesSummable_mul_fourier_of_nonneg (x := x) ha
      (hG.comp Complex.continuous_ofReal.continuousOn fun r hr ↦ by simpa using hr.1)
      (fun sigma h1 _ ↦ hG' sigma (by simpa using h1)) (fun sigma h1 _ ↦ hsum sigma h1)
      hpsi hsupp hxpos
    rwa [LSeriesSummable, term_mul_comp_log_div] at this
  have hsumerr : Summable fun n : ℕ ↦ _root_.LSeries.term a 1 n *
      (W (1 / (2 * π) * Real.log (n / x)) - 𝓕 psi (1 / (2 * π) * Real.log (n / x))) := by
    have := LSeriesSummable_mul_comp_log_div (W := W - 𝓕 psi) hC hW hxpos
    rw [LSeriesSummable, term_mul_comp_log_div] at this
    simpa only [Pi.sub_apply] using this
  have hsplit : ∑' n : ℕ, _root_.LSeries.term a 1 n * W (1 / (2 * π) * Real.log (n / x)) =
      ∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * Real.log (n / x)) +
        ∑' n : ℕ, _root_.LSeries.term a 1 n *
          (W (1 / (2 * π) * Real.log (n / x)) - 𝓕 psi (1 / (2 * π) * Real.log (n / x))) := by
    rw [← hsumpsi.tsum_add hsumerr]
    exact tsum_congr fun n ↦ by ring
  have herr := norm_tsum_term_mul_comp_log_div_le hC hW hxpos
  have hconst : ‖2 * (π : ℂ) * A * psi 0 - 2 * (π : ℂ) * A * L‖ ≤
      ‖2 * (π : ℂ) * A‖ * (ε / (2 * K)) := by
    rw [← mul_sub, norm_mul, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left hL (norm_nonneg _)
  have hsmall : ε / (2 * K) * (C * (1 + 2 * π ^ 2)) + ‖2 * (π : ℂ) * A‖ * (ε / (2 * K)) ≤
      ε / 2 := by
    calc _ = ε / (2 * K) * (C * (1 + 2 * π ^ 2) + ‖2 * (π : ℂ) * A‖) := by ring
      _ ≤ ε / (2 * K) * K := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hK]
          exact le_add_of_nonneg_right zero_le_one
      _ = ε / 2 := by field_simp
  rw [dist_eq_norm] at hmain ⊢
  rw [hsplit]
  calc
    _ = ‖(∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi
          (1 / (2 * π) * Real.log (n / x))) - 2 * (π : ℂ) * A * psi 0 +
        ∑' n : ℕ, _root_.LSeries.term a 1 n *
          (W (1 / (2 * π) * Real.log (n / x)) - 𝓕 psi
            (1 / (2 * π) * Real.log (n / x))) +
        (2 * (π : ℂ) * A * psi 0 - 2 * (π : ℂ) * A * L)‖ :=
      congrArg norm (by abel)
    _ < ε := by
      refine (norm_add₃_le.trans_lt (add_lt_add_of_lt_of_le
        (add_lt_add_of_lt_of_le hmain herr) hconst)).trans_le ?_
      rw [add_assoc]
      exact (add_le_add_right hsmall _).trans (add_halves ε).le

/-! ### Schwartz test functions -/

/-- **The smoothed Wiener--Ikehara asymptotic for a Schwartz test function.** Let `a` be
nonnegative, with Dirichlet series summable on `Re s > 1` and a boundary remainder
`G = LSeries a - A / (s - 1)` continuous on `Re s ≥ 1`. For every Schwartz function `g` on `ℝ`,
`∑ a n / n * 𝓕 g (log (n / x) / 2π) → 2π A g 0` as `x → ∞`.

This extends `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg` from smooth
compactly supported test functions to Schwartz functions. In particular it applies to every
smooth compactly supported weight `W`, since `W = 𝓕 (𝓕⁻ W)` with `𝓕⁻ W` a Schwartz function. -/
theorem tendsto_tsum_term_mul_fourier_schwartz_atTop (ha : 0 ≤ a)
    (hG : ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → LSeriesSummable a sigma) (g : 𝓢(ℝ, ℂ)) :
    Tendsto (fun x : ℝ ↦
        ∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 (g : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x)))
      atTop (𝓝 (2 * (π : ℂ) * A * g 0)) := by
  refine tendsto_tsum_term_mul_atTop_of_approx_fourier ha hG hG' hsum fun ε hε ↦ ?_
  -- Truncate `g` by a bump function rescaled by `R`; the truncations tend to `g` in `𝓢(ℝ, ℂ)`,
  -- hence so do their Fourier transforms.
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  set u : ℝ → 𝓢(ℝ, ℂ) := fun R ↦ SchwartzMap.smulLeftCLM ℂ (fun y ↦ b (R⁻¹ • y)) g
  have hbdd (i : ℕ) : ∃ B, ∀ x, ‖iteratedFDeriv ℝ i b x‖ ≤ B :=
    (b.contDiff.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (b.hasCompactSupport.iteratedFDeriv i)
  have hu : Tendsto u atTop (𝓝 g) := SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop
    b.contDiff hbdd b.eventuallyEq_one g
  have hFu : Tendsto (fun R ↦ 𝓕 (u R)) atTop (𝓝 (𝓕 g)) :=
    (ContinuousFourier.continuous_fourier.tendsto g).comp hu
  rw [(schwartz_withSeminorms ℝ ℝ ℂ).tendsto_nhds] at hFu
  obtain ⟨R, hR, h0, h2⟩ := ((eventually_gt_atTop 0).and ((hFu (0, 0) (ε / 2) (half_pos hε)).and
    (hFu (2, 0) (ε / 2) (half_pos hε)))).exists
  simp only [SchwartzMap.schwartzSeminormFamily_apply] at h0 h2
  refine ⟨u R, (u R).smooth ⊤, SchwartzMap.hasCompactSupport_smulLeftCLM_comp_inv_smul
    b.contDiff b.hasCompactSupport hR.ne' g, fun v ↦ ?_, ?_⟩
  · -- The weighted sup norm of `𝓕 g - 𝓕 (u R)` is at most two seminorms of it.
    have hv0 := SchwartzMap.norm_le_seminorm ℝ (𝓕 (u R) - 𝓕 g) v
    have hv2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕 (u R) - 𝓕 g) 2 v
    rw [sub_apply, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, norm_sub_rev] at hv0 hv2
    rw [Real.norm_eq_abs, sq_abs] at hv2
    rw [le_mul_inv_iff₀ (by positivity)]
    linarith
  · -- The truncation does not change the value at the origin.
    rw [SchwartzMap.smulLeftCLM_comp_inv_smul_apply
        (b.hasCompactSupport.hasTemperateGrowth b.contDiff),
      smul_zero, b.one_of_mem_closedBall (by simp [b]), one_smul, sub_self, norm_zero]
    exact hε.le

end TauCeti.LSeries

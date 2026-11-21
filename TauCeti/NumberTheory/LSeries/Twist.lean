/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.PSeries
import TauCeti.Algebra.BigOperators.Finset.Periodic
import TauCeti.Algebra.BigOperators.Module
import TauCeti.Analysis.Asymptotics.Sum.Periodic
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Twisting the coefficients of a Dirichlet series by a power of the index

Multiplying the `n`-th coefficient of a Dirichlet series by `n ^ (-z)` translates the series by
`z`: the `n`-th term becomes `f n * n ^ (-z) / n ^ s = f n / n ^ (s + z)`, so the twisted series
at `s` is the original one at `s + z`. The identity is termwise, hence needs no convergence
hypothesis; at a point where neither series converges both sides are Mathlib's junk value `0`.

The purely imaginary parameters `z = -u * I` are the ones a Hecke character twisted by
`N(I) ^ (i u)` produces. They translate the series in the imaginary (vertical) direction, so a
pole of the original series at `s = 1` becomes a pole of the twisted one at `s = 1 + i u`.

For a sequence `a : ℕ → ℂ` that is periodic of period `N ≠ 0` on `k ≥ 1` with vanishing period sum
`∑ k ∈ Icc 1 N, a k = 0` — such as a nontrivial Dirichlet character or the norm coefficients of a
nontrivial ray class character over a degree-one number field — a single summation by parts against
`k ^ (-z)` with `Re z = 0` would lose a logarithm (`∑_{k ≤ n} |Δ(k ^ (-i t))| asymp |t| log n`).
Subtracting the period average of the first partial sums makes the second partial sums bounded too,
and a second summation by parts against the `O(k⁻²)` second difference of `k ↦ k ^ (-z)` recovers a
uniform `O(1)` bound on `∑ k ∈ Icc 1 n, a k * k ^ (-z)` for every `z` with `0 ≤ z.re`. The
half-plane `0 ≤ z.re` is sharp: for `z.re < 0` and `a k = (-1) ^ k` (`N = 2`), the `n`-th summand
itself has norm `n ^ (-z.re) → ∞`, so the partial sums cannot be bounded.

## Main results

* `TauCeti.LSeries.term_mul_natCast_cpow_neg`, `TauCeti.LSeries.LSeries_mul_natCast_cpow_neg`,
  `TauCeti.LSeries.LSeriesSummable_mul_natCast_cpow_neg_iff`, and
  `TauCeti.LSeries.LSeriesHasSum_mul_natCast_cpow_neg_iff`: twisting by `n ^ (-z)` translates
  terms, `tsum` values, summability, and `LSeriesHasSum` from `s` to `s + z`.
* `TauCeti.LSeries.term_mul_natCast_cpow`, `TauCeti.LSeries.LSeries_mul_natCast_cpow`,
  `TauCeti.LSeries.LSeriesSummable_mul_natCast_cpow_iff`, and
  `TauCeti.LSeries.LSeriesHasSum_mul_natCast_cpow_iff`: the positive-exponent versions,
  translating from `s` to `s - z`.
* `TauCeti.LSeries.exists_norm_sum_Icc_mul_natCast_cpow_neg_le` and
  `TauCeti.LSeries.isBigO_sum_Icc_mul_natCast_cpow_neg`: uniform `O(1)` partial-sum bounds for
  `∑ k ∈ Icc 1 n, a k * k ^ (-z)` when `a` is `N`-periodic on `k ≥ 1` (`N ≠ 0`) with zero period
  sum and `0 ≤ z.re`, together with the positive-exponent versions for `z.re ≤ 0`.
-/

public section

namespace TauCeti.LSeries

section Termwise

variable (f : ℕ → ℂ) (z s : ℂ)

/-- Twisting the `n`-th coefficient of a Dirichlet series by `n ^ (-z)` translates its `n`-th
term by `z`. -/
theorem term_mul_natCast_cpow_neg (n : ℕ) :
    LSeries.term (fun n ↦ f n * (n : ℂ) ^ (-z)) s n = LSeries.term f (s + z) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn), Complex.cpow_neg]
  ring

/-- **Twisting a Dirichlet series by a power of the index translates it.** The series of the
coefficients `f n * n ^ (-z)` at `s` is the series of `f` at `s + z`. -/
theorem LSeries_mul_natCast_cpow_neg :
    LSeries (fun n ↦ f n * (n : ℂ) ^ (-z)) s = LSeries f (s + z) :=
  tsum_congr (term_mul_natCast_cpow_neg f z s)

/-- Twisting by `n ^ (-z)` translates absolute summability from `s` to `s + z`. -/
theorem LSeriesSummable_mul_natCast_cpow_neg_iff :
    LSeriesSummable (fun n ↦ f n * (n : ℂ) ^ (-z)) s ↔ LSeriesSummable f (s + z) := by
  simp only [LSeriesSummable, funext (term_mul_natCast_cpow_neg f z s)]

/-- Twisting by `n ^ (-z)` translates `LSeriesHasSum` from `s` to `s + z`. -/
theorem LSeriesHasSum_mul_natCast_cpow_neg_iff (a : ℂ) :
    LSeriesHasSum (fun n ↦ f n * (n : ℂ) ^ (-z)) s a ↔ LSeriesHasSum f (s + z) a := by
  simp only [LSeriesHasSum, funext (term_mul_natCast_cpow_neg f z s)]

/-- Twisting the `n`-th coefficient of a Dirichlet series by `n ^ z` translates its `n`-th term
to `s - z`. -/
theorem term_mul_natCast_cpow (n : ℕ) :
    LSeries.term (fun n ↦ f n * (n : ℂ) ^ z) s n = LSeries.term f (s - z) n := by
  simpa [sub_eq_add_neg] using term_mul_natCast_cpow_neg f (-z) s n

/-- The Dirichlet series of `f n * n ^ z` at `s` equals that of `f` at `s - z`. -/
theorem LSeries_mul_natCast_cpow :
    LSeries (fun n ↦ f n * (n : ℂ) ^ z) s = LSeries f (s - z) :=
  tsum_congr (term_mul_natCast_cpow f z s)

/-- Twisting by `n ^ z` translates absolute summability from `s` to `s - z`. -/
theorem LSeriesSummable_mul_natCast_cpow_iff :
    LSeriesSummable (fun n ↦ f n * (n : ℂ) ^ z) s ↔ LSeriesSummable f (s - z) := by
  simp only [LSeriesSummable, funext (term_mul_natCast_cpow f z s)]

/-- Twisting by `n ^ z` translates `LSeriesHasSum` from `s` to `s - z`. -/
theorem LSeriesHasSum_mul_natCast_cpow_iff (a : ℂ) :
    LSeriesHasSum (fun n ↦ f n * (n : ℂ) ^ z) s a ↔ LSeriesHasSum f (s - z) a := by
  simp only [LSeriesHasSum, funext (term_mul_natCast_cpow f z s)]

end Termwise

section PeriodicPartialSums

open Asymptotics Filter

/-- Second-order summation by parts on `Finset.Icc 1 (m + 2)` after subtracting a constant shift `μ`
from the first partial sums. -/
private theorem sum_Icc_add_two_eq (a f : ℕ → ℂ) (μ : ℂ) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 (m + 2), a k * f k =
      (∑ j ∈ Finset.Icc 1 (m + 2), a j) * f (m + 2) - μ * (f (m + 2) - f 1) -
        (∑ j ∈ Finset.Icc 1 (m + 1), ((∑ i ∈ Finset.Icc 1 j, a i) - μ)) *
          (f (m + 2) - f (m + 1)) +
        ∑ k ∈ Finset.Icc 1 m,
          (∑ j ∈ Finset.Icc 1 k, ((∑ i ∈ Finset.Icc 1 j, a i) - μ)) *
            ((f (k + 2) - f (k + 1)) - (f (k + 1) - f k)) := by
  have hsbp (u v : ℕ → ℂ) (n : ℕ) :
      ∑ k ∈ Finset.Icc 1 (n + 1), u k * v k =
        (∑ j ∈ Finset.Icc 1 (n + 1), u j) * v (n + 1) -
          ∑ k ∈ Finset.Icc 1 n, (∑ j ∈ Finset.Icc 1 k, u j) * (v (k + 1) - v k) := by
    simpa [smul_eq_mul] using Finset.sum_Icc_succ_by_parts' u v n
  have hsbp1 := hsbp a f (m + 1)
  have hsplit : ∑ k ∈ Finset.Icc 1 (m + 1), (∑ i ∈ Finset.Icc 1 k, a i) * (f (k + 1) - f k) =
      ∑ k ∈ Finset.Icc 1 (m + 1), ((∑ i ∈ Finset.Icc 1 k, a i) - μ) * (f (k + 1) - f k) +
        μ * (f (m + 2) - f 1) := by
    have hA_eq (k : ℕ) : (∑ i ∈ Finset.Icc 1 k, a i) * (f (k + 1) - f k) =
        ((∑ i ∈ Finset.Icc 1 k, a i) - μ) * (f (k + 1) - f k) + μ * (f (k + 1) - f k) := by ring
    simp_rw [hA_eq, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_Icc_sub (Nat.le_add_left 1 m) f]
  have hsbp2 := hsbp (fun j ↦ (∑ i ∈ Finset.Icc 1 j, a i) - μ) (fun k ↦ f (k + 1) - f k) m
  rw [hsbp1, hsplit, hsbp2]
  ring

private theorem norm_sum_Icc_mul_secondDiff_le {B : ℕ → ℂ} {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hB : ∀ k, ‖B k‖ ≤ M₂) {z : ℂ} (hz : 0 ≤ z.re) (m : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 m, B k *
        ((((k + 2 : ℕ) : ℂ) ^ (-z) - ((k + 1 : ℕ) : ℂ) ^ (-z)) -
          (((k + 1 : ℕ) : ℂ) ^ (-z) - (k : ℂ) ^ (-z)))‖ ≤
      2 * M₂ * ‖z‖ * ‖z + 1‖ := by
  have hsq : ∑ k ∈ Finset.Icc 1 m, ((k : ℝ) ^ 2)⁻¹ ≤ 2 := by
    rw [show Finset.Icc 1 m = Finset.Ioo 0 (m + 1) by ext k; simp; omega]
    simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 (m + 1)
  calc ‖∑ k ∈ Finset.Icc 1 m, B k *
          ((((k + 2 : ℕ) : ℂ) ^ (-z) - ((k + 1 : ℕ) : ℂ) ^ (-z)) -
            (((k + 1 : ℕ) : ℂ) ^ (-z) - (k : ℂ) ^ (-z)))‖
      ≤ ∑ k ∈ Finset.Icc 1 m, ‖B k‖ *
          ‖(((k + 2 : ℕ) : ℂ) ^ (-z) - ((k + 1 : ℕ) : ℂ) ^ (-z)) -
            (((k + 1 : ℕ) : ℂ) ^ (-z) - (k : ℂ) ^ (-z))‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ ↦ norm_mul _ _))
    _ ≤ ∑ k ∈ Finset.Icc 1 m, M₂ * (‖z‖ * ‖z + 1‖ / (k : ℝ) ^ 2) :=
        Finset.sum_le_sum fun k hk ↦ mul_le_mul (hB k)
          (norm_natCast_add_two_cpow_neg_sub_sub_le hz (Finset.mem_Icc.mp hk).1)
          (norm_nonneg _) hM₂
    _ = M₂ * ‖z‖ * ‖z + 1‖ * ∑ k ∈ Finset.Icc 1 m, ((k : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ ≤ M₂ * ‖z‖ * ‖z + 1‖ * 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2 * M₂ * ‖z‖ * ‖z + 1‖ := by ring

/-- **Uniform partial-sum bound for index-power twists of a zero-mean periodic sequence.**
Let `a : ℕ → ℂ` be periodic of period `N ≠ 0` on positive indices (`a (k + N) = a k` for all
`k ≥ 1`) with vanishing period sum `∑ k ∈ Icc 1 N, a k = 0`. Then for every `z : ℂ` with
`0 ≤ z.re`, the twisted partial sums `∑ k ∈ Icc 1 n, a k * k ^ (-z)` are uniformly bounded in norm
for all `n : ℕ`. -/
theorem exists_norm_sum_Icc_mul_natCast_cpow_neg_le {a : ℕ → ℂ} {N : ℕ} (hN : N ≠ 0)
    (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (hsum : ∑ k ∈ Finset.Icc 1 N, a k = 0)
    {z : ℂ} (hz : 0 ≤ z.re) :
    ∃ C : ℝ, ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, a k * (k : ℂ) ^ (-z)‖ ≤ C := by
  let A₁ : ℕ → ℂ := fun k ↦ ∑ j ∈ Finset.Icc 1 k, a j
  let M₁ : ℝ := ∑ j ∈ Finset.Icc 1 N, ‖a j‖
  have hA₁_per : Function.Periodic A₁ N := Finset.periodic_sum_Icc_of_sum_eq_zero hper hsum
  have hA₁_le (k : ℕ) : ‖A₁ k‖ ≤ M₁ := Finset.norm_sum_Icc_le_of_sum_eq_zero hN hper hsum k
  let μ : ℂ := (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, A₁ j
  let b : ℕ → ℂ := fun k ↦ A₁ k - μ
  have hb_sum : ∑ j ∈ Finset.Icc 1 N, b j = 0 := by
    simp [b, Finset.sum_sub_distrib, μ,
      mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr hN : (N : ℂ) ≠ 0)]
  let B : ℕ → ℂ := fun k ↦ ∑ j ∈ Finset.Icc 1 k, b j
  let M₂ : ℝ := ∑ j ∈ Finset.Icc 1 N, ‖b j‖
  have hB_le (k : ℕ) : ‖B k‖ ≤ M₂ :=
    Finset.norm_sum_Icc_le_of_sum_eq_zero hN (fun j _ ↦ by simp [b, hA₁_per j]) hb_sum k
  have hM₁ : 0 ≤ M₁ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hM₂ : 0 ≤ M₂ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  let f : ℕ → ℂ := fun k ↦ (k : ℂ) ^ (-z)
  refine ⟨M₁ + 2 * ‖μ‖ + M₂ * ‖z‖ + 2 * M₂ * ‖z‖ * ‖z + 1‖, fun n ↦ ?_⟩
  rcases n with _ | _ | m
  · rw [Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.sum_empty, norm_zero]
    positivity
  · rw [Finset.Icc_self, Finset.sum_singleton, norm_mul]
    have hterm : ‖a 1‖ * ‖f 1‖ ≤ M₁ := by simpa [A₁, f] using hA₁_le 1
    have hrest : 0 ≤ 2 * ‖μ‖ + M₂ * ‖z‖ + 2 * M₂ * ‖z‖ * ‖z + 1‖ := by positivity
    linarith
  · rw [sum_Icc_add_two_eq a f μ m]
    have hb1 : ‖A₁ (m + 2) * f (m + 2)‖ ≤ M₁ := by
      rw [norm_mul]
      simpa [f] using mul_le_mul (hA₁_le (m + 2))
        (norm_natCast_cpow_neg_le_one hz (m + 2)) (norm_nonneg _) hM₁
    have hb2 : ‖μ * (f (m + 2) - f 1)‖ ≤ 2 * ‖μ‖ := by
      rw [norm_mul, mul_comm 2]
      refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (norm_nonneg μ)
      linarith [norm_natCast_cpow_neg_le_one hz (m + 2), norm_natCast_cpow_neg_le_one hz 1]
    have hb3 : ‖B (m + 1) * (f (m + 2) - f (m + 1))‖ ≤ M₂ * ‖z‖ := by
      rw [norm_mul]
      exact mul_le_mul (hB_le (m + 1))
        (norm_natCast_add_one_cpow_neg_sub_le_norm hz (by omega)) (norm_nonneg _) hM₂
    exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add ((norm_sub_le _ _).trans (add_le_add hb1 hb2)) hb3))
      (norm_sum_Icc_mul_secondDiff_le hM₂ hB_le hz m))

/-- **Asymptotic `O(1)` form** of `exists_norm_sum_Icc_mul_natCast_cpow_neg_le`. -/
theorem isBigO_sum_Icc_mul_natCast_cpow_neg {a : ℕ → ℂ} {N : ℕ} (hN : N ≠ 0)
    (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (hsum : ∑ k ∈ Finset.Icc 1 N, a k = 0)
    {z : ℂ} (hz : 0 ≤ z.re) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, a k * (k : ℂ) ^ (-z)) =O[atTop] (1 : ℕ → ℝ) := by
  obtain ⟨C, hC⟩ := exists_norm_sum_Icc_mul_natCast_cpow_neg_le hN hper hsum hz
  exact IsBigO.of_bound C (Eventually.of_forall fun n ↦ by simpa using hC n)

/-- Positive-exponent version of `exists_norm_sum_Icc_mul_natCast_cpow_neg_le`, for `z.re ≤ 0`. -/
theorem exists_norm_sum_Icc_mul_natCast_cpow_le {a : ℕ → ℂ} {N : ℕ} (hN : N ≠ 0)
    (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (hsum : ∑ k ∈ Finset.Icc 1 N, a k = 0)
    {z : ℂ} (hz : z.re ≤ 0) :
    ∃ C : ℝ, ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, a k * (k : ℂ) ^ z‖ ≤ C := by
  simpa using exists_norm_sum_Icc_mul_natCast_cpow_neg_le hN hper hsum
    (z := -z) (by simpa using hz)

/-- Positive-exponent version of `isBigO_sum_Icc_mul_natCast_cpow_neg`, for `z.re ≤ 0`. -/
theorem isBigO_sum_Icc_mul_natCast_cpow {a : ℕ → ℂ} {N : ℕ} (hN : N ≠ 0)
    (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (hsum : ∑ k ∈ Finset.Icc 1 N, a k = 0)
    {z : ℂ} (hz : z.re ≤ 0) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, a k * (k : ℂ) ^ z) =O[atTop] (1 : ℕ → ℝ) := by
  simpa using isBigO_sum_Icc_mul_natCast_cpow_neg hN hper hsum
    (z := -z) (by simpa using hz)

end PeriodicPartialSums

end TauCeti.LSeries

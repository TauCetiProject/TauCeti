/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Algebra.BigOperators.Periodic

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
  `TauCeti.LSeries.isBigO_sum_Icc_mul_natCast_cpow_neg_one`: uniform `O(1)` partial-sum bounds for
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

/-- Summation by parts on `Finset.Icc 1 (m + 1)`. -/
private theorem sum_Icc_succ_by_parts (u v : ℕ → ℂ) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 (m + 1), u k * v k =
      (∑ j ∈ Finset.Icc 1 (m + 1), u j) * v (m + 1) -
        ∑ k ∈ Finset.Icc 1 m, (∑ j ∈ Finset.Icc 1 k, u j) * (v (k + 1) - v k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : Finset.Icc 1 (m + 2) = insert (m + 2) (Finset.Icc 1 (m + 1)) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h2 : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hsum_m1 : ∑ k ∈ Finset.Icc 1 (m + 1), (∑ j ∈ Finset.Icc 1 k, u j) * (v (k + 1) - v k) =
        (∑ j ∈ Finset.Icc 1 (m + 1), u j) * (v (m + 2) - v (m + 1)) +
          ∑ k ∈ Finset.Icc 1 m, (∑ j ∈ Finset.Icc 1 k, u j) * (v (k + 1) - v k) := by
      conv_lhs => rw [h2]
      rw [Finset.sum_insert (by simp)]
    rw [h1, Finset.sum_insert (by simp), Finset.sum_insert (by simp), ih, hsum_m1]
    ring

/-- Mean-value bound on the forward difference `(y + 1) ^ (-w) - y ^ (-w)` for `y > 0` and
`-1 ≤ w.re`. -/
private theorem norm_add_one_cpow_neg_sub_le (w : ℂ) (hw : -1 ≤ w.re) {y : ℝ} (hy : 0 < y) :
    ‖((y + 1 : ℝ) : ℂ) ^ (-w) - (y : ℂ) ^ (-w)‖ ≤ ‖w‖ * y ^ (-w.re - 1) := by
  have hderiv : ∀ x ∈ Set.Ici y,
      HasDerivWithinAt (fun t : ℝ ↦ (t : ℂ) ^ (-w)) (-w * (x : ℂ) ^ (-w - 1)) (Set.Ici y) x :=
    fun x hx ↦ (((Complex.hasStrictDerivAt_cpow_const (c := -w)
      (Complex.ofReal_mem_slitPlane.mpr (hy.trans_le hx))).hasDerivAt).comp_ofReal).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ici y, ‖-w * (x : ℂ) ^ (-w - 1)‖ ≤ ‖w‖ * y ^ (-w.re - 1) := by
    intro x hx
    have hxpos : 0 < x := hy.trans_le hx
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
      Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hy hx (by linarith)) (norm_nonneg w)
  have hmvt := (convex_Ici y).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (le_rfl : y ∈ Set.Ici y) (show y + 1 ∈ Set.Ici y by simp)
  simpa using hmvt

/-- For `1 ≤ k` and `0 ≤ z.re`, `‖k ^ (-z)‖ ≤ 1`. -/
private theorem norm_natCast_cpow_neg_le_one {z : ℂ} (hz : 0 ≤ z.re) {k : ℕ} (hk : 1 ≤ k) :
    ‖(k : ℂ) ^ (-z)‖ ≤ 1 := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hkpos, Complex.neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk) (by linarith)

/-- First forward difference bound: `‖(k + 1) ^ (-z) - k ^ (-z)‖ ≤ ‖z‖` for `1 ≤ k` and
`0 ≤ z.re`. -/
private theorem norm_firstDiff_natCast_cpow_neg_le {z : ℂ} (hz : 0 ≤ z.re) {k : ℕ}
    (hk : 1 ≤ k) : ‖((k + 1 : ℕ) : ℂ) ^ (-z) - (k : ℂ) ^ (-z)‖ ≤ ‖z‖ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := zero_lt_one.trans_le hk1
  have h := norm_add_one_cpow_neg_sub_le z (by linarith) hkpos
  have hrpow : (k : ℝ) ^ (-z.re - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hk1 (by linarith)
  calc ‖((k + 1 : ℕ) : ℂ) ^ (-z) - (k : ℂ) ^ (-z)‖
      = ‖(((k : ℝ) + 1 : ℝ) : ℂ) ^ (-z) - ((k : ℝ) : ℂ) ^ (-z)‖ := by push_cast; rfl
    _ ≤ ‖z‖ * (k : ℝ) ^ (-z.re - 1) := h
    _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hrpow (norm_nonneg z)
    _ = ‖z‖ := mul_one _

/-- Second forward difference bound:
`‖((k + 2) ^ (-z) - (k + 1) ^ (-z)) - ((k + 1) ^ (-z) - k ^ (-z))‖ ≤ ‖z‖ * ‖z + 1‖ / k ^ 2`
for `1 ≤ k` and `0 ≤ z.re`. -/
private theorem norm_secondDiff_natCast_cpow_neg_le {z : ℂ} (hz : 0 ≤ z.re) {k : ℕ}
    (hk : 1 ≤ k) :
    ‖(((k + 2 : ℕ) : ℂ) ^ (-z) - ((k + 1 : ℕ) : ℂ) ^ (-z)) -
        (((k + 1 : ℕ) : ℂ) ^ (-z) - (k : ℂ) ^ (-z))‖ ≤
      ‖z‖ * ‖z + 1‖ / (k : ℝ) ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := zero_lt_one.trans_le hk1
  let g : ℝ → ℂ := fun y ↦ ((y : ℂ) + 1) ^ (-z) - (y : ℂ) ^ (-z)
  have hderiv : ∀ x ∈ Set.Ici (k : ℝ),
      HasDerivWithinAt g
        (-z * (((x + 1 : ℝ) : ℂ) ^ (-(z + 1)) - (x : ℂ) ^ (-(z + 1)))) (Set.Ici (k : ℝ)) x := by
    intro x (hx : (k : ℝ) ≤ x)
    have hxpos : 0 < x := hkpos.trans_le hx
    have hslit1 : ((x : ℂ) + 1) ∈ Complex.slitPlane := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add]
      exact Complex.ofReal_mem_slitPlane.mpr (by linarith)
    have h1 : HasDerivAt (fun w : ℂ ↦ (w + 1) ^ (-z))
        (-z * ((x + 1 : ℝ) : ℂ) ^ (-(z + 1))) (x : ℂ) :=
      (((hasDerivAt_id' (x : ℂ)).add_const (1 : ℂ)).cpow_const (c := -z) hslit1).congr_deriv
        (by push_cast; ring_nf)
    have h2 : HasDerivAt (fun w : ℂ ↦ w ^ (-z))
        (-z * (x : ℂ) ^ (-(z + 1))) (x : ℂ) :=
      ((hasDerivAt_id' (x : ℂ)).cpow_const (c := -z)
        (Complex.ofReal_mem_slitPlane.mpr hxpos)).congr_deriv (by ring_nf)
    exact (((h1.comp_ofReal).sub (h2.comp_ofReal)).congr_deriv (by ring)).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ici (k : ℝ),
      ‖-z * (((x + 1 : ℝ) : ℂ) ^ (-(z + 1)) - (x : ℂ) ^ (-(z + 1)))‖ ≤
        ‖z‖ * ‖z + 1‖ / (k : ℝ) ^ 2 := by
    intro x (hx : (k : ℝ) ≤ x)
    have hxpos : 0 < x := hkpos.trans_le hx
    have hdiff := norm_add_one_cpow_neg_sub_le (z + 1)
      (by simp [Complex.add_re]; linarith) hxpos
    have hexp : x ^ (-(z + 1).re - 1) ≤ (k : ℝ) ^ (-2 : ℝ) := by
      calc x ^ (-(z + 1).re - 1)
          ≤ x ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (hk1.trans hx)
              (by simp [Complex.add_re]; linarith)
        _ ≤ (k : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_nonpos hkpos hx (by norm_num)
    have hsq : (k : ℝ) ^ (-2 : ℝ) = ((k : ℝ) ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hkpos.le, Real.rpow_natCast]
    rw [norm_mul, norm_neg, div_eq_mul_inv, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (hdiff.trans (by rw [← hsq]; exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)))
      (norm_nonneg z)
  have hmvt := (convex_Ici (k : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (le_rfl : (k : ℝ) ∈ Set.Ici (k : ℝ)) (show (k : ℝ) + 1 ∈ Set.Ici (k : ℝ) by simp)
  have heq : g ((k : ℝ) + 1) - g (k : ℝ) =
      (((k + 2 : ℕ) : ℂ) ^ (-z) - ((k + 1 : ℕ) : ℂ) ^ (-z)) -
        (((k + 1 : ℕ) : ℂ) ^ (-z) - (k : ℂ) ^ (-z)) := by
    simp only [g]
    push_cast
    ring_nf
  rw [← heq]
  simpa using hmvt

/-- Elementary telescoping bound `∑ k ∈ Icc 1 m, 1 / k ^ 2 ≤ 2`. -/
private theorem sum_Icc_one_div_sq_le_two (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, (1 / (k : ℝ) ^ 2) ≤ 2 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    clear hm
    suffices h : ∑ k ∈ Finset.Icc 1 (d + 1), (1 / (k : ℝ) ^ 2) ≤ 2 - 1 / ((d + 1 : ℕ) : ℝ) by
      have : (0 : ℝ) ≤ 1 / ((d + 1 : ℕ) : ℝ) := by positivity
      linarith
    induction d with
    | zero => norm_num
    | succ d ih =>
      have h1 : Finset.Icc 1 (d + 2) = insert (d + 2) (Finset.Icc 1 (d + 1)) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [h1, Finset.sum_insert (by simp)]
      have hd1 : (0 : ℝ) < (d + 1 : ℕ) := by positivity
      have hd2 : (0 : ℝ) < (d + 2 : ℕ) := by positivity
      have hstep : 1 / ((d + 2 : ℕ) : ℝ) ^ 2 ≤
          1 / ((d + 1 : ℕ) : ℝ) - 1 / ((d + 2 : ℕ) : ℝ) := by
        rw [div_sub_div _ _ hd1.ne' hd2.ne', div_le_div_iff₀ (pow_pos hd2 2) (mul_pos hd1 hd2)]
        push_cast
        nlinarith
      linarith

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
  have hsbp1 := sum_Icc_succ_by_parts a f (m + 1)
  have hsplit : ∑ k ∈ Finset.Icc 1 (m + 1), (∑ i ∈ Finset.Icc 1 k, a i) * (f (k + 1) - f k) =
      ∑ k ∈ Finset.Icc 1 (m + 1), ((∑ i ∈ Finset.Icc 1 k, a i) - μ) * (f (k + 1) - f k) +
        μ * (f (m + 2) - f 1) := by
    have hA_eq (k : ℕ) : (∑ i ∈ Finset.Icc 1 k, a i) * (f (k + 1) - f k) =
        ((∑ i ∈ Finset.Icc 1 k, a i) - μ) * (f (k + 1) - f k) + μ * (f (k + 1) - f k) := by ring
    simp_rw [hA_eq, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_Icc_sub (Nat.le_add_left 1 m) f]
  have hsbp2 := sum_Icc_succ_by_parts (fun j ↦ (∑ i ∈ Finset.Icc 1 j, a i) - μ)
    (fun k ↦ f (k + 1) - f k) m
  rw [hsbp1, hsplit, hsbp2]
  ring

private theorem norm_sum_Icc_mul_secondDiff_le {B : ℕ → ℂ} {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hB : ∀ k, ‖B k‖ ≤ M₂) {z : ℂ} (hz : 0 ≤ z.re) (m : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 m, B k *
        ((((k + 2 : ℕ) : ℂ) ^ (-z) - ((k + 1 : ℕ) : ℂ) ^ (-z)) -
          (((k + 1 : ℕ) : ℂ) ^ (-z) - (k : ℂ) ^ (-z)))‖ ≤
      2 * M₂ * ‖z‖ * ‖z + 1‖ := by
  calc ‖∑ k ∈ Finset.Icc 1 m, B k *
          ((((k + 2 : ℕ) : ℂ) ^ (-z) - ((k + 1 : ℕ) : ℂ) ^ (-z)) -
            (((k + 1 : ℕ) : ℂ) ^ (-z) - (k : ℂ) ^ (-z)))‖
      ≤ ∑ k ∈ Finset.Icc 1 m, ‖B k‖ *
          ‖(((k + 2 : ℕ) : ℂ) ^ (-z) - ((k + 1 : ℕ) : ℂ) ^ (-z)) -
            (((k + 1 : ℕ) : ℂ) ^ (-z) - (k : ℂ) ^ (-z))‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ ↦ norm_mul _ _))
    _ ≤ ∑ k ∈ Finset.Icc 1 m, M₂ * (‖z‖ * ‖z + 1‖ / (k : ℝ) ^ 2) :=
        Finset.sum_le_sum fun k hk ↦ mul_le_mul (hB k)
          (norm_secondDiff_natCast_cpow_neg_le hz (Finset.mem_Icc.mp hk).1) (norm_nonneg _) hM₂
    _ = M₂ * ‖z‖ * ‖z + 1‖ * ∑ k ∈ Finset.Icc 1 m, (1 / (k : ℝ) ^ 2) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ ≤ M₂ * ‖z‖ * ‖z + 1‖ * 2 :=
        mul_le_mul_of_nonneg_left (sum_Icc_one_div_sq_le_two m) (by positivity)
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
      simpa using mul_le_mul (hA₁_le (m + 2))
        (norm_natCast_cpow_neg_le_one hz (by omega)) (norm_nonneg _) hM₁
    have hb2 : ‖μ * (f (m + 2) - f 1)‖ ≤ 2 * ‖μ‖ := by
      rw [norm_mul, mul_comm 2]
      refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (norm_nonneg μ)
      linarith [norm_natCast_cpow_neg_le_one hz (show 1 ≤ m + 2 by omega),
        norm_natCast_cpow_neg_le_one hz le_rfl]
    have hb3 : ‖B (m + 1) * (f (m + 2) - f (m + 1))‖ ≤ M₂ * ‖z‖ := by
      rw [norm_mul]
      exact mul_le_mul (hB_le (m + 1))
        (norm_firstDiff_natCast_cpow_neg_le hz (by omega)) (norm_nonneg _) hM₂
    exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add ((norm_sub_le _ _).trans (add_le_add hb1 hb2)) hb3))
      (norm_sum_Icc_mul_secondDiff_le hM₂ hB_le hz m))

/-- **Asymptotic `O(1)` form** of `exists_norm_sum_Icc_mul_natCast_cpow_neg_le`. -/
theorem isBigO_sum_Icc_mul_natCast_cpow_neg_one {a : ℕ → ℂ} {N : ℕ} (hN : N ≠ 0)
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

/-- Positive-exponent version of `isBigO_sum_Icc_mul_natCast_cpow_neg_one`, for `z.re ≤ 0`. -/
theorem isBigO_sum_Icc_mul_natCast_cpow_one {a : ℕ → ℂ} {N : ℕ} (hN : N ≠ 0)
    (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (hsum : ∑ k ∈ Finset.Icc 1 N, a k = 0)
    {z : ℂ} (hz : z.re ≤ 0) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, a k * (k : ℂ) ^ z) =O[atTop] (1 : ℕ → ℝ) := by
  simpa using isBigO_sum_Icc_mul_natCast_cpow_neg_one hN hper hsum
    (z := -z) (by simpa using hz)

end PeriodicPartialSums

end TauCeti.LSeries

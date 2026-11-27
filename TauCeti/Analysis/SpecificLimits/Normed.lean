/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.Ring
import TauCeti.Analysis.Normed.Ring.InfiniteSum

/-!
# Geometric series in seminormed rings and normed fields

The norms of the powers of an element in the open unit ball form a summable series, even when
the seminorm is not normalized. The same holds after multiplication by bounded coefficients.
Completeness then gives summability in the ring itself. In a complete seminormed group, a
sequence whose consecutive norms shrink by factors `C ρᵏ` with `ρ < 1` is summable, by the ratio
test. In any seminormed ring, the shifted polynomial-geometric terms `(n + c) ^ k * r ^ n` tend to
zero whenever `‖r‖ < 1`, which absorbs polynomial growth after shifting an index; under the same
hypothesis `‖r‖ < 1`, in any normed ring with summable geometric series, the series
`∑ (n + c) ^ k * r ^ n` is summable. Summability of `∑ n * f n * r ^ n` and `∑ f n * r ^ n`
yields summability of `∑ (n + 1) * f n * r ^ (n + 1)`. On the closed unit ball away from `1`, the
geometric partial sums are bounded by `2 / ‖x - 1‖`. **Dirichlet's test** holds for coefficients
of bounded variation tending to zero: their products with a sequence of bounded partial sums have
Cauchy partial sums.
Quantitatively, Abel's inequality bounds a block `∑ n ∈ Ioc K M, w n • a n` by `2 B w (K + 1)`
when the partial sums of `a` are at most `B` and the weights `w` are nonnegative and antitone, so
a convergent series of this shape has tail at most `2 B w (K + 1)` after `K` terms.

In a normed division ring, a geometric series indexed by positive integers sums to `r / (1 - r)`
for `‖r‖ < 1`.

Over a normed field, the evaluations below specialize Mathlib's binomial geometric-series
formula to linear and quadratic coefficients, without requiring completeness or an ultrametric
norm; the affine case `∑ (a k + b) xᵏ` holds more generally in a normed division ring.
Finite products of geometric series converge unconditionally over all exponent vectors,
giving the product Cauchy kernel expansion. Over a complete normed field, the Lambert series
`∑_{n ≥ 1} f(qⁿw)` is the power series `∑_{k ≥ 1} c(k - 1) qᵏ wᵏ / (1 - qᵏ)` in `w` for every
power series `f(z) = ∑_{k ≥ 0} c(k) z^(k + 1)` whose coefficients grow slowly enough. This applies
to `z / (1 - z)²`, `z² / (1 - z)³` and `z / (1 - z)³`, whose coefficients are binomial.

The geometric weights `(1 - q) qᵏ` sum to `1` and have mean `q / (1 - q)`, so over a normed
field they average an affine function `c k + B` of `k` to `c q / (1 - q) + B`. For `‖d‖ > 1` the
shifted series `∑ₘ C d⁻⁽ᵐ⁺¹⁾` sums to `C / (d - 1)`, the bound behind Tate's limit.

Dirichlet's test `Filter.Tendsto.cauchySeq_series_smul_of_summable_norm_sub` is adapted from the
lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Hypergeometric/AnalyticProperties.lean`, where it is
`exists_tendsto_sum_mul_of_bdd_variation`.
-/

public section

namespace TauCeti

/-- In a normed division ring, the geometric series over the positive integers sums to
`r / (1 - r)` whenever `‖r‖ < 1`. -/
theorem hasSum_geometric_pnat {K : Type*} [NormedDivisionRing K] {r : K} (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ+ ↦ r ^ (n : ℕ)) (r / (1 - r)) := by
  refine (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ ↦ r ^ n)).2 ?_
  simpa only [pow_succ', div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hr).mul_left r

/-- The norms of the powers of an element in the open unit ball are summable in a seminormed
ring, without requiring a normalized seminorm. -/
theorem summable_norm_pow_of_norm_lt_one {K : Type*} [SeminormedRing K]
    {q : K} (hq : ‖q‖ < 1) : Summable (fun n : ℕ ↦ ‖q ^ n‖) := by
  -- The positive-degree estimate does not require any bound on the seminorm of one.
  rw [← summable_nat_add_iff 1]
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun n ↦ norm_pow_le' q n.succ_pos)
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq))

/-- A geometric series with bounded coefficients is absolutely summable in a seminormed ring
when the parameter belongs to the open unit ball. -/
theorem summable_norm_mul_pow_of_norm_le {K : Type*} [SeminormedRing K]
    {b : ℕ → K} {C : ℝ} (hb : ∀ n, ‖b n‖ ≤ C) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ ‖b n * q ^ n‖) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    ((summable_norm_pow_of_norm_lt_one hq).mul_left C)
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))

/-- A geometric series with bounded coefficients is summable in a complete seminormed ring
when the parameter belongs to the open unit ball. -/
theorem summable_mul_pow_of_norm_le {K : Type*} [SeminormedRing K] [CompleteSpace K]
    {b : ℕ → K} {C : ℝ} (hb : ∀ n, ‖b n‖ ≤ C) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ b n * q ^ n) :=
  (summable_norm_mul_pow_of_norm_le hb hq).of_norm

/-- Geometric majorant bound: if `‖t‖ ≤ M ^ m * S ^ (m + 1)`, then
`‖t * x ^ (m + 1)‖ ≤ (S * ‖x‖) * (M * S * ‖x‖) ^ m`. -/
theorem norm_mul_pow_succ_le {R : Type*} [SeminormedRing R] {t x : R} {M S : ℝ} {m : ℕ}
    (ht : ‖t‖ ≤ M ^ m * S ^ (m + 1)) :
    ‖t * x ^ (m + 1)‖ ≤ (S * ‖x‖) * (M * S * ‖x‖) ^ m :=
  (norm_mul_le _ _).trans <| (mul_le_mul ht (norm_pow_le' x m.succ_pos) (norm_nonneg _)
    ((norm_nonneg t).trans ht)).trans_eq (by simp only [Nat.succ_eq_add_one]; ring)

/-- Geometric summability criterion for shifted power series `∑ m, f m * x ^ (m + 1)` with bounds
`‖f m‖ ≤ M ^ m * S ^ (m + 1)`. -/
theorem summable_norm_mul_pow_succ_of_le {R : Type*} [SeminormedRing R] {f : ℕ → R} {M S : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) {x : R} (hx : M * S * ‖x‖ < 1)
    (hf : ∀ m, ‖f m‖ ≤ M ^ m * S ^ (m + 1)) :
    Summable fun m : ℕ ↦ ‖f m * x ^ (m + 1)‖ :=
  ((summable_geometric_of_lt_one (by positivity) hx).mul_left (S * ‖x‖)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun m ↦ norm_mul_pow_succ_le (hf m)

/-- A sequence whose consecutive norms shrink by a factor `C ρᵏ` with `ρ < 1` is summable. -/
theorem summable_of_norm_succ_le_mul_pow {E : Type*} [SeminormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → E} {C ρ : ℝ} (hρ : ρ < 1) (h : ∀ k, ‖f (k + 1)‖ ≤ C * ρ ^ k * ‖f k‖) :
    Summable f := by
  rcases le_or_gt 0 ρ with hρ₀ | hρ₀
  · have ht : Filter.Tendsto (fun k : ℕ ↦ C * ρ ^ k) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ₀ hρ).const_mul C
    refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
    filter_upwards [(tendsto_order.1 ht).2 (1 / 2) (by norm_num)] with k hk
    exact (h k).trans (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _))
  · -- For `ρ < 0` the factors `C ρᵏ` and `C ρᵏ⁺¹` cannot both be positive, so `‖f n‖` dies out.
    have hstep (k : ℕ) (hk : C * ρ ^ k ≤ 0) : ‖f (k + 1)‖ ≤ 0 :=
      (h k).trans (mul_nonpos_of_nonpos_of_nonneg hk (norm_nonneg _))
    have hzero (j : ℕ) (hj : ‖f j‖ ≤ 0) (n : ℕ) : ‖f (j + n)‖ ≤ 0 := by
      induction n with
      | zero => exact hj
      | succ n ih =>
        have h1 := h (j + n)
        rw [← add_assoc]
        rwa [le_antisymm ih (norm_nonneg _), mul_zero] at h1
    obtain ⟨j, hj2, hj⟩ : ∃ j ≤ 2, ‖f j‖ ≤ 0 := by
      rcases le_or_gt C 0 with hC | hC
      · exact ⟨1, by norm_num, hstep 0 (by simpa using hC)⟩
      · exact ⟨2, le_rfl, hstep 1 (by simpa using mul_neg_of_pos_of_neg hC hρ₀ |>.le)⟩
    refine Summable.of_norm_bounded_eventually_nat (g := fun _ ↦ 0) summable_zero ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    simpa [add_tsub_cancel_of_le (hj2.trans hn)] using hzero j hj (n - j)

/-- For any shift `c` and `r` with `‖r‖ < 1` in a seminormed ring, the shifted
polynomial-geometric sequence `(n + c) ^ k * r ^ n` tends to `0`. This is useful for absorbing
polynomial growth after shifting an index. -/
theorem tendsto_add_pow_mul_pow_of_norm_lt_one {R : Type*} [SeminormedRing R] (c : R) (k : ℕ)
    {r : R} (hr : ‖r‖ < 1) :
    Filter.Tendsto (fun n : ℕ ↦ ((n : R) + c) ^ k * r ^ n) Filter.atTop (nhds 0) := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simpa using tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr
  -- for `n ≥ 1`, `‖(n + c) ^ k * r ^ n‖ ≤ (‖1‖ + ‖c‖) ^ k * (n ^ k * ‖r‖ ^ n)`, and Mathlib's
  -- unshifted limit sends the right-hand side to `0`
  have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one k
    ((abs_norm r).trans_lt hr)).const_mul ((‖(1 : R)‖ + ‖c‖) ^ k)
  rw [mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [Filter.eventually_ge_atTop 1, eventually_norm_pow_le r] with n hn hrn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnc : ‖(n : R) + c‖ ≤ (‖(1 : R)‖ + ‖c‖) * n :=
    calc ‖(n : R) + c‖ ≤ n * ‖(1 : R)‖ + ‖c‖ := (norm_add_le _ _).trans (by
          gcongr; exact Nat.norm_cast_le n)
      _ ≤ (‖(1 : R)‖ + ‖c‖) * n := by nlinarith [norm_nonneg c]
  calc ‖((n : R) + c) ^ k * r ^ n‖ ≤ ‖(n : R) + c‖ ^ k * ‖r‖ ^ n :=
        (norm_mul_le _ _).trans <| mul_le_mul (norm_pow_le' _ hk) hrn (norm_nonneg _)
          (by positivity)
    _ ≤ ((‖(1 : R)‖ + ‖c‖) * n) ^ k * ‖r‖ ^ n := by gcongr
    _ = (‖(1 : R)‖ + ‖c‖) ^ k * (n ^ k * ‖r‖ ^ n) := by rw [mul_pow]; ring

/-- For any shift `c` and `r` with `‖r‖ < 1` in a normed ring with summable geometric series,
the shifted polynomial-geometric series `∑' n, (n + c) ^ k * r ^ n` is summable. -/
theorem summable_add_pow_mul_geometric_of_norm_lt_one {R : Type*} [NormedRing R]
    [HasSummableGeomSeries R] (c : R) (k : ℕ) {r : R} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ ↦ ((n : R) + c) ^ k * r ^ n) := by
  have hsum : Summable fun n : ℕ ↦
      ∑ i ∈ Finset.range (k + 1), (c ^ (k - i) * (k.choose i : R)) * ((n : R) ^ i * r ^ n) :=
    summable_sum fun i _ ↦ (summable_pow_mul_geometric_of_norm_lt_one i hr).mul_left _
  refine hsum.congr fun n ↦ ?_
  rw [(Nat.cast_commute n c).add_pow k, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← mul_assoc, ← Nat.cast_pow, (Nat.cast_commute (n ^ i) _).symm.eq, Nat.cast_pow,
    ← mul_assoc]

/-- Summability of `n * f n * r ^ n` and `f n * r ^ n` yields summability of
`(n + 1) * f n * r ^ (n + 1)`. -/
theorem summable_add_one_mul_pow_succ {R : Type*} [CommSemiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] {f : ℕ → R} {r : R}
    (hnf : Summable fun n : ℕ => (n : R) * f n * r ^ n)
    (hf : Summable fun n : ℕ => f n * r ^ n) :
    Summable fun n : ℕ => ((n : R) + 1) * f n * r ^ (n + 1) := by
  refine ((hnf.mul_left r).add (hf.mul_left r)).congr fun n => ?_
  rw [pow_succ r n]
  ring

/-- On the closed unit ball of a normed division ring, away from `1`, the partial sums of the
geometric series `∑ xⁱ` are bounded by `2 / ‖x - 1‖`. These are the bounded partial sums fed to
Dirichlet's test below on the unit circle. -/
theorem norm_geom_sum_le {D : Type*} [NormedDivisionRing D] {x : D} (hx : ‖x‖ ≤ 1)
    (hx1 : x ≠ 1) (n : ℕ) : ‖∑ i ∈ Finset.range n, x ^ i‖ ≤ 2 / ‖x - 1‖ := by
  rw [geom_sum_eq hx1, norm_div]
  gcongr
  calc ‖x ^ n - 1‖ ≤ ‖x ^ n‖ + ‖(1 : D)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by
      gcongr
      · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
      · simp
    _ = 2 := one_add_one_eq_two

/-- **Dirichlet's test** for coefficients of bounded variation. If `f n → 0`, the series of the
differences `‖f (n + 1) - f n‖` converges, and the partial sums of `z` are bounded, then the
partial sums of `∑ f n • z n` form a Cauchy sequence. Mathlib's
`Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` is the case of a monotone real `f`. -/
theorem _root_.Filter.Tendsto.cauchySeq_series_smul_of_summable_norm_sub {R E : Type*}
    [SeminormedRing R] [SeminormedAddCommGroup E] [Module R E] [IsBoundedSMul R E] {f : ℕ → R}
    {z : ℕ → E} {b : ℝ} (hf0 : Filter.Tendsto f Filter.atTop (nhds 0))
    (hvar : Summable fun n ↦ ‖f (n + 1) - f n‖) (hzb : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ b) :
    CauchySeq fun n ↦ ∑ i ∈ Finset.range n, f i • z i := by
  rw [← cauchySeq_shift 1]
  simp_rw [Finset.sum_range_by_parts _ _ (_ + 1), add_tsub_cancel_right, sub_eq_add_neg]
  refine CauchySeq.add (Filter.Tendsto.cauchySeq (x := 0) ?_) (CauchySeq.neg ?_)
  · have hzb' : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (norm ∘ fun n ↦ ∑ i ∈ Finset.range (n + 1), z i) :=
      Filter.isBoundedUnder_of ⟨b, fun n ↦ hzb (n + 1)⟩
    exact hf0.op_zero_isBoundedUnder_le hzb' (· • ·) norm_smul_le
  · refine cauchySeq_range_of_norm_bounded (g := fun i ↦ b * ‖f (i + 1) + -f i‖)
      (by simpa only [← sub_eq_add_neg] using (hvar.mul_left b).hasSum.tendsto_sum_nat.cauchySeq)
      fun i ↦ ?_
    rw [mul_comm]
    exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hzb _) (norm_nonneg _))

section SummationByParts

open Finset

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Abel's inequality** for a block of a series. If every partial sum `∑ k ∈ Icc 1 n, a k`
has norm at most `B`, and the real weights `w` are nonnegative and antitone beyond `K`, then
`‖∑ n ∈ Ioc K M, w n • a n‖ ≤ 2 * B * w (K + 1)` for every `M`. Mathlib's
`Finset.abs_sum_mul_le_mul_of_abs_sum_range_le` is the corresponding inequality in a linearly
ordered ring. -/
theorem norm_sum_Ioc_smul_le {a : ℕ → E} {w : ℕ → ℝ} {B : ℝ} {K : ℕ}
    (hw : AntitoneOn w (Set.Ioi K)) (hw₀ : ∀ n, K < n → 0 ≤ w n)
    (ha : ∀ n, ‖∑ k ∈ Icc 1 n, a k‖ ≤ B) (M : ℕ) :
    ‖∑ n ∈ Ioc K M, w n • a n‖ ≤ 2 * B * w (K + 1) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (ha 0)
  have hK : 0 ≤ w (K + 1) := hw₀ _ K.lt_succ_self
  rcases le_or_gt M K with hMK | hKM
  · rw [Ioc_eq_empty_of_le hMK, sum_empty, norm_zero]
    positivity
  -- Summation by parts against `a'`, which agrees with `a` off `0` and vanishes at `0`, so that
  -- its partial sums over `range (n + 1)` are the partial sums `∑ k ∈ Icc 1 n, a k`.
  set a' : ℕ → E := fun n ↦ if n = 0 then 0 else a n with ha'
  have hS (n : ℕ) : ∑ i ∈ range (n + 1), a' i = ∑ k ∈ Icc 1 n, a k := by
    induction n with
    | zero => simp [ha']
    | succ n ih => rw [sum_range_succ, ih, sum_Icc_succ_top (by omega)]; simp [ha']
  have hsum : ∑ n ∈ Ioc K M, w n • a n = ∑ n ∈ Ioc K M, w n • a' n :=
    sum_congr rfl fun n hn ↦ by
      have hn0 : n ≠ 0 := by simp only [mem_Ioc] at hn; omega
      simp [ha', hn0]
  rw [hsum, sum_Ioc_by_parts w a' hKM, hS, hS]
  -- The remaining terms are bounded by `B` times the telescoping variation of `w`.
  have hvar : ‖∑ i ∈ Ioc K (M - 1), (w (i + 1) - w i) • ∑ j ∈ range (i + 1), a' j‖ ≤
      B * (w (K + 1) - w M) := by
    have htel : ∑ i ∈ Ico (K + 1) M, (w i - w (i + 1)) = w (K + 1) - w M := by
      have := sum_Ico_sub w (show K + 1 ≤ M by omega)
      rw [sum_sub_distrib] at this ⊢
      linarith
    calc _ ≤ ∑ i ∈ Ioc K (M - 1), (w i - w (i + 1)) * B := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun i hi ↦ ?_)
          have hi' := mem_Ioc.mp hi
          have hmono : w (i + 1) ≤ w i :=
            hw (show K < i by omega) (show K < i + 1 by omega) (by omega)
          rw [norm_smul, hS, Real.norm_of_nonpos (sub_nonpos.mpr hmono), neg_sub]
          exact mul_le_mul_of_nonneg_left (ha i) (sub_nonneg.mpr hmono)
      _ = B * (w (K + 1) - w M) := by
          rw [← sum_mul, ← Ico_add_one_add_one_eq_Ioc, Nat.sub_add_cancel (by omega : 1 ≤ M),
            htel, mul_comm]
  have hM : 0 ≤ w M := hw₀ _ hKM
  calc _ ≤ w M * B + w (K + 1) * B + B * (w (K + 1) - w M) := by
        refine norm_sub_le_of_le (norm_sub_le_of_le ?_ ?_) hvar
        · rw [norm_smul, Real.norm_of_nonneg hM]
          exact mul_le_mul_of_nonneg_left (ha M) hM
        · rw [norm_smul, Real.norm_of_nonneg hK]
          exact mul_le_mul_of_nonneg_left (ha K) hK
    _ = 2 * B * w (K + 1) := by ring

/-- **The tail of a series with bounded partial sums.** If every partial sum
`∑ k ∈ Icc 1 n, a k` has norm at most `B`, the real weights `w` are nonnegative and antitone
beyond `K`, and the partial sums of `∑ w n • a n` converge to `L`, then the partial sum up to `K`
is within `2 * B * w (K + 1)` of `L`. -/
theorem norm_sub_sum_Icc_smul_le_of_tendsto {a : ℕ → E} {w : ℕ → ℝ} {B : ℝ} {K : ℕ}
    (hw : AntitoneOn w (Set.Ioi K)) (hw₀ : ∀ n, K < n → 0 ≤ w n)
    (ha : ∀ n, ‖∑ k ∈ Icc 1 n, a k‖ ≤ B) {L : E}
    (hL : Filter.Tendsto (fun M ↦ ∑ n ∈ Icc 1 M, w n • a n) Filter.atTop (nhds L)) :
    ‖L - ∑ n ∈ Icc 1 K, w n • a n‖ ≤ 2 * B * w (K + 1) := by
  refine le_of_tendsto ((hL.sub_const _).norm)
    (Filter.eventually_atTop.mpr ⟨K, fun M hKM ↦ ?_⟩)
  have hIcc (n : ℕ) : Icc 1 n = Ioc 0 n := Icc_add_one_left_eq_Ioc 0 n
  rw [hIcc, hIcc, ← sum_Ioc_consecutive _ (Nat.zero_le K) hKM, add_sub_cancel_left]
  exact norm_sum_Ioc_smul_le hw hw₀ ha M

end SummationByParts

variable {K : Type*} [NormedField K]

/-- The geometric series with coefficients `(k + 1)²` sums to `(1 + x) / (1 - x)³`. -/
theorem hasSum_succ_sq_mul_geometric_of_norm_lt_one {x : K} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ ↦ ((k : K) + 1) ^ 2 * x ^ k) ((1 + x) / (1 - x) ^ 3) := by
  have H := ((hasSum_sq_mul_geometric_of_norm_lt_one hx).add
    ((hasSum_coe_mul_geometric_of_norm_lt_one hx).mul_left 2)).add
    (hasSum_geometric_of_norm_lt_one hx)
  convert H using 1
  · ext k
    ring
  · have hne : 1 - x ≠ 0 := sub_ne_zero.mpr (fun h ↦ by
      have : x = 1 := h.symm
      simp only [this, norm_one, lt_self_iff_false] at hx)
    field_simp
    ring

/-- The geometric series with affine coefficients `a k + b` sums to
`(b + (a - b) x) / (1 - x)²`, in any normed division ring. -/
theorem hasSum_affine_mul_geometric_of_norm_lt_one {D : Type*} [NormedDivisionRing D] {x : D}
    (hx : ‖x‖ < 1) (a b : D) :
    HasSum (fun k : ℕ ↦ (a * k + b) * x ^ k) ((b + (a - b) * x) / (1 - x) ^ 2) := by
  have hx1 : 1 - x ≠ 0 := sub_ne_zero.2 fun h ↦ by simp [← h] at hx
  convert ((hasSum_coe_mul_geometric_of_norm_lt_one hx).mul_left a).add
    ((hasSum_geometric_of_norm_lt_one hx).mul_left b) using 1
  · ext k
    rw [add_mul, mul_assoc]
  · have hc : (1 - x) * ((1 - x) ^ 2)⁻¹ = (1 - x)⁻¹ := by
      rw [pow_two, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hx1, one_mul]
    rw [div_eq_mul_inv, div_eq_mul_inv, ← hc]
    noncomm_ring

/-- The geometric series with coefficient and exponent both shifted by one. -/
theorem tsum_natCast_succ_mul_pow_succ (r : K) (hr : ‖r‖ < 1) :
    (∑' d : ℕ, ((d + 1 : ℕ) : K) * r ^ (d + 1)) = r / (1 - r) ^ 2 := by
  calc
    _ = r * ∑' d : ℕ, (((d + 1).choose 1 : ℕ) : K) * r ^ d := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro d
      simp only [Nat.choose_one_right, pow_succ]
      ring
    _ = _ := by rw [tsum_choose_mul_geometric_of_norm_lt_one 1 hr]; ring

/-- The shifted geometric series weighted by `choose (d + 1) 2`. -/
theorem tsum_choose_two_mul_pow_succ (r : K) (hr : ‖r‖ < 1) :
    (∑' d : ℕ, (((d + 1).choose 2 : ℕ) : K) * r ^ (d + 1)) = r ^ 2 / (1 - r) ^ 3 := by
  have ht : Summable (fun d : ℕ ↦ (((d + 1 + 1).choose 2 : ℕ) : K) * r ^ (d + 1 + 1)) := by
    refine ((hasSum_choose_mul_geometric_of_norm_lt_one 2 hr).summable.mul_right (r ^ 2)).congr ?_
    intro d
    rw [Nat.add_assoc, pow_add]
    ring
  rw [tsum_eq_zero_add' (f := fun d : ℕ ↦ (((d + 1).choose 2 : ℕ) : K) * r ^ (d + 1)) ht]
  simp only [Nat.choose_eq_zero_of_lt (by decide : 1 < 2), Nat.cast_zero, zero_mul, zero_add]
  calc
    _ = r ^ 2 * ∑' d : ℕ, (((d + 2).choose 2 : ℕ) : K) * r ^ d := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro d
      rw [Nat.add_assoc, pow_add]
      ring
    _ = _ := by rw [tsum_choose_mul_geometric_of_norm_lt_one 2 hr]; ring

/-- The shifted geometric series weighted by `-choose (d + 2) 2`. -/
theorem tsum_neg_choose_two_mul_pow_succ (r : K) (hr : ‖r‖ < 1) :
    (∑' d : ℕ, -((((d + 1 + 1).choose 2 : ℕ) : K)) * r ^ (d + 1)) =
      -r / (1 - r) ^ 3 := by
  calc
    _ = -r * ∑' d : ℕ, (((d + 2).choose 2 : ℕ) : K) * r ^ d := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro d
      rw [Nat.add_assoc, pow_succ]
      ring
    _ = _ := by rw [tsum_choose_mul_geometric_of_norm_lt_one 2 hr]; ring

/-- The product of finitely many geometric series, indexed by all exponent vectors.
The index type may be empty. -/
theorem hasSum_prod_geometric_of_norm_lt_one {𝕜 ι : Type*} [NormedField 𝕜]
    [Fintype ι] {r : ι → 𝕜} (hr : ∀ i, ‖r i‖ < 1) :
    HasSum (fun α : ι → ℕ ↦ ∏ i, r i ^ α i) (∏ i, (1 - r i)⁻¹) :=
  hasSum_prod_of_summable_norm (fun i ↦ hasSum_geometric_of_norm_lt_one (hr i)) fun i ↦ by
    simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hr i)

/-- A finite product of shifted reciprocal kernels expands into geometric series whenever
in each coordinate the displacement has smaller norm than the denominator. -/
theorem hasSum_prod_geometric_div {𝕜 ι : Type*} [NormedField 𝕜] [Fintype ι]
    {z w : ι → 𝕜} (hw : ∀ i, ‖w i‖ < ‖z i‖) :
    HasSum (fun α : ι → ℕ ↦ ∏ i, (w i / z i) ^ α i / z i)
      (∏ i, (z i - w i)⁻¹) := by
  have hne (i) : z i ≠ 0 := norm_ne_zero_iff.mp
    ((norm_nonneg _).trans_lt (hw i)).ne'
  have hg := hasSum_prod_geometric_of_norm_lt_one (r := fun i ↦ w i / z i)
    (fun i ↦ by rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr (hne i))).mpr (hw i))
  have heq (i) : (1 - w i / z i)⁻¹ / z i = (z i - w i)⁻¹ := by
    field_simp [hne i]
  convert hg.mul_right (∏ i, (z i)⁻¹) using 1
  · ext α
    simp only [← Finset.prod_mul_distrib, div_eq_mul_inv]
  · simp only [← Finset.prod_mul_distrib, ← div_eq_mul_inv, heq]

/-- **Lambert series.** If `f(z) = ∑_{k ≥ 0} c(k) z^(k + 1)` on the open unit disc and
`∑ₖ ‖c(k)‖ ‖q w‖ᵏ` converges, then `∑_{n ≥ 1} f(qⁿw) = ∑_{k ≥ 1} c(k - 1) qᵏ wᵏ / (1 - qᵏ)`
for `‖q‖ < 1` and `‖q w‖ < 1`. -/
theorem _root_.Summable.hasSum_lambert [CompleteSpace K] {c : ℕ → K} {f : K → K} {q w : K}
    (hc : Summable fun k ↦ ‖c k‖ * ‖q * w‖ ^ k)
    (hf : ∀ z : K, ‖z‖ < 1 → HasSum (fun k ↦ c k * z ^ (k + 1)) (f z))
    (hq : ‖q‖ < 1) (hw : ‖q * w‖ < 1) :
    HasSum (fun k : ℕ ↦ c k * q ^ (k + 1) / (1 - q ^ (k + 1)) * w ^ (k + 1))
      (∑' n : ℕ, f (q ^ (n + 1) * w)) := by
  set F : ℕ × ℕ → K := fun p ↦ c p.2 * (q ^ (p.1 + 1) * w) ^ (p.2 + 1) with hF
  have hz (n : ℕ) : ‖q ^ (n + 1) * w‖ = ‖q‖ ^ n * ‖q * w‖ := by
    rw [pow_succ, mul_assoc, norm_mul, norm_pow]
  have hqn (n : ℕ) : ‖q‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hq.le
  have hbound (p : ℕ × ℕ) : ‖F p‖ ≤ ‖q‖ ^ p.1 * (‖c p.2‖ * ‖q * w‖ ^ (p.2 + 1)) := by
    rw [hF, norm_mul, norm_pow, hz, mul_pow, mul_left_comm]
    gcongr
    exact pow_le_of_le_one (by positivity) (hqn p.1) (Nat.succ_ne_zero _)
  have hc' : Summable fun k ↦ ‖c k‖ * ‖q * w‖ ^ (k + 1) := by
    simpa only [pow_succ, mul_assoc] using hc.mul_right ‖q * w‖
  have hs : Summable F :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_of_nonneg hc'
      (fun _ ↦ by positivity) (fun _ ↦ by positivity)) hbound
  have hrow (n : ℕ) : HasSum (fun k ↦ F (n, k)) (f (q ^ (n + 1) * w)) := by
    have hlt : ‖q ^ (n + 1) * w‖ < 1 := by
      rw [hz]
      calc ‖q‖ ^ n * ‖q * w‖ ≤ 1 * ‖q * w‖ := by gcongr; exact hqn n
        _ < 1 := by rwa [one_mul]
    exact hf _ hlt
  have hcol (k : ℕ) :
      HasSum (fun n ↦ F (n, k)) (c k * q ^ (k + 1) / (1 - q ^ (k + 1)) * w ^ (k + 1)) := by
    have hξ : ‖q ^ (k + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero _)
    convert (hasSum_geometric_of_norm_lt_one hξ).mul_left (c k * q ^ (k + 1) * w ^ (k + 1))
      using 1
    · funext n
      simp only [hF]
      ring
    · rw [div_eq_mul_inv]
      ring
  have h₁ := hs.hasSum.prod_fiberwise hrow
  have h₂ := ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hs.hasSum).prod_fiberwise fun k ↦ hcol k
  rwa [← h₁.tsum_eq] at h₂

/-- Natural-number coefficients bounded by `(k + m).choose m` have summable norms against the
powers of `0 ≤ r < 1`. -/
theorem summable_norm_natCast_mul_pow {a : ℕ → ℕ} (m : ℕ)
    (ha : ∀ k, a k ≤ (k + m).choose m) {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1) :
    Summable fun k ↦ ‖(a k : K)‖ * r ^ k := by
  refine (summable_choose_mul_geometric_of_norm_lt_one m (r := r)
    (by rwa [Real.norm_of_nonneg hr₀])).of_nonneg_of_le (fun _ ↦ by positivity) fun k ↦ ?_
  have h : ‖(a k : K)‖ ≤ a k := by simpa using Nat.norm_cast_le (α := K) (a k)
  gcongr
  exact h.trans (by exact_mod_cast ha k)

/-- The geometric weights `(1 - q) qᵏ` average an affine function of `k` to its value at the
mean `q / (1 - q)`: `∑ₖ (1 - q) qᵏ (c k + B) = c q / (1 - q) + B`, for `‖q‖ < 1`. -/
theorem hasSum_one_sub_mul_geometric_mul_affine {q : K} (hq : ‖q‖ < 1) (c B : K) :
    HasSum (fun k : ℕ ↦ (1 - q) * q ^ k * (c * k + B)) (c * q / (1 - q) + B) := by
  have hq1 : 1 - q ≠ 0 := sub_ne_zero.2 fun h ↦ by simp [← h] at hq
  convert (hasSum_affine_mul_geometric_of_norm_lt_one hq c B).mul_left (1 - q) using 1
  · ext k; ring
  · field_simp
    ring

/-- For `‖d‖ > 1` the shifted geometric series `∑ₘ C d⁻⁽ᵐ⁺¹⁾` sums to `C / (d - 1)`. -/
theorem hasSum_mul_inv_pow_succ_of_one_lt_norm {d : K} (hd : 1 < ‖d‖) (C : K) :
    HasSum (fun m : ℕ ↦ C * d⁻¹ ^ (m + 1)) (C / (d - 1)) := by
  have hd0 : d ≠ 0 := norm_pos_iff.mp (one_pos.trans hd)
  have hd1 : d - 1 ≠ 0 := sub_ne_zero.2 fun h ↦ by simp [h] at hd
  have hinv : ‖d⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hd
  convert (hasSum_geometric_of_norm_lt_one hinv).mul_left (C * d⁻¹) using 1
  · ext m
    ring
  · field_simp

variable [CompleteSpace K]

/-- The Lambert series `∑_{n ≥ 1} qⁿw / (1 - qⁿw)² = ∑_{k ≥ 1} k qᵏ wᵏ / (1 - qᵏ)`, for
`‖q w‖ < 1`. -/
theorem hasSum_lambert {q w : K} (hq : ‖q‖ < 1) (hw : ‖q * w‖ < 1) :
    HasSum (fun k : ℕ ↦ ((k + 1 : ℕ) : K) * q ^ (k + 1) / (1 - q ^ (k + 1)) * w ^ (k + 1))
      (∑' n : ℕ, q ^ (n + 1) * w / (1 - q ^ (n + 1) * w) ^ 2) := by
  refine Summable.hasSum_lambert (c := fun k ↦ ((k + 1 : ℕ) : K))
    (f := fun z ↦ z / (1 - z) ^ 2) (summable_norm_natCast_mul_pow (a := fun k ↦ k + 1) 1
      (fun k ↦ by simp) (norm_nonneg _) hw) (fun z hz ↦ ?_) hq hw
  simpa using (hasSum_nat_add_iff' (f := fun n : ℕ ↦ (n : K) * z ^ n) 1).mpr
    (hasSum_coe_mul_geometric_of_norm_lt_one hz)

/-- The Lambert series `∑_{n ≥ 1} (qⁿw)² / (1 - qⁿw)³ = ∑_{k ≥ 1} (k choose 2) qᵏ wᵏ / (1 - qᵏ)`,
for `‖q‖ < 1` and `‖q w‖ < 1`. -/
theorem hasSum_lambert_sq_div_pow_three {q w : K} (hq : ‖q‖ < 1) (hw : ‖q * w‖ < 1) :
    HasSum (fun k : ℕ ↦ ((k + 1).choose 2 : K) * q ^ (k + 1) / (1 - q ^ (k + 1)) * w ^ (k + 1))
      (∑' n : ℕ, (q ^ (n + 1) * w) ^ 2 / (1 - q ^ (n + 1) * w) ^ 3) := by
  refine Summable.hasSum_lambert (c := fun k ↦ ((k + 1).choose 2 : K))
    (f := fun z ↦ z ^ 2 / (1 - z) ^ 3) (summable_norm_natCast_mul_pow
      (a := fun k ↦ (k + 1).choose 2) 2 (fun k ↦ Nat.choose_le_choose 2 (by omega))
      (norm_nonneg _) hw) (fun z hz ↦ ?_) hq hw
  rw [← hasSum_nat_add_iff' 1]
  convert (hasSum_choose_mul_geometric_of_norm_lt_one 2 hz).mul_left (z ^ 2) using 1
  · funext k
    rw [show k + 1 + 1 = k + 2 by ring]
    ring
  · simp [div_eq_mul_inv]

/-- The Lambert series `∑_{n ≥ 1} qⁿw / (1 - qⁿw)³ = ∑_{k ≥ 1} (k + 1 choose 2) qᵏ wᵏ / (1 - qᵏ)`,
for `‖q‖ < 1` and `‖q w‖ < 1`. -/
theorem hasSum_lambert_div_pow_three {q w : K} (hq : ‖q‖ < 1) (hw : ‖q * w‖ < 1) :
    HasSum (fun k : ℕ ↦ ((k + 2).choose 2 : K) * q ^ (k + 1) / (1 - q ^ (k + 1)) * w ^ (k + 1))
      (∑' n : ℕ, q ^ (n + 1) * w / (1 - q ^ (n + 1) * w) ^ 3) := by
  refine Summable.hasSum_lambert (c := fun k ↦ ((k + 2).choose 2 : K))
    (f := fun z ↦ z / (1 - z) ^ 3) (summable_norm_natCast_mul_pow
      (a := fun k ↦ (k + 2).choose 2) 2 (fun _ ↦ le_rfl) (norm_nonneg _) hw) (fun z hz ↦ ?_) hq hw
  convert (hasSum_choose_mul_geometric_of_norm_lt_one 2 hz).mul_left z using 1
  · funext k
    ring
  · simp [div_eq_mul_inv]

end TauCeti

end

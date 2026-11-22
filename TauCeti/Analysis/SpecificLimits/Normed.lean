/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring
import TauCeti.Analysis.Normed.Ring.InfiniteSum

/-!
# Geometric series in seminormed rings and normed fields

The norms of the powers of an element in the open unit ball form a summable series, even when
the seminorm is not normalized. The same holds after multiplication by bounded coefficients.
Completeness then gives summability in the ring itself. In a complete seminormed group, a
sequence whose consecutive norms shrink by factors `C ρᵏ` with `ρ < 1` is summable, by the ratio
test; conversely, norm divergence of partial sums over `Ico N n` does not depend on the starting
index `N`, and if consecutive norms eventually expand by a factor `c > 2` (with infinitely many
terms of positive norm), each term dominates the sum of its predecessors and the partial sums
diverge in norm. In any normed ring with summable geometric series, shifted polynomial-geometric
series `∑ (n + c) ^ k * r ^ n` are summable whenever `‖r‖ < 1`.
**Dirichlet's test** holds for coefficients of bounded variation tending to zero: their
products with a sequence of bounded partial sums have Cauchy partial sums.

Over a normed field, the evaluations below specialize Mathlib's binomial geometric-series
formula to linear and quadratic coefficients, without requiring completeness or an ultrametric
norm; the affine case `∑ (a k + b) xᵏ` holds more generally in a normed division ring.
Finite products of geometric series converge unconditionally over all exponent vectors,
giving the product Cauchy kernel expansion. Over a complete normed field, the Lambert series
`∑_{n ≥ 1} f(qⁿw)` is the power series `∑_{k ≥ 1} c(k - 1) qᵏ wᵏ / (1 - qᵏ)` in `w` for every
power series `f(z) = ∑_{k ≥ 0} c(k) z^(k + 1)` whose coefficients grow slowly enough. This applies
to `z / (1 - z)²`, `z² / (1 - z)³` and `z / (1 - z)³`, whose coefficients are binomial.

The geometric weights `(1 - q) qᵏ` sum to `1` and have mean `q / (1 - q)`, so over a normed
field they average an affine function `c k + B` of `k` to `c q / (1 - q) + B`.

Dirichlet's test `Filter.Tendsto.cauchySeq_series_smul_of_summable_norm_sub` is adapted from the
lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Hypergeometric/AnalyticProperties.lean`, where it is
`exists_tendsto_sum_mul_of_bdd_variation`.
-/

public section

namespace TauCeti

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

/-- Divergence in norm of partial sums `∑ m ∈ Ico N n, T m` does not depend on the starting index
`N`. -/
theorem tendsto_norm_sum_Ico_atTop_iff {E : Type*} [SeminormedAddCommGroup E] {T : ℕ → E}
    (N M : ℕ) :
    Filter.Tendsto (fun n => ‖∑ m ∈ Finset.Ico N n, T m‖) Filter.atTop Filter.atTop ↔
      Filter.Tendsto (fun n => ‖∑ m ∈ Finset.Ico M n, T m‖) Filter.atTop Filter.atTop := by
  have hmp (N M : ℕ)
      (hN : Filter.Tendsto (fun n => ‖∑ m ∈ Finset.Ico N n, T m‖) Filter.atTop Filter.atTop) :
      Filter.Tendsto (fun n => ‖∑ m ∈ Finset.Ico M n, T m‖) Filter.atTop Filter.atTop := by
    let K := max N M
    let C := (∑ m ∈ Finset.Ico N K, T m) - ∑ m ∈ Finset.Ico M K, T m
    refine Filter.tendsto_atTop_mono' Filter.atTop ?_
      (Filter.tendsto_atTop_add_const_right Filter.atTop (-‖C‖) hN)
    filter_upwards [Filter.eventually_ge_atTop K] with n hn
    have hdiff : (∑ m ∈ Finset.Ico N n, T m) - C = ∑ m ∈ Finset.Ico M n, T m := by
      rw [← Finset.sum_Ico_consecutive T (le_max_left N M) hn,
        ← Finset.sum_Ico_consecutive T (le_max_right N M) hn]
      simp only [C]
      abel
    simpa only [← sub_eq_add_neg, hdiff] using norm_sub_norm_le (∑ m ∈ Finset.Ico N n, T m) C
  exact ⟨hmp N M, hmp M N⟩

/-- If consecutive terms of a sequence eventually expand in norm by a factor `c > 2` (so
`(c - 1)⁻¹ < 1` and each term dominates the sum of its predecessors) and infinitely many terms
have positive norm, then the partial sums `∑ m ∈ Ico N n, T m` diverge in norm for every `N`. -/
theorem tendsto_norm_sum_Ico_atTop_of_eventually_mul_norm_le {E : Type*}
    [SeminormedAddCommGroup E] {T : ℕ → E} {c : ℝ} (hc : 2 < c)
    (hgrow : ∀ᶠ m in Filter.atTop, c * ‖T m‖ ≤ ‖T (m + 1)‖)
    (hpos : ∃ᶠ m in Filter.atTop, 0 < ‖T m‖) (N : ℕ) :
    Filter.Tendsto (fun n => ‖∑ m ∈ Finset.Ico N n, T m‖) Filter.atTop Filter.atTop := by
  have hc1_pos : 0 < c - 1 := sub_pos.2 ((by norm_num : (1 : ℝ) < 2).trans hc)
  have hc2_pos : 0 < c - 2 := sub_pos.2 hc
  have hc_gt_one : 1 < c := (by norm_num : (1 : ℝ) < 2).trans hc
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hgrow
  obtain ⟨M, hMM₀, hTM_pos⟩ := Filter.frequently_atTop.1 hpos M₀
  rw [tendsto_norm_sum_Ico_atTop_iff N M]
  -- Each tail prefix `∑_{m = M}^{M + k - 1} T m` has norm at most `(c - 1)⁻¹ ‖T (M + k)‖`,
  -- while `‖T (M + k)‖` grows at least as `c ^ k ‖T M‖`.
  have hprefix (k : ℕ) :
      ‖∑ m ∈ Finset.Ico M (M + k), T m‖ ≤ (c - 1)⁻¹ * ‖T (M + k)‖ ∧
        c ^ k * ‖T M‖ ≤ ‖T (M + k)‖ := by
    induction k with
    | zero =>
      exact ⟨by simpa using mul_nonneg (inv_nonneg.2 hc1_pos.le) (norm_nonneg _), by simp⟩
    | succ k ih =>
      have hstep : c * ‖T (M + k)‖ ≤ ‖T (M + k + 1)‖ :=
        hM₀ (M + k) (hMM₀.trans (Nat.le_add_right M k))
      refine ⟨?_, ?_⟩
      · rw [← add_assoc, Finset.sum_Ico_succ_top (Nat.le_add_right M k)]
        calc ‖(∑ m ∈ Finset.Ico M (M + k), T m) + T (M + k)‖
            ≤ ‖∑ m ∈ Finset.Ico M (M + k), T m‖ + ‖T (M + k)‖ := norm_add_le _ _
          _ ≤ (c - 1)⁻¹ * ‖T (M + k)‖ + ‖T (M + k)‖ := by gcongr; exact ih.1
          _ = (c - 1)⁻¹ * (c * ‖T (M + k)‖) := by
              have : c - 1 ≠ 0 := hc1_pos.ne'
              field_simp
              ring
          _ ≤ (c - 1)⁻¹ * ‖T (M + k + 1)‖ :=
              mul_le_mul_of_nonneg_left hstep (inv_nonneg.2 hc1_pos.le)
      · rw [← add_assoc, pow_succ', mul_assoc]
        exact (mul_le_mul_of_nonneg_left ih.2 (zero_le_two.trans hc.le)).trans hstep
  have htail : Filter.Tendsto (fun k : ℕ => (c - 2) / (c - 1) * (c ^ k * ‖T M‖))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (div_pos hc2_pos hc1_pos) <|
      Filter.Tendsto.atTop_mul_const hTM_pos (tendsto_pow_atTop_atTop_of_one_lt hc_gt_one)
  rw [Filter.tendsto_atTop_atTop] at htail ⊢
  intro B
  obtain ⟨K, hK⟩ := htail B
  refine ⟨M + K + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = M + k + 1 := ⟨n - M - 1, by omega⟩
  calc B ≤ (c - 2) / (c - 1) * (c ^ k * ‖T M‖) := hK k (by omega)
    _ ≤ (c - 2) / (c - 1) * ‖T (M + k)‖ := by
          gcongr
          exact (hprefix k).2
    _ = ‖T (M + k)‖ - (c - 1)⁻¹ * ‖T (M + k)‖ := by
          have : c - 1 ≠ 0 := hc1_pos.ne'
          field_simp
          ring
    _ ≤ ‖T (M + k)‖ - ‖∑ m ∈ Finset.Ico M (M + k), T m‖ := by
          gcongr
          exact (hprefix k).1
    _ ≤ ‖∑ m ∈ Finset.Ico M (M + k + 1), T m‖ := by
          rw [Finset.sum_Ico_succ_top (Nat.le_add_right M k)]
          simpa [sub_neg_eq_add, add_comm] using
            norm_sub_norm_le (T (M + k)) (-(∑ m ∈ Finset.Ico M (M + k), T m))

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
  · refine squeeze_zero_norm (fun n ↦ (norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_left (hzb (n + 1)) (norm_nonneg _))) ?_
    simpa using (tendsto_norm_zero.comp hf0).mul_const b
  · refine cauchySeq_range_of_norm_bounded (g := fun i ↦ b * ‖f (i + 1) + -f i‖)
      (by simpa only [← sub_eq_add_neg] using (hvar.mul_left b).hasSum.tendsto_sum_nat.cauchySeq)
      fun i ↦ ?_
    rw [mul_comm]
    exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hzb _) (norm_nonneg _))

/-- A sequence in a seminormed group whose norms are eventually bounded by `(n : ℝ)⁻¹` converges
to `0`. -/
theorem tendsto_zero_of_eventually_norm_le_inv {E : Type*} [SeminormedAddCommGroup E]
    {g : ℕ → E} (hg : ∀ᶠ n in Filter.atTop, ‖g n‖ ≤ (n : ℝ)⁻¹) :
    Filter.Tendsto g Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) hg
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)

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

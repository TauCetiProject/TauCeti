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
test.

Over a normed field, the evaluations below specialize Mathlib's binomial geometric-series
formula to linear and quadratic coefficients, without requiring completeness or an ultrametric
norm. Finite products of geometric series converge unconditionally over all exponent vectors,
giving the product Cauchy kernel expansion. Over a complete normed field, the Lambert series
`∑_{n ≥ 1} f(qⁿw)` is the power series `∑_{k ≥ 1} c(k - 1) qᵏ wᵏ / (1 - qᵏ)` in `w` for every
power series `f(z) = ∑_{k ≥ 0} c(k) z^(k + 1)` whose coefficients grow slowly enough. This applies
to `z / (1 - z)²`, `z² / (1 - z)³` and `z / (1 - z)³`, whose coefficients are binomial.

The geometric weights `(1 - q) qᵏ` sum to `1` and have mean `q / (1 - q)`, so over a normed
field they average an affine function `c k + B` of `k` to `c q / (1 - q) + B`.
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

/-- A sequence whose consecutive norms shrink by a factor `C ρᵏ` with `ρ < 1` is summable. -/
theorem summable_of_norm_succ_le_mul_pow {E : Type*} [SeminormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → E} {C ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ : ρ < 1) (h : ∀ k, ‖f (k + 1)‖ ≤ C * ρ ^ k * ‖f k‖) :
    Summable f := by
  have ht : Filter.Tendsto (fun k : ℕ ↦ C * ρ ^ k) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ₀ hρ).const_mul C
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  filter_upwards [(tendsto_order.1 ht).2 (1 / 2) (by norm_num)] with k hk
  exact (h k).trans (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _))

variable {K : Type*} [NormedField K]

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
  convert ((hasSum_coe_mul_geometric_of_norm_lt_one hq).mul_left ((1 - q) * c)).add
    ((hasSum_geometric_of_norm_lt_one hq).mul_left ((1 - q) * B)) using 1
  · ext k; ring
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

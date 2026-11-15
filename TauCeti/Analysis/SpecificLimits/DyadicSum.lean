/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sums over dyadic scales

For a base `b > 1` and an exponent `δ > 0`, the sum of `min (b ^ j u) ((b ^ j u) ^ (-δ))` over
any finite set of integers `j` is at most `(1 - b⁻¹)⁻¹ + (1 - b ^ (-δ))⁻¹`, for every real `u`.
For `u > 0`, the terms with `b ^ j u ≤ 1` are at most `b ^ j u`, a geometric series of ratio
`b⁻¹` whose largest term is at most `1`, and the terms with `b ^ j u > 1` are `(b ^ j u) ^ (-δ)`,
a geometric series of ratio `b ^ (-δ)` whose largest term is below `1`. For `u ≤ 0` every term is
nonpositive.

With `b = 2` this is how per-scale estimates of the shape "at most `2 ^ j ‖h‖` for small scales and
at most `(2 ^ j ‖h‖) ^ (-δ)` for large ones" are summed into a bound uniform in `h`, as in the
verification of Hörmander's condition for the kernel of a Fourier multiplier cut into
Littlewood–Paley pieces.

Similarly, for `0 < α < 1`, a nonnegative sequence with `2^{jα} gⱼ ≤ a` and `2^{jα} gⱼ ≤ b 2^j d`
sums to at most `C (a + b) d^α`: the second bound is the better one while `2^j d ≤ 1`, and the
first beyond. Applied to the increments `gⱼ = |fⱼ(x) - fⱼ(y)|` at distance `d = |x - y|` of
pieces with `‖fⱼ‖_∞ ≲ 2^{-jα}` and Lipschitz constants `≲ 2^{j(1-α)}`, this shows that `∑ⱼ fⱼ` is
`α`-Hölder.

## Main declarations

* `TauCeti.sum_min_zpow_mul_rpow_neg_le`: the uniform bound over any finite set of scales.
* `TauCeti.exists_tsum_le_mul_rpow_of_rpow_mul_le`: for `0 < α < 1`, a nonnegative sequence with
  `2^{jα} gⱼ ≤ a` and `2^{jα} gⱼ ≤ b 2^j d` sums to at most `C (a + b) d^α`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., proof of Theorem 6.2.7.
-/

public section

namespace TauCeti

open Finset

/-- For `b > 1` and `δ > 0`, summing `min (b ^ j u) ((b ^ j u) ^ (-δ))` over any finite set of
integers `j` gives at most `(1 - b⁻¹)⁻¹ + (1 - b ^ (-δ))⁻¹`, independently of `u`. For `b = 2` the
first summand is `2`. -/
theorem sum_min_zpow_mul_rpow_neg_le {b δ : ℝ} (hb : 1 < b) (hδ : 0 < δ) (u : ℝ) (s : Finset ℤ) :
    ∑ j ∈ s, min (b ^ j * u) ((b ^ j * u) ^ (-δ)) ≤ (1 - b⁻¹)⁻¹ + (1 - b ^ (-δ))⁻¹ := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hb1 : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
  set q : ℝ := b ^ (-δ)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  -- For `u ≤ 0` every term is nonpositive.
  obtain hu | hu := le_or_gt u 0
  · exact (sum_nonpos fun j _ ↦ (min_le_left _ _).trans
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hu)).trans
      (add_nonneg (inv_nonneg.2 (sub_nonneg.2 hb1.le)) (inv_nonneg.2 (sub_nonneg.2 hq1.le)))
  obtain ⟨m, hlo, hhi⟩ := exists_mem_Ico_zpow hu hb
  -- The comparison function on `ℤ`: `b ^ (i + 1)` for `i < 0` and `q ^ i` for `i ≥ 0`.
  set f : ℤ → ℝ := fun i ↦ if i < 0 then b ^ (i + 1) else q ^ i
  have hf : HasSum f ((1 - q)⁻¹ + (1 - b⁻¹)⁻¹) := by
    refine HasSum.of_nat_of_neg_add_one ?_ ?_
    · convert hasSum_geometric_of_lt_one hq0 hq1 using 2 with n
      simp [f]
    · convert hasSum_geometric_of_lt_one (inv_nonneg.2 hb0.le) hb1 using 2 with n
      have hn : (-((n : ℤ) + 1)) < 0 := by omega
      simp only [f, hn, ite_true]
      rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring, zpow_neg, zpow_natCast, inv_pow]
  -- Since `b ^ m ≤ u < b ^ (m + 1)`, the term of index `j` is at most `f (j + m)`.
  have hterm (j : ℤ) : min (b ^ j * u) ((b ^ j * u) ^ (-δ)) ≤ f (j + m) := by
    by_cases hj : j + m < 0
    · simp only [f, hj, ite_true]
      refine (min_le_left _ _).trans ?_
      rw [add_assoc, zpow_add₀ hb0.ne']
      gcongr
    · simp only [f, hj, ite_false]
      refine (min_le_right _ _).trans ?_
      rw [Real.rpow_zpow_comm hb0.le, zpow_add₀ hb0.ne']
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by gcongr) (by linarith)
  calc ∑ j ∈ s, min (b ^ j * u) ((b ^ j * u) ^ (-δ)) ≤ ∑ j ∈ s, f (j + m) :=
        sum_le_sum fun j _ ↦ hterm j
    _ = ∑ i ∈ s.map (addRightEmbedding m), f i := by simp
    _ ≤ (1 - q)⁻¹ + (1 - b⁻¹)⁻¹ := sum_le_hasSum _ (fun i _ ↦ by positivity) hf
    _ = (1 - b⁻¹)⁻¹ + (1 - q)⁻¹ := add_comm _ _

/-- **Summing two dyadic bounds.** For `0 < α < 1` there is `C ≥ 0` such that every nonnegative
sequence with `2^{jα} gⱼ ≤ a` and `2^{jα} gⱼ ≤ b 2^j d` for all `j`, where `a, b, d ≥ 0`, is
summable with `∑ⱼ gⱼ ≤ C (a + b) d^α`. -/
theorem exists_tsum_le_mul_rpow_of_rpow_mul_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℕ → ℝ) {a b d : ℝ}, 0 ≤ a → 0 ≤ b → 0 ≤ d → (∀ j, 0 ≤ g j) →
      (∀ j : ℕ, 2 ^ (α * j) * g j ≤ a) → (∀ j : ℕ, 2 ^ (α * j) * g j ≤ b * 2 ^ j * d) →
      Summable g ∧ ∑' j, g j ≤ C * (a + b) * d ^ α := by
  -- The ratios `q = 2^{-α} < 1` of the first bounds and `2 q = 2^{1-α} > 1` of the second.
  set q : ℝ := ((2 : ℝ) ^ α)⁻¹ with hq_def
  have h2α : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow one_lt_two hα0
  have h2α' : (2 : ℝ) ^ α < 2 := by simpa using Real.rpow_lt_rpow_of_exponent_lt one_lt_two hα1
  have hq0 : 0 < q := inv_pos.2 (by positivity)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ h2α
  have h2q : 1 < 2 * q := by
    rw [hq_def, ← div_eq_mul_inv, one_lt_div (by positivity)]
    exact h2α'
  have hpow : ∀ j : ℕ, (2 : ℝ) ^ (α * j) = (q ^ j)⁻¹ := fun j ↦ by
    rw [hq_def, inv_pow, inv_inv, Real.rpow_mul_natCast zero_le_two]
  set C₁ : ℝ := (1 - q)⁻¹
  set C₂ : ℝ := 2 * q * (2 * q - 1)⁻¹
  have hC₁ : 0 ≤ C₁ := by have := sub_pos.2 hq1; positivity
  have hC₂ : 0 ≤ C₂ := by have := sub_pos.2 h2q; positivity
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun g a b d ha0 hb0 hd0 hg0 ha hb ↦ ?_⟩
  have hga : ∀ j, g j ≤ a * q ^ j := fun j ↦ by
    have h := ha j
    rw [hpow, inv_mul_le_iff₀ (by positivity)] at h
    linarith
  have hgb : ∀ j, g j ≤ b * d * (2 * q) ^ j := fun j ↦ by
    have h := hb j
    rw [hpow, inv_mul_le_iff₀ (by positivity)] at h
    calc g j ≤ q ^ j * (b * 2 ^ j * d) := h
      _ = b * d * (2 * q) ^ j := by ring
  have hgeo := summable_geometric_of_lt_one hq0.le hq1
  have hgs : Summable g := Summable.of_nonneg_of_le hg0 hga (hgeo.mul_left a)
  refine ⟨hgs, ?_⟩
  rcases le_or_gt 1 d with hd | hd
  · -- For `d ≥ 1` the first bounds suffice.
    calc ∑' j, g j ≤ ∑' j, a * q ^ j := hgs.tsum_le_tsum hga (hgeo.mul_left a)
      _ = a * C₁ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
      _ ≤ (C₁ + C₂) * (a + b) * 1 := by nlinarith
      _ ≤ (C₁ + C₂) * (a + b) * d ^ α := by
          gcongr
          exact Real.one_le_rpow hd hα0.le
  rcases hd0.eq_or_lt with hd0 | hd0
  · -- For `d = 0` the second bounds vanish.
    have hg : ∀ j, g j = 0 := fun j ↦ le_antisymm ((hgb j).trans_eq (by simp [← hd0])) (hg0 j)
    simp only [hg, tsum_zero]
    positivity
  -- For `0 < d < 1` split the sum at the scale `J` with `1 < 2^J d ≤ 2`: the second bounds sum
  -- to `b C₂ d^α` below it, and the first bounds to `a C₁ d^α` above it.
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (one_le_inv₀ hd0 |>.2 hd.le) one_lt_two
  set J := n + 1
  set t := (2 : ℝ) ^ J * d
  have ht1 : 1 < t := by
    have h := mul_lt_mul_of_pos_right hn2 hd0
    rwa [inv_mul_cancel₀ hd0.ne'] at h
  have ht2 : t ≤ 2 := by
    have h := mul_le_mul_of_nonneg_right hn1 hd0.le
    rw [inv_mul_cancel₀ hd0.ne'] at h
    calc t = 2 * (2 ^ n * d) := by simp only [t, J, pow_succ]; ring
      _ ≤ 2 := by linarith
  -- `q^J t^α = d^α`, since `t = 2^J d`.
  have hqJ : q ^ J * t ^ α = d ^ α := by
    have h2J : ((2 : ℝ) ^ J) ^ α = ((2 : ℝ) ^ α) ^ J := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, mul_comm, Real.rpow_mul zero_le_two,
        Real.rpow_natCast]
    rw [Real.mul_rpow (by positivity) hd0.le, h2J, hq_def, inv_pow, ← mul_assoc,
      inv_mul_cancel₀ (by positivity), one_mul]
  have hqd : q ^ J ≤ d ^ α := by
    rw [← hqJ]
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow ht1.le hα0.le)
  have hdq : d * (2 * q) ^ J ≤ 2 * q * d ^ α := by
    have ht : t ^ (1 - α) * t ^ α = t := by
      rw [← Real.rpow_add (by positivity), sub_add_cancel, Real.rpow_one]
    have h2 : (2 : ℝ) ^ (1 - α) = 2 * q := by
      rw [Real.rpow_sub two_pos, Real.rpow_one, hq_def, div_eq_mul_inv]
    calc d * (2 * q) ^ J = t ^ (1 - α) * (q ^ J * t ^ α) := by
          rw [← mul_assoc, mul_comm _ (q ^ J), mul_assoc, ht]
          simp only [t]
          ring
      _ ≤ 2 ^ (1 - α) * d ^ α := by
          rw [hqJ]
          gcongr
      _ = 2 * q * d ^ α := by rw [h2]
  have hlow : ∑ j ∈ range J, g j ≤ b * C₂ * d ^ α := by
    have := sub_pos.2 h2q
    calc ∑ j ∈ range J, g j ≤ ∑ j ∈ range J, b * d * (2 * q) ^ j := sum_le_sum fun j _ ↦ hgb j
      _ = b * d * (((2 * q) ^ J - 1) / (2 * q - 1)) := by rw [← mul_sum, geom_sum_eq h2q.ne']
      _ ≤ b * (d * (2 * q) ^ J) * (2 * q - 1)⁻¹ := by
          rw [div_eq_mul_inv, ← mul_assoc, mul_assoc b]
          gcongr
          linarith
      _ ≤ b * (2 * q * d ^ α) * (2 * q - 1)⁻¹ := by gcongr
      _ = b * C₂ * d ^ α := by ring
  have hhigh : ∑' j, g (j + J) ≤ a * C₁ * d ^ α := by
    calc ∑' j, g (j + J) ≤ ∑' j, a * q ^ J * q ^ j :=
          ((summable_nat_add_iff J).2 hgs).tsum_le_tsum
            (fun j ↦ (hga (j + J)).trans_eq (by ring)) (hgeo.mul_left _)
      _ = a * C₁ * q ^ J := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
          ring
      _ ≤ a * C₁ * d ^ α := by gcongr
  rw [← hgs.sum_add_tsum_nat_add J]
  have : 0 ≤ d ^ α := by positivity
  nlinarith [mul_nonneg ha0 hC₂, mul_nonneg hb0 hC₁]

end TauCeti

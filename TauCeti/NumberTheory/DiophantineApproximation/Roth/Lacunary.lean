/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Roth.Theorem

/-!
# Transcendence of lacunary series `∑ b ^ (-r ^ k)`

Let `b ≥ 2` and `r ≥ 2` be natural numbers and let `x = ∑_{k ≥ 1} b ^ (-r ^ k)`. The partial sum
`x_n` of the first `n` terms is a rational number with denominator `q = b ^ (r ^ n)`, and the
remaining tail is positive and at most `2 b ^ (-r ^ (n + 1)) = 2 / q ^ r`. Hence `x` is a Liouville
number with exponent `r`. For `r ≥ 3` Roth's theorem (`IsAlgebraic.not_liouvilleWith`) rules out
algebraic `x`, so `x` is transcendental. The case `r = 3` is Evertse's Exercise 6.5.

## Main results

* `TauCeti.liouvilleWith_tsum_inv_pow_pow`: for `b, r ≥ 2`, `∑_{k ≥ 1} b ^ (-r ^ k)` is a Liouville
  number with exponent `r`.
* `TauCeti.transcendental_tsum_inv_pow_pow`: for `b ≥ 2` and `r ≥ 3`, `∑_{k ≥ 1} b ^ (-r ^ k)` is
  transcendental.
* `TauCeti.transcendental_tsum_inv_pow_three_pow`: the case `r = 3`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, Exercise 6.5.
-/

public section

open Filter

namespace TauCeti

/-- For natural numbers `b ≥ 2` and `r ≥ 2`, the lacunary series `∑_{k ≥ 1} b ^ (-r ^ k)` is a
Liouville number with exponent `r`: its partial sums have denominators `q = b ^ (r ^ n)` and
approximate it to within `2 / q ^ r`. -/
theorem liouvilleWith_tsum_inv_pow_pow {b r : ℕ} (hb : 2 ≤ b) (hr : 2 ≤ r) :
    LiouvilleWith r (∑' k : ℕ, ((b : ℝ) ^ r ^ (k + 1))⁻¹) := by
  set f : ℕ → ℝ := fun k ↦ ((b : ℝ) ^ r ^ (k + 1))⁻¹ with hf
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hr1 : 1 ≤ r := by omega
  -- `f k ≤ b⁻¹ ^ k`, which gives summability.
  have hfle : ∀ k, f k ≤ ((b : ℝ)⁻¹) ^ k := fun k ↦ by
    rw [hf, inv_pow]
    refine inv_anti₀ (by positivity) (pow_le_pow_right₀ hb1.le ?_)
    exact (Nat.lt_pow_self (by omega)).le.trans (Nat.pow_le_pow_right hr1 k.le_succ)
  have hsum : Summable f :=
    (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)).of_nonneg_of_le
      (fun k ↦ by positivity) hfle
  -- The denominators `b ^ (r ^ n)` tend to infinity.
  have hmono : StrictMono fun n : ℕ ↦ b ^ r ^ n := fun m n hmn ↦
    Nat.pow_lt_pow_right hb (Nat.pow_lt_pow_right hr hmn)
  refine ⟨3, hmono.tendsto_atTop.frequently_map _ (fun n h ↦ h)
    (Filter.Frequently.of_forall fun n ↦ ?_)⟩
  -- Write the partial sum of the first `n` terms over the denominator `q = b ^ (r ^ n)`.
  set q : ℕ := b ^ r ^ n with hq
  have hq0 : (0 : ℝ) < q := by rw [hq]; push_cast; positivity
  refine ⟨∑ k ∈ Finset.range n, (b : ℤ) ^ (r ^ n - r ^ (k + 1)), ?_⟩
  have hpartial : ((∑ k ∈ Finset.range n, (b : ℤ) ^ (r ^ n - r ^ (k + 1)) : ℤ) : ℝ) / q =
      ∑ k ∈ Finset.range n, f k := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hle : r ^ (k + 1) ≤ r ^ n :=
      Nat.pow_le_pow_right hr1 (Finset.mem_range.1 hk)
    rw [hf, hq]
    push_cast
    rw [div_eq_iff (by positivity), eq_inv_mul_iff_mul_eq₀ (by positivity), ← pow_add,
      Nat.add_sub_cancel' hle]
  -- The tail `∑_k f (k + n)` is positive and at most `2 / q ^ r`.
  have htail : ∑' k : ℕ, f k - ∑ k ∈ Finset.range n, f k = ∑' k : ℕ, f (k + n) := by
    rw [← hsum.sum_add_tsum_nat_add n]; ring
  have hpos : 0 < ∑' k : ℕ, f (k + n) :=
    ((summable_nat_add_iff n).2 hsum).tsum_pos (fun k ↦ by positivity) 0 (by positivity)
  have hle : ∑' k : ℕ, f (k + n) ≤ 2 / (q : ℝ) ^ (r : ℝ) := by
    -- `f (k + n) ≤ (q ^ r)⁻¹ * b⁻¹ ^ k`, since `r ^ (k + n + 1) ≥ r ^ (n + 1) + k`.
    have hterm : ∀ k, f (k + n) ≤ ((q : ℝ) ^ r)⁻¹ * ((b : ℝ)⁻¹) ^ k := fun k ↦ by
      rw [hf, hq, inv_pow, ← mul_inv, Nat.cast_pow, ← pow_mul, ← pow_succ, ← pow_add]
      refine inv_anti₀ (by positivity) (pow_le_pow_right₀ hb1.le ?_)
      have h1 : 1 ≤ r ^ (n + 1) := Nat.one_le_pow _ _ (by omega)
      calc r ^ (n + 1) + k ≤ r ^ (n + 1) * (k + 1) := by nlinarith
        _ ≤ r ^ (n + 1) * r ^ k := Nat.mul_le_mul_left _ (Nat.lt_pow_self (by omega))
        _ = r ^ (k + n + 1) := by ring
    have hgeom : ∑' k : ℕ, ((b : ℝ)⁻¹) ^ k ≤ 2 := by
      rw [tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)]
      have : (b : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) (by exact_mod_cast hb)
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc ∑' k : ℕ, f (k + n) ≤ ∑' k : ℕ, ((q : ℝ) ^ r)⁻¹ * ((b : ℝ)⁻¹) ^ k :=
          ((summable_nat_add_iff n).2 hsum).tsum_le_tsum hterm
            ((summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)).mul_left _)
      _ = ((q : ℝ) ^ r)⁻¹ * ∑' k : ℕ, ((b : ℝ)⁻¹) ^ k := tsum_mul_left
      _ ≤ ((q : ℝ) ^ r)⁻¹ * 2 := by gcongr
      _ = 2 / (q : ℝ) ^ (r : ℝ) := by rw [Real.rpow_natCast]; ring
  have hlt : ∑' k : ℕ, f (k + n) < 3 / (q : ℝ) ^ (r : ℝ) :=
    hle.trans_lt (div_lt_div_of_pos_right (by norm_num) (by positivity))
  rw [hpartial]
  refine ⟨fun h ↦ hpos.ne' (by rw [← htail, h, sub_self]), ?_⟩
  rw [htail, abs_of_pos hpos]
  exact hlt

/-- **Transcendence of lacunary series.** For natural numbers `b ≥ 2` and `r ≥ 3`, the number
`∑_{k ≥ 1} b ^ (-r ^ k)` is transcendental. It is a Liouville number with exponent `r > 2`
(`TauCeti.liouvilleWith_tsum_inv_pow_pow`), which Roth's theorem excludes for algebraic numbers. -/
theorem transcendental_tsum_inv_pow_pow {b r : ℕ} (hb : 2 ≤ b) (hr : 3 ≤ r) :
    Transcendental ℚ (∑' k : ℕ, ((b : ℝ) ^ r ^ (k + 1))⁻¹) := fun h ↦
  h.not_liouvilleWith (by exact_mod_cast hr) (liouvilleWith_tsum_inv_pow_pow hb (by omega))

/-- **Evertse, Exercise 6.5.** For every natural number `b ≥ 2`, the number
`∑_{k ≥ 1} b ^ (-3 ^ k)` is transcendental. -/
theorem transcendental_tsum_inv_pow_three_pow {b : ℕ} (hb : 2 ≤ b) :
    Transcendental ℚ (∑' k : ℕ, ((b : ℝ) ^ 3 ^ (k + 1))⁻¹) := by
  exact_mod_cast transcendental_tsum_inv_pow_pow hb le_rfl

end TauCeti

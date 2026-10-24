/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

/-!
# The lacunary series `∑ b ^ (-r ^ k)` is a Liouville number

Let `b ≥ 2` and `r ≥ 2` be natural numbers and let `x = ∑_{k ≥ 1} b ^ (-r ^ k)`. The partial sum
`x_n` of the first `n` terms is a rational number with denominator `q = b ^ (r ^ n)`, and the
remaining tail is positive and at most `2 b ^ (-r ^ (n + 1)) = 2 / q ^ r`. Hence `x` is a Liouville
number with exponent `r` (`TauCeti.liouvilleWith_tsum_inv_pow_pow`). Roth's theorem then makes `x`
transcendental for `r ≥ 3`; see
`TauCeti.NumberTheory.DiophantineApproximation.Roth.Lacunary`.

## Main results

* `TauCeti.partial_sum_inv_pow_pow_eq`: the `n`-th partial sum is an integer over the
  denominator `q = b ^ (r ^ n)`.
* `TauCeti.tsum_inv_pow_pow_tail_le`: the tail after `n` terms is at most `2 / q ^ r`.
* `TauCeti.liouvilleWith_tsum_inv_pow_pow`: for `b, r ≥ 2`, `∑_{k ≥ 1} b ^ (-r ^ k)` is a Liouville
  number with exponent `r`.
-/

public section

open Filter

namespace TauCeti

section Lacunary

variable {b r : ℕ}

/-- The lacunary series is summable, by comparison with the geometric series: the exponents
`r ^ (k + 1)` grow at least linearly (`summable_one_div_pow_of_le`). -/
private lemma summable_inv_pow_pow (hb : 2 ≤ b) (hr : 2 ≤ r) :
    Summable fun k : ℕ ↦ ((b : ℝ) ^ r ^ (k + 1))⁻¹ := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  simpa [one_div] using summable_one_div_pow_of_le hb1 fun k ↦
    (Nat.lt_pow_self (by omega)).le.trans (Nat.pow_le_pow_right (by omega) k.le_succ)

/-- The partial sum of the first `n` terms of the lacunary series, written as an integer over the
denominator `q = b ^ (r ^ n)`. -/
lemma partial_sum_inv_pow_pow_eq (hb : 0 < b) (n : ℕ) :
    ((∑ k ∈ Finset.range n, (b : ℤ) ^ (r ^ n - r ^ (k + 1)) : ℤ) : ℝ) / (b : ℝ) ^ r ^ n =
      ∑ k ∈ Finset.range n, ((b : ℝ) ^ r ^ (k + 1))⁻¹ := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hle : r ^ (k + 1) ≤ r ^ n := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · exact Nat.pow_le_pow_right hr (Finset.mem_range.1 hk)
  rw [div_eq_iff (by positivity), eq_inv_mul_iff_mul_eq₀ (by positivity), ← pow_add,
    Nat.add_sub_cancel' hle]

/-- **Tail estimate.** The tail of the lacunary series after `n` terms is at most
`2 / q ^ r`, where `q = b ^ (r ^ n)` is the denominator of the `n`-th partial sum. -/
lemma tsum_inv_pow_pow_tail_le (hb : 2 ≤ b) (hr : 2 ≤ r) (n : ℕ) :
    ∑' k : ℕ, ((b : ℝ) ^ r ^ (k + n + 1))⁻¹ ≤ 2 / ((b : ℝ) ^ r ^ n) ^ r := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  -- Each tail term is at most `(q ^ r)⁻¹ * b⁻¹ ^ k`, since `r ^ (k + n + 1) ≥ r ^ (n + 1) + k`.
  have hterm : ∀ k, ((b : ℝ) ^ r ^ (k + n + 1))⁻¹ ≤ (((b : ℝ) ^ r ^ n) ^ r)⁻¹ * ((b : ℝ)⁻¹) ^ k :=
    fun k ↦ by
      rw [inv_pow, ← mul_inv, ← pow_mul, ← pow_succ, ← pow_add]
      refine inv_anti₀ (by positivity) (pow_le_pow_right₀ hb1.le ?_)
      have h1 : 1 ≤ r ^ (n + 1) := Nat.one_le_pow _ _ (by omega)
      calc r ^ (n + 1) + k ≤ r ^ (n + 1) * (k + 1) := by nlinarith
        _ ≤ r ^ (n + 1) * r ^ k := Nat.mul_le_mul_left _ (Nat.lt_pow_self (by omega))
        _ = r ^ (k + n + 1) := by ring
  -- The geometric series `∑ b⁻¹ ^ k` sums to at most `2` because `b ≥ 2`.
  have hgeom : ∑' k : ℕ, ((b : ℝ)⁻¹) ^ k ≤ 2 := by
    rw [tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1)]
    have : (b : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) (by exact_mod_cast hb)
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc ∑' k : ℕ, ((b : ℝ) ^ r ^ (k + n + 1))⁻¹
      ≤ ∑' k : ℕ, (((b : ℝ) ^ r ^ n) ^ r)⁻¹ * ((b : ℝ)⁻¹) ^ k := by
        refine Summable.tsum_le_tsum hterm ?_ ?_
        · simpa using (summable_nat_add_iff n).2 (summable_inv_pow_pow hb hr)
        · exact (summable_geometric_of_lt_one (by positivity)
            (inv_lt_one_of_one_lt₀ hb1)).mul_left _
    _ = (((b : ℝ) ^ r ^ n) ^ r)⁻¹ * ∑' k : ℕ, ((b : ℝ)⁻¹) ^ k := tsum_mul_left
    _ ≤ (((b : ℝ) ^ r ^ n) ^ r)⁻¹ * 2 := by gcongr
    _ = 2 / ((b : ℝ) ^ r ^ n) ^ r := by ring

/-- For natural numbers `b ≥ 2` and `r ≥ 2`, the lacunary series `∑_{k ≥ 1} b ^ (-r ^ k)` is a
Liouville number with exponent `r`: its partial sums have denominators `q = b ^ (r ^ n)` and
approximate it to within `2 / q ^ r` (`TauCeti.tsum_inv_pow_pow_tail_le`). -/
theorem liouvilleWith_tsum_inv_pow_pow (hb : 2 ≤ b) (hr : 2 ≤ r) :
    LiouvilleWith r (∑' k : ℕ, ((b : ℝ) ^ r ^ (k + 1))⁻¹) := by
  set f : ℕ → ℝ := fun k ↦ ((b : ℝ) ^ r ^ (k + 1))⁻¹ with hf
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hsum : Summable f := summable_inv_pow_pow hb hr
  -- The denominators `b ^ (r ^ n)` tend to infinity.
  have hmono : StrictMono fun n : ℕ ↦ b ^ r ^ n := fun m n hmn ↦
    Nat.pow_lt_pow_right hb (Nat.pow_lt_pow_right hr hmn)
  refine ⟨3, hmono.tendsto_atTop.frequently_map _ (fun n h ↦ h)
    (Filter.Frequently.of_forall fun n ↦ ?_)⟩
  set q : ℕ := b ^ r ^ n with hq
  have hq0 : (0 : ℝ) < q := by rw [hq]; push_cast; positivity
  have hqr : ((q : ℝ)) = (b : ℝ) ^ r ^ n := by rw [hq]; push_cast; rfl
  refine ⟨∑ k ∈ Finset.range n, (b : ℤ) ^ (r ^ n - r ^ (k + 1)), ?_⟩
  -- The tail `∑_k f (k + n)` is positive and, by the tail estimate, less than `3 / q ^ r`.
  have htail : ∑' k : ℕ, f k - ∑ k ∈ Finset.range n, f k = ∑' k : ℕ, f (k + n) := by
    rw [← hsum.sum_add_tsum_nat_add n]; ring
  have hpos : 0 < ∑' k : ℕ, f (k + n) :=
    ((summable_nat_add_iff n).2 hsum).tsum_pos (fun k ↦ by positivity) 0 (by positivity)
  have hlt : ∑' k : ℕ, f (k + n) < 3 / (q : ℝ) ^ (r : ℝ) := by
    refine lt_of_le_of_lt ?_ (div_lt_div_of_pos_right (by norm_num : (2 : ℝ) < 3) (by positivity))
    rw [Real.rpow_natCast, hqr]
    simpa [hf, add_right_comm] using tsum_inv_pow_pow_tail_le hb hr n
  -- `partial_sum_inv_pow_pow_eq` is stated with the denominator `(b : ℝ) ^ r ^ n`, while the
  -- goal has the cast `(q : ℝ)` of the natural number `q = b ^ r ^ n`; `hqr` bridges the two.
  have hrepr : ((∑ k ∈ Finset.range n, (b : ℤ) ^ (r ^ n - r ^ (k + 1)) : ℤ) : ℝ) / q =
      ∑ k ∈ Finset.range n, f k := by
    rw [hqr]; exact partial_sum_inv_pow_pow_eq (by omega) n
  rw [hrepr]
  refine ⟨fun h ↦ hpos.ne' (by rw [← htail, h, sub_self]), ?_⟩
  rw [htail, abs_of_pos hpos]
  exact hlt

end Lacunary

end TauCeti

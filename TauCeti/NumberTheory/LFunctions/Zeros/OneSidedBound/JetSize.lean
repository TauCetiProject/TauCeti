/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Logarithmic jet sizes and the sum over directions

A derivative of order `j` contributes the logarithm of `j!` plus `j` times the
logarithmic scale. In a comparison of covolumes this size is offset by a prime sum,
which measures divisibility. We bound the resulting sum over the directions and
show how a subset of directions of large weight supplies a lower bound for the
main amount, without requiring a lower bound for the prime sums.

The definitions follow `New.Data.jetSize` and `New.Data.directionAmount` in
`grh/src/New/Reduction/Data/AdmissibleData.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`. The jet interval bound, the direction bounds,
and the rank-scaled lower bound adapt `New.Data.jetSize_mem_Icc`,
`New.Data.directionAmount_mem_Icc`, and `New.Data.le_mainAmount`, respectively, from
`grh/src/New/Reduction/PrimeSums.lean` at the same commit.
-/

public section

open Finset Real Set
open scoped Nat

namespace TauCeti.OneSidedBound

/-- The logarithmic size charged to a derivative of order `j` at scale `exp c`. -/
noncomputable def jetSize (c : ℝ) (j : ℕ) : ℝ := log (j ! : ℝ) + j * c

/-- The factorial term and the logarithmic scale in the jet size. -/
theorem jetSize_def (c : ℝ) (j : ℕ) : jetSize c j = log (j ! : ℝ) + j * c := (rfl)

/-- A jet of order zero has no logarithmic size cost. -/
@[simp] theorem jetSize_zero (c : ℝ) : jetSize c 0 = 0 := by
  simp [jetSize_def]

/-- For orders at most `b²`, the logarithm of the factorial costs at most `2j log b`. -/
theorem jetSize_le {c b : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ b ^ 2) :
    jetSize c j ≤ j * (c + 2 * log b) := by
  rcases eq_or_ne j 0 with rfl | hj₀
  · simp
  have hjpos : (0 : ℝ) < j := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj₀)
  have hfac : log (j ! : ℝ) ≤ j * (2 * log b) := by
    calc
      log (j ! : ℝ) ≤ log ((j : ℝ) ^ j) :=
        log_le_log (by positivity) (by exact_mod_cast j.factorial_le_pow)
      _ = j * log (j : ℝ) := log_pow _ _
      _ ≤ j * log (b ^ 2) := mul_le_mul_of_nonneg_left (log_le_log hjpos hj) hjpos.le
      _ = j * (2 * log b) := by rw [log_pow]; norm_num
  rw [jetSize_def, mul_add]
  linarith

/-- Bounds for the jet size for orders `j ≤ b²` when the logarithmic scale is between
`20 log b` and `23 log b`. -/
theorem jetSize_mem_Icc {c b : ℝ} {j : ℕ} (hj : (j : ℝ) ≤ b ^ 2)
    (hc₁ : 20 * log b ≤ c) (hc₂ : c ≤ 23 * log b) :
    jetSize c j ∈ Icc (20 * j * log b) (25 * j * log b) := by
  have hj₀ : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  refine ⟨?_, (jetSize_le hj).trans ?_⟩
  · rw [jetSize_def]
    linarith [log_natCast_nonneg (j !), mul_le_mul_of_nonneg_left hc₁ hj₀]
  · linarith [mul_le_mul_of_nonneg_left hc₂ hj₀]

/-- The size remaining after subtracting a prime sum bounded by `j * l` is at least
`j * (c - l)`. There is no restriction on the order of the jet. -/
theorem mul_sub_le_jetSize_sub {c l P : ℝ} {j : ℕ} (hP : P ≤ j * l) :
    j * (c - l) ≤ jetSize c j - P := by
  rw [jetSize_def, mul_sub]
  linarith [log_natCast_nonneg (j !)]

/-- The total logarithmic size of the jets, less their prime-sum contributions. Here `κ i`
is the derivative order in direction `i` and `P i` is the prime sum at that order. -/
noncomputable def directionAmount {ι : Type*} (s : Finset ι) (κ : ι → ℕ)
    (c : ℝ) (P : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (jetSize c (κ i) - P i)

/-- The total remaining size is the sum of the individual remaining sizes. -/
theorem directionAmount_def {ι : Type*} (s : Finset ι) (κ : ι → ℕ) (c : ℝ) (P : ι → ℝ) :
    directionAmount s κ c P = ∑ i ∈ s, (jetSize c (κ i) - P i) := (rfl)

/-- The total size over no directions is zero. -/
@[simp] theorem directionAmount_empty {ι : Type*} (κ : ι → ℕ) (c : ℝ) (P : ι → ℝ) :
    directionAmount ∅ κ c P = 0 := by
  simp [directionAmount_def]

/-- Any subset of directions gives a lower bound for the remaining size when the logarithmic
scale dominates the prime-sum rate. Each unit of derivative order on the subset contributes
at least `c - l`. -/
theorem sum_mul_sub_le_directionAmount {ι : Type*} {s t : Finset ι} {κ : ι → ℕ}
    {c l : ℝ} {P : ι → ℝ} (ht : t ⊆ s) (hl : l ≤ c)
    (hP : ∀ i ∈ s, P i ≤ κ i * l) :
    (∑ i ∈ t, (κ i : ℝ)) * (c - l) ≤ directionAmount s κ c P := by
  rw [Finset.sum_mul, directionAmount_def]
  calc
    ∑ i ∈ t, (κ i : ℝ) * (c - l) ≤ ∑ i ∈ t, (jetSize c (κ i) - P i) :=
      sum_le_sum fun i hi ↦ mul_sub_le_jetSize_sub (hP i (ht hi))
    _ ≤ ∑ i ∈ s, (jetSize c (κ i) - P i) :=
      sum_le_sum_of_subset_of_nonneg ht fun i hi _ ↦
        (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hl)).trans
          (mul_sub_le_jetSize_sub (hP i hi))

/-- Suppose `0 ≤ log b` and the logarithmic scale `c` is at most `23 log b`. If every derivative
order is at most `b` and the prime sums are nonnegative, the total remaining size is at most
`25 b log b` times the number of directions. -/
theorem directionAmount_le {ι : Type*} {s : Finset ι} {κ : ι → ℕ} {c b : ℝ}
    {P : ι → ℝ} (hlog : 0 ≤ log b) (hc : c ≤ 23 * log b)
    (hκ : ∀ i ∈ s, (κ i : ℝ) ≤ b) (hP : ∀ i ∈ s, 0 ≤ P i) :
    directionAmount s κ c P ≤ 25 * s.card * b * log b := by
  rw [directionAmount_def]
  calc
    ∑ i ∈ s, (jetSize c (κ i) - P i) ≤ ∑ _i ∈ s, 25 * b * log b := by
      refine sum_le_sum fun i hi ↦ ?_
      have hj : (κ i : ℝ) ≤ b ^ 2 := by
        rcases eq_or_ne (κ i) 0 with hj | hj
        · simp only [hj, Nat.cast_zero]
          positivity
        · have h₁ : (1 : ℝ) ≤ κ i := by exact_mod_cast Nat.pos_of_ne_zero hj
          have hb := h₁.trans (hκ i hi)
          exact (hκ i hi).trans (by nlinarith)
      have hsize := jetSize_le (c := c) hj
      have hlog25 : 0 ≤ 25 * log b := by positivity
      linarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (κ i)),
        mul_le_mul_of_nonneg_right (hκ i hi) hlog25, hP i hi]
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

/-- Suppose `b` is nonnegative, `c - log b` is at least both `0` and `log b`, and each prime sum
`P i` on `s` is at most `κ i * log b`. A subset `t ⊆ s` of orders at least `b` then gives a
lower bound of `b * T` for the total remaining size whenever `T ≤ t.card * log b`. -/
theorem mul_le_directionAmount {ι : Type*} {s t : Finset ι} {κ : ι → ℕ} {c b T : ℝ}
    {P : ι → ℝ} (ht : t ⊆ s) (hb : 0 ≤ b) (hc : max 0 (log b) ≤ c - log b)
    (hκ : ∀ i ∈ t, b ≤ κ i) (hT : T ≤ t.card * log b)
    (hP : ∀ i ∈ s, P i ≤ κ i * log b) :
    b * T ≤ directionAmount s κ c P := by
  have hl : 0 ≤ c - log b := (le_max_left _ _).trans hc
  have hsum := sum_mul_sub_le_directionAmount ht (sub_nonneg.mp hl) hP
  have hκsum : (t.card : ℝ) * b ≤ ∑ i ∈ t, (κ i : ℝ) := by
    simpa only [sum_const, nsmul_eq_mul] using sum_le_sum hκ
  calc
    b * T ≤ b * ((t.card : ℝ) * log b) := mul_le_mul_of_nonneg_left hT hb
    _ = (t.card : ℝ) * b * log b := by ring
    _ ≤ (t.card : ℝ) * b * (c - log b) :=
      mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hc) (by positivity)
    _ ≤ _ := (mul_le_mul_of_nonneg_right hκsum hl).trans hsum

/-- A bound on the product of the ranks converts the contribution of the large-weight
subset into a lower bound for the main amount. The number of directions is `F * T`, and
`a = x * b` is the unscaled derivative order. -/
theorem le_rank_mul_directionAmount {ι : Type*} {s t : Finset ι} {κ : ι → ℕ}
    {c rank : ℝ} {b T F x : ℕ} {P : ι → ℝ} (ht : t ⊆ s) (hc : 2 * log b ≤ c)
    (hκ : ∀ i ∈ t, b ≤ κ i) (hT : T ≤ t.card * log b)
    (hP : ∀ i ∈ s, P i ≤ κ i * log b) (hcard : s.card = F * T)
    (hrank : F * (x : ℝ) ^ 5 ≤ rank) :
    (x : ℝ) ^ 4 * s.card * ((x : ℝ) * b) ≤ rank * directionAmount s κ c P := by
  have hBT : (b : ℝ) * T ≤ directionAmount s κ c P :=
    mul_le_directionAmount ht (Nat.cast_nonneg _) (max_le (by linarith [log_natCast_nonneg b])
      (by linarith)) (by exact_mod_cast hκ) hT hP
  calc
    (x : ℝ) ^ 4 * s.card * ((x : ℝ) * b) = (F * (x : ℝ) ^ 5) * ((b : ℝ) * T) := by
      rw [hcard, Nat.cast_mul]
      ring
    _ ≤ (F * (x : ℝ) ^ 5) * directionAmount s κ c P :=
      mul_le_mul_of_nonneg_left hBT (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hrank ((by positivity : 0 ≤ (b : ℝ) * T).trans hBT)

/-- The scale separation and the lower bounds on the ranks pay for a factor `F` in the
main-amount estimate, provided `F ≤ l` (where `l` is the logarithm of the larger cutoff). -/
theorem mul_pow_five_le_mul_of_separated_scales {l F x m k : ℝ}
    (hl : 2 ≤ l) (hF : F ≤ l) (hx : l ^ 8 ≤ x) (hm : 0 ≤ m) (hm₂ : x ≤ m ^ 2)
    (hk : exp (-2) * x ^ 5 ≤ k) : F * x ^ 5 ≤ m * k := by
  have hl₀ : 0 ≤ l := by linarith
  have hx₀ : 0 ≤ x := (by positivity : 0 ≤ l ^ 8).trans hx
  have h₄ : l ^ 4 ≤ m := by
    refine le_of_pow_le_pow_left₀ two_ne_zero hm ?_
    rw [← pow_mul]
    exact hx.trans hm₂
  have he : exp 2 ≤ 8 := by
    have htwo : (2 : ℝ) = 1 + 1 := by norm_num
    rw [htwo, exp_add]
    nlinarith [exp_one_lt_d9, exp_pos 1]
  have hl₃ : (8 : ℝ) ≤ l ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hl 3
    norm_num at h
    exact h
  have hmul : exp 2 * l ≤ m := calc
    exp 2 * l ≤ l ^ 3 * l := mul_le_mul_of_nonneg_right (he.trans hl₃) hl₀
    _ = l ^ 4 := by ring
    _ ≤ m := h₄
  have hcancel : l ≤ m * exp (-2) := by
    rw [exp_neg, ← div_eq_mul_inv, le_div_iff₀ (exp_pos 2)]
    simpa only [mul_comm] using hmul
  calc
    F * x ^ 5 ≤ (m * exp (-2)) * x ^ 5 :=
      mul_le_mul_of_nonneg_right (hF.trans hcancel) (by positivity)
    _ = m * (exp (-2) * x ^ 5) := mul_assoc ..
    _ ≤ m * k := mul_le_mul_of_nonneg_left hk hm

end TauCeti.OneSidedBound

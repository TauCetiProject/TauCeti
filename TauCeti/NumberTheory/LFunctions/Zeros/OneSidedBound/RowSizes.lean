/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.SpecialFunctions.Log.Factorial

/-!
# Logarithmic row costs of a theta lift chain

The cost of differentiating to order `r` at logarithmic scale `C` is `log(r!) + r C`.
For a row with extra boxes beyond its reference length, the factorial estimate charges
at most one logarithmic factor per extra box. Summing first over rows and then over
places and lifts bounds the total cost by the reference cost plus half the allowed error.

The reference lengths and error budget are those in `New.Data.sum_rowSizeSum_le` of
`New/UpperBound/Size/ArchimedeanSize.lean` in lsernau/grh-lean (`72fead1`).
-/

public section

open Finset

namespace TauCeti

/-- Bound the cost of one lift diagram at one place by the cost of the first reference
row and at most `k` equal reference rows. Each extra box costs at most `log B + C`,
where `B` bounds the actual row lengths. The first row may have additional slack `u`
on top of the common per-row slack `v`. -/
theorem sum_row_cost_le {n k a w u v B : ℕ} {C : ℝ} (hC : 0 ≤ C) (r : ℕ → ℕ)
    (hB : ∀ i < n, r i ≤ B)
    (hr : ∀ i < n, r i ≤ (if i = 0 then a else if i < k then w else 0) +
      ((if i = 0 then u else 0) + v)) :
    let cost := fun l : ℕ ↦ Real.log (l.factorial : ℝ) + l * C
    ∑ i ∈ range n, cost (r i) ≤ cost a + k * cost w + (Real.log (B : ℝ) + C) * (u + n * v) := by
  dsimp only
  let cost := fun l : ℕ ↦ Real.log (l.factorial : ℝ) + l * C
  have hcost (l : ℕ) : 0 ≤ cost l :=
    add_nonneg (Real.log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC)
  have hbox : 0 ≤ Real.log (B : ℝ) + C := add_nonneg (Real.log_natCast_nonneg _) hC
  have hrow (i : ℕ) (hi : i < n) :
      cost (r i) ≤ cost (if i = 0 then a else if i < k then w else 0) +
        (Real.log (B : ℝ) + C) * (((if i = 0 then u else 0) + v : ℕ) : ℝ) := by
    simpa only [cost, mul_comm (Real.log (B : ℝ) + C)] using
      Real.log_factorial_add_mul_le_of_le_add hC (hr i hi) (hB i hi)
  have hmain : (∑ i ∈ range n, cost (if i = 0 then a else if i < k then w else 0)) ≤
      cost a + k * cost w := by
    cases n with
    | zero => simpa using add_nonneg (hcost a) (mul_nonneg (Nat.cast_nonneg k) (hcost w))
    | succ n =>
      have hs : (range n).filter (fun i ↦ i + 1 < k) ⊆ range k := by
        intro i hi
        exact mem_range.mpr (by have := (mem_filter.mp hi).2; omega)
      rw [sum_range_succ']
      have hz : cost 0 = 0 := by simp [cost]
      simp only [Nat.succ_ne_zero, ite_false, ite_true, apply_ite cost, hz, ← sum_filter, sum_const,
        nsmul_eq_mul]
      have hk : (((range n).filter (fun i ↦ i + 1 < k)).card : ℝ) ≤ k := by
        exact_mod_cast (card_le_card hs).trans_eq (card_range k)
      linarith only [mul_le_mul_of_nonneg_right hk (hcost w)]
  have hslack : (∑ i ∈ range n, ((if i = 0 then u else 0) + v : ℕ)) ≤ u + n * v := by
    cases n with
    | zero => simp
    | succ n => rw [sum_range_succ']; simp [Nat.succ_mul, add_assoc, add_comm]
  calc
    _ ≤ ∑ i ∈ range n, (cost (if i = 0 then a else if i < k then w else 0) +
          (Real.log (B : ℝ) + C) * (((if i = 0 then u else 0) + v : ℕ) : ℝ)) :=
      sum_le_sum fun i hi ↦ hrow i (mem_range.mp hi)
    _ ≤ _ := by
      rw [sum_add_distrib, ← mul_sum, ← Nat.cast_sum]
      exact add_le_add hmain (mul_le_mul_of_nonneg_left (by exact_mod_cast hslack) hbox)

-- The slack budget for one lift diagram, including its extra first-row allowance.
private theorem row_slack_cost_le {x x₁ b n g : ℕ} {C : ℝ} (hx₁ : x ≤ x₁) (hxb : x ≤ b)
    (hb : 13 ≤ Real.log (b : ℝ)) (hCb : C ≤ 23 * Real.log (b : ℝ))
    (hg : n * g ^ 2 ≤ b) :
    (Real.log ((2 * (x * b) : ℕ) : ℝ) + C) * (↑(b + x * b / x₁) + n * (↑(g ^ 2) : ℝ)) ≤
      78 * Real.log (b : ℝ) * b := by
  have hb₂ : 2 ≤ b := by
    by_contra! h
    interval_cases b <;> norm_num at hb
  have hlog : Real.log ((2 * (x * b) : ℕ) : ℝ) ≤ 3 * Real.log (b : ℝ) := by
    by_cases hx : x = 0
    · simpa [hx] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (by linarith)
    · have hpos : 0 < 2 * (x * b) := Nat.mul_pos (by decide)
        (Nat.mul_pos (Nat.pos_of_ne_zero hx) (by omega))
      calc
        _ ≤ Real.log ((b : ℝ) ^ 3) := by
          apply Real.log_le_log (by exact_mod_cast hpos)
          have hb₂' : (2 : ℝ) ≤ b := by exact_mod_cast hb₂
          have hxb' : (x : ℝ) ≤ b := by exact_mod_cast hxb
          push_cast
          calc
            _ ≤ (b : ℝ) * (b * b) := by gcongr
            _ = _ := by ring
        _ = _ := by rw [Real.log_pow]; norm_num
  have hdiv : x * b / x₁ ≤ b := Nat.div_le_of_le_mul (by
    simpa [mul_comm] using Nat.mul_le_mul_right b hx₁)
  have hslack : (↑(b + x * b / x₁) + (n : ℝ) * (↑(g ^ 2) : ℝ)) ≤ 3 * b := by
    exact_mod_cast (by omega : b + x * b / x₁ + n * g ^ 2 ≤ 3 * b)
  calc
    _ ≤ (26 * Real.log (b : ℝ)) * (3 * b) :=
      mul_le_mul (by linarith only [hlog, hCb]) hslack (by positivity) (by positivity)
    _ = _ := by ring

/-- Sum the row costs of `m` lifts over all places. The first reference row has length `x b`
at the places in `A` and vanishes elsewhere; the next reference rows have weight `κ`. The first
row's extra allowance is `b + x b / x₁`, and the common allowance per row is `g²`. If the latter
costs at most `b` boxes in each diagram, the total excess is bounded by `f x b (log b)³ / 2`,
where `f` is the number of places. -/
theorem _root_.Finset.sum_row_size_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (κ : ι → ℕ) (n : ℕ → ℕ) (r : ℕ → ι → ℕ → ℕ) {x x₁ b m k g : ℕ} {C : ℝ}
    (hm : m ≤ x) (hx₁ : x ≤ x₁) (hxb : x ≤ b) (hb : 13 ≤ Real.log (b : ℝ))
    (hC : 0 ≤ C) (hCb : C ≤ 23 * Real.log (b : ℝ))
    (hg : ∀ j < m, n j * g ^ 2 ≤ b)
    (hcap : ∀ j < m, ∀ p i, i < n j → r j p i ≤ 2 * (x * b))
    (hrow : ∀ j < m, ∀ p i, i < n j →
      r j p i ≤ (if i = 0 then if p ∈ A then x * b else 0 else if i < k then κ p else 0) +
        ((if i = 0 then b + x * b / x₁ else 0) + g ^ 2)) :
    let cost := fun l : ℕ ↦ Real.log (l.factorial : ℝ) + l * C
    (∑ j ∈ range m, ∑ p : ι, ∑ i ∈ range (n j), cost (r j p i)) ≤
      m * (A.card * cost (x * b) + k * ∑ p : ι, cost (κ p)) +
        Fintype.card ι * (x * b : ℕ) * Real.log (b : ℝ) ^ 3 / 2 := by
  dsimp only
  let cost := fun l : ℕ ↦ Real.log (l.factorial : ℝ) + l * C
  let L := Real.log (b : ℝ)
  have hcost (j : ℕ) (hj : j ∈ range m) (p : ι) :
      (∑ i ∈ range (n j), cost (r j p i)) ≤
        (if p ∈ A then cost (x * b) else 0) + k * cost (κ p) + 78 * L * b := by
    have h := sum_row_cost_le (a := if p ∈ A then x * b else 0) hC (r j p)
      (hcap j (mem_range.mp hj) p) (hrow j (mem_range.mp hj) p)
    have hz : cost 0 = 0 := by simp [cost]
    have hs := row_slack_cost_le hx₁ hxb hb hCb (hg j (mem_range.mp hj))
    have h' : (∑ i ∈ range (n j), cost (r j p i)) ≤
        cost (if p ∈ A then x * b else 0) + k * cost (κ p) + 78 * L * b :=
      h.trans (add_le_add_right hs _)
    simpa only [apply_ite cost, hz] using h'
  have herr : (m : ℝ) * (Fintype.card ι * (78 * L * b)) ≤
      Fintype.card ι * (x * b : ℕ) * L ^ 3 / 2 := by
    have hL : 13 ≤ L := hb
    have h : 78 * L ≤ L ^ 3 / 2 := by
      have hs : 156 ≤ L ^ 2 := by nlinarith only [hL, sq_nonneg (L - 13)]
      nlinarith [mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ L)]
    push_cast
    calc
      _ = Fintype.card ι * (m * b) * (78 * L) := by ring
      _ ≤ Fintype.card ι * (x * b) * (L ^ 3 / 2) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ j ∈ range m, ∑ p : ι,
          ((if p ∈ A then cost (x * b) else 0) + k * cost (κ p) + 78 * L * b) :=
      sum_le_sum fun j hj ↦ sum_le_sum fun p _ ↦ hcost j hj p
    _ = m * (A.card * cost (x * b) + k * ∑ p : ι, cost (κ p) +
        Fintype.card ι * (78 * L * b)) := by
      simp [sum_add_distrib, ← mul_sum, mul_add]
    _ ≤ _ := by rw [mul_add]; exact add_le_add_right herr _

end TauCeti

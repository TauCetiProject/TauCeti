/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Nat.ModEq

/-!
# Dedekind sums and their reciprocity law

For an integer `h` and a natural number `c`, the Dedekind sum is
`s(h, c) = ∑_{r=1}^{c-1} (r / c) (h r / c - ⌊h r / c⌋ - 1/2)`.
It is the arithmetic part of the multiplier of the Dedekind eta function: for
`γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0`, the multiplier of `η` with respect to the principal
root `√(c τ + d)` is `exp(π i ((a + d) / (12 c) - s(d, c) - 1/4))` (Apostol, Theorem 3.4).

This file defines `s(h, c)` as a rational number, proves that it depends only on `h` modulo `c`,
and proves Dedekind's reciprocity law: for coprime `h, c ≥ 1`,
`s(h, c) + s(c, h) = (h² + c² + 1) / (12 h c) - 1/4`.
At `h = 1` it evaluates `s(1, c) = (c - 1)(c - 2) / (12 c)`.

The proof is elementary. Writing `h r = c ⌊h r / c⌋ + (h r mod c)` expresses `s(h, c)` through
the weighted floor sum `∑_{r < c} r ⌊h r / c⌋`. Counting the lattice points under the diagonal of
the rectangle `(0, c) × (0, h)` from either side relates this weighted floor sum to the sums of
`⌊c s / h⌋` and `⌊c s / h⌋²` over `s < h`. Since `s ↦ c s mod h` permutes the residues modulo
`h`, the first and second moments of the residues `c s mod h` are those of `0, …, h - 1`, which
eliminates these two sums.

## Main definitions

* `TauCeti.dedekindSum h c`: the Dedekind sum `s(h, c)`.

## Main results

* `TauCeti.dedekindSum_add_mul_self`, `TauCeti.dedekindSum_mod_left`: `s(h, c)` depends only on
  `h` modulo `c`.
* `TauCeti.dedekindSum_reciprocity`: Dedekind's reciprocity law.
* `TauCeti.dedekindSum_one_left`: `s(1, c) = (c - 1)(c - 2) / (12 c)`.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, Chapter 3, the
  definition of `s(h, k)` and Theorem 3.7.
* H. Rademacher and E. Grosswald, *Dedekind Sums*, Chapter 2.
-/

public section

open Finset

namespace TauCeti

/-- The Dedekind sum `s(h, c) = ∑_{r=1}^{c-1} (r / c) (h r / c - ⌊h r / c⌋ - 1/2)`. The sum is
taken over `r < c`; its term at `r = 0` vanishes. For `c = 0` the sum is empty. -/
def dedekindSum (h : ℤ) (c : ℕ) : ℚ :=
  ∑ r ∈ range c, (r / c : ℚ) * (Int.fract (h * r / c : ℚ) - 1 / 2)

/-- The Dedekind sum `s(h, 0)` is the empty sum. -/
@[simp]
theorem dedekindSum_zero_right (h : ℤ) : dedekindSum h 0 = 0 := by
  simp [dedekindSum]

/-- The Dedekind sum `s(h, 1)` vanishes: its only term is at `r = 0`. -/
@[simp]
theorem dedekindSum_one_right (h : ℤ) : dedekindSum h 1 = 0 := by
  simp [dedekindSum]

/-- The Dedekind sum `s(h, c)` is unchanged when a multiple of `c` is added to `h`. -/
@[simp]
theorem dedekindSum_add_mul_self (h m : ℤ) (c : ℕ) :
    dedekindSum (h + m * c) c = dedekindSum h c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  refine sum_congr rfl fun r _ ↦ ?_
  have : ((h + m * c : ℤ) : ℚ) * r / c = h * r / c + ((m * r : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [this, Int.fract_add_intCast]

/-- The Dedekind sum `s(h, c)` depends only on `h` modulo `c`. -/
theorem dedekindSum_mod_left (h : ℤ) (c : ℕ) : dedekindSum (h % c) c = dedekindSum h c := by
  conv_rhs => rw [← Int.emod_add_ediv_mul h c, dedekindSum_add_mul_self]

/-- The Dedekind sum is odd in `h`: `s(-h, c) = -s(h, c)` for `h` coprime to `c`. -/
theorem dedekindSum_neg {h : ℤ} {c : ℕ} (hhc : IsCoprime h c) :
    dedekindSum (-h) c = -dedekindSum h c := by
  rw [dedekindSum, dedekindSum, ← sum_neg_distrib]
  refine sum_congr rfl fun r hr ↦ ?_
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  have hne : Int.fract ((h : ℚ) * r / c) ≠ 0 := by
    have hcast : (h : ℚ) * r / c = ((h * r : ℤ) : ℚ) / c := by push_cast; ring
    rw [hcast, Int.fract_div_intCast_eq_div_intCast_mod]
    refine div_ne_zero (Int.cast_ne_zero.2 fun hmod ↦ ?_)
      (Nat.cast_ne_zero.2 (ne_zero_of_lt (mem_range.1 hr)))
    have hdvd : (c : ℤ) ∣ r :=
      hhc.symm.dvd_of_dvd_mul_left (Int.dvd_of_emod_eq_zero hmod)
    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) (Int.natCast_dvd_natCast.1 hdvd))
      (not_le.2 (mem_range.1 hr))
  rw [Int.cast_neg, neg_mul, neg_div, Int.fract_neg hne]
  ring

/-! ### The reciprocity law -/

/-- The Dedekind sum through the weighted floor sum `∑_{r < c} r ⌊h r / c⌋`:
`c² s(h, c) = h ∑_{r < c} r² - c ∑_{r < c} r ⌊h r / c⌋ - (c / 2) ∑_{r < c} r`. -/
private theorem sq_mul_dedekindSum_natCast (h : ℕ) {c : ℕ} (hc : c ≠ 0) :
    (c : ℚ) ^ 2 * dedekindSum h c = h * ∑ r ∈ range c, (r : ℚ) ^ 2 -
      c * ∑ r ∈ range c, (r : ℚ) * ((h * r / c : ℕ) : ℚ) - c / 2 * ∑ r ∈ range c, (r : ℚ) := by
  rw [dedekindSum, mul_sum, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun r _ ↦ ?_
  have hmod : ((h * r % c : ℕ) : ℚ) = h * r - c * ((h * r / c : ℕ) : ℚ) := by
    rw [eq_sub_iff_add_eq, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
  have hfract : Int.fract ((h : ℤ) * r / c : ℚ) = ((h * r % c : ℕ) : ℚ) / c := by
    rw [← Int.fract_div_natCast_eq_div_natCast_mod, Int.cast_natCast, Nat.cast_mul]
  rw [hfract, hmod]
  field_simp

/-- Counting lattice points under the diagonal of the rectangle `(0, c) × (0, h)` from either
side: for coprime `h, c` with `h > 0`,
`2 ∑_{r < c} r ⌊h r / c⌋ + ∑_{s < h} ⌊c s / h⌋ (⌊c s / h⌋ + 1) = (h - 1) c (c - 1)`. -/
private theorem two_mul_sum_mul_div_add_sum_div_mul_div_add_one {h c : ℕ} (hh : 0 < h)
    (hhc : h.Coprime c) :
    2 * ∑ r ∈ range c, r * (h * r / c) + ∑ s ∈ range h, (c * s / h) * (c * s / h + 1) =
      (h - 1) * (c * (c - 1)) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  -- `⌊h r / c⌋` counts the `1 ≤ s < h` with `s c ≤ h r`; swap the order of summation.
  have hcount (r : ℕ) (hr : r ∈ range c) :
      h * r / c = ∑ s ∈ Ico 1 h, if s * c ≤ h * r then 1 else 0 := by
    have hlt : h * r / c < h :=
      Nat.div_lt_of_lt_mul (by rw [mul_comm c]; exact (Nat.mul_lt_mul_left hh).2 (mem_range.1 hr))
    rw [ZMod.div_eq_filter_card hc (Nat.le_sub_one_of_lt hlt), Nat.succ_eq_add_one,
      Nat.sub_add_cancel hh, card_eq_sum_ones, sum_filter]
  -- For `1 ≤ s < h`, the points `r` with `s c ≤ h r` are exactly those above `⌊c s / h⌋`.
  have hinner (s : ℕ) (hs : s ∈ Ico 1 h) :
      2 * ∑ r ∈ range c, (if s * c ≤ h * r then r else 0) +
        (c * s / h) * (c * s / h + 1) = c * (c - 1) := by
    obtain ⟨hs1, hsh⟩ := mem_Ico.1 hs
    have hiff (r : ℕ) : s * c ≤ h * r ↔ c * s / h < r := by
      rw [Nat.div_lt_iff_lt_mul hh, mul_comm c, mul_comm r]
      refine ⟨fun hle ↦ hle.lt_of_ne fun heq ↦ ?_, le_of_lt⟩
      have : h ∣ s * c := ⟨r, heq⟩
      exact absurd (Nat.le_of_dvd hs1 (hhc.dvd_of_dvd_mul_right this)) (not_le.2 hsh)
    have hB : c * s / h + 1 ≤ c :=
      Nat.div_lt_of_lt_mul (by rw [mul_comm h]; exact (Nat.mul_lt_mul_left hc).2 hsh)
    have hlow := sum_range_id_mul_two (c * s / h + 1)
    rw [Nat.add_sub_cancel] at hlow
    simp_rw [hiff]
    rw [← sum_range_id_mul_two, ← sum_range_add_sum_Ico _ hB, ← sum_range_add_sum_Ico _ hB,
      sum_eq_zero fun r hr ↦ ite_eq_right_iff.2 fun hlt ↦
        absurd (Nat.lt_succ_iff.1 (mem_range.1 hr)) (not_le.2 hlt),
      sum_congr rfl fun r hr ↦ ite_eq_left_iff.2 fun hlt ↦
        absurd (Nat.lt_of_succ_le (mem_Ico.1 hr).1) hlt]
    linarith
  have hswap : ∑ r ∈ range c, r * (h * r / c) =
      ∑ s ∈ Ico 1 h, ∑ r ∈ range c, if s * c ≤ h * r then r else 0 := by
    rw [sum_comm]
    refine sum_congr rfl fun r hr ↦ ?_
    rw [hcount r hr, mul_sum]
    simp_rw [mul_ite, mul_one, mul_zero]
  rw [sum_range_eq_add_Ico (fun s ↦ (c * s / h) * (c * s / h + 1)) hh, hswap, mul_sum]
  simp only [mul_zero, Nat.zero_div, zero_mul, zero_add]
  rw [← sum_add_distrib, sum_congr rfl hinner, sum_const, Nat.card_Ico, smul_eq_mul]

/-- **Dedekind's reciprocity law**: for coprime `h, c ≥ 1`,
`s(h, c) + s(c, h) = (h² + c² + 1) / (12 h c) - 1/4`. -/
theorem dedekindSum_reciprocity {h c : ℕ} (hh : 0 < h) (hc : 0 < c) (hhc : h.Coprime c) :
    dedekindSum h c + dedekindSum c h = (h ^ 2 + c ^ 2 + 1) / (12 * h * c) - 1 / 4 := by
  have hh' : (h : ℚ) ≠ 0 := by positivity
  have hc' : (c : ℚ) ≠ 0 := by positivity
  have E₁ := sq_mul_dedekindSum_natCast h hc.ne'
  have E₂ := sq_mul_dedekindSum_natCast c hh.ne'
  -- The lattice-point count, cast to `ℚ`.
  have F : 2 * ∑ r ∈ range c, (r : ℚ) * ((h * r / c : ℕ) : ℚ) +
      ∑ s ∈ range h, ((c * s / h : ℕ) : ℚ) ^ 2 + ∑ s ∈ range h, ((c * s / h : ℕ) : ℚ) =
        (h - 1) * (c * (c - 1)) := by
    have := congrArg (Nat.cast (R := ℚ)) (two_mul_sum_mul_div_add_sum_div_mul_div_add_one hh hhc)
    push_cast [Nat.cast_sub hh, Nat.cast_sub hc] at this
    rw [← this, add_assoc, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun s _ ↦ by ring
  -- The residues `c s mod h = c s - h ⌊c s / h⌋` are a permutation of `0, …, h - 1`.
  have hres (s : ℕ) : ((c * s % h : ℕ) : ℚ) = c * s - h * ((c * s / h : ℕ) : ℚ) := by
    rw [eq_sub_iff_add_eq, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
  have P₁ := Nat.Coprime.sum_range_mul_mod hhc.symm (fun j ↦ (j : ℚ))
  have P₂ := Nat.Coprime.sum_range_mul_mod hhc.symm (fun j ↦ (j : ℚ) ^ 2)
  simp only [hres] at P₁ P₂
  have hcross : ∑ s ∈ range h, 2 * ((c : ℚ) * s) * (h * ((c * s / h : ℕ) : ℚ)) =
      2 * c * h * ∑ s ∈ range h, (s : ℚ) * ((c * s / h : ℕ) : ℚ) := by
    rw [mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring
  simp only [sub_sq, mul_pow, sum_add_distrib, sum_sub_distrib, ← mul_sum, hcross] at P₁ P₂
  -- The power sums `∑_{r < n} r` and `∑_{r < n} r²`.
  have S₁ (n : ℕ) : ∑ r ∈ range n, (r : ℚ) = n * (n - 1) / 2 := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
  have S₂ (n : ℕ) : ∑ r ∈ range n, (r : ℚ) ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; push_cast; ring
  simp only [S₁, S₂] at E₁ E₂ P₁ P₂
  have key : 12 * h * c * (dedekindSum h c + dedekindSum c h) = h ^ 2 + c ^ 2 + 1 - 3 * h * c :=
    mul_left_cancel₀ (mul_ne_zero hh' hc') <| by
      linear_combination 12 * (h : ℚ) ^ 2 * E₁ + 12 * (c : ℚ) ^ 2 * E₂ -
        6 * (h : ℚ) ^ 2 * c * F + 6 * (c : ℚ) * P₂ - 6 * (h : ℚ) * c * P₁
  field_simp
  linear_combination 4 * key

/-- The Dedekind sum at `h = 1`: `s(1, c) = (c - 1)(c - 2) / (12 c)`. -/
theorem dedekindSum_one_left (c : ℕ) : dedekindSum 1 c = (c - 1) * (c - 2) / (12 * c) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  have := dedekindSum_reciprocity one_pos hc (Nat.coprime_one_left c)
  simp only [Nat.cast_one, dedekindSum_one_right, add_zero] at this
  have hc' : (c : ℚ) ≠ 0 := by positivity
  rw [this]
  field_simp
  ring

end TauCeti

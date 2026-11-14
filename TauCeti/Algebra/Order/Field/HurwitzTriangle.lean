/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sharp reciprocal bounds and equality cases for hyperbolic pairs and triples

For natural numbers `a, b, c ≥ 2` with `1/a + 1/b + 1/c < 1`, the deficit
`1 - 1/a - 1/b - 1/c` is at least `1/42`, attained uniquely (up to permutation) at `{2, 3, 7}`,
while every other triple with `1/a + 1/b + 1/c < 1` has deficit at least `1/24`, attained at
`{2, 3, 8}`. Likewise, for natural numbers `a, b` with `1/a + 1/b < 1`, the pair deficit
`1 - 1/a - 1/b` is at least `1/6`, attained uniquely at `{2, 3}`, while every other pair with
`1/a + 1/b < 1` has deficit at least `1/4`, attained at `{2, 4}`. Because `1 / (0 : K) = 0` and
`1 / (1 : K) = 1`, the new bounds and equality characterizations hold for all natural numbers
without lower-bound hypotheses on the indices.

Applied to ramification indices and Fuchsian orbifold signatures, these bounds and spectral gaps
give Hurwitz's sharp `84(g - 1)` bound, Siegel's `π/21` minimal-covolume theorem and its
`(0; 2, 3, 7)` uniqueness, and the `π/3` minimal-covolume theorem and `(0; 2, 3; 1)` uniqueness for
cusped Fuchsian groups.

All bounds and characterizations are stated in an arbitrary linearly ordered field.

## Main results

* `TauCeti.one_div_forty_two_le_hyperbolic_triangle_deficit` and
  `TauCeti.hyperbolic_triangle_deficit_eq_one_div_forty_two_iff`: sharp `1/42` lower bound and
  `{2, 3, 7}` uniqueness for hyperbolic triples, with
  `TauCeti.one_div_twenty_four_le_hyperbolic_triangle_deficit_of_ne` giving the `1/24` bound away
  from `{2, 3, 7}`.
* `TauCeti.one_div_six_le_hyperbolic_pair_deficit` and
  `TauCeti.hyperbolic_pair_deficit_eq_one_div_six_iff`: sharp `1/6` lower bound and `{2, 3}`
  uniqueness for hyperbolic pairs, with `TauCeti.one_div_four_le_hyperbolic_pair_deficit_of_ne`
  giving the `1/4` bound away from `{2, 3}`.

## References

* C. L. Siegel, *Some remarks on discontinuous groups*, Ann. of Math. (2) 46 (1945), 708–718.
* G. Martin, *The geometry and arithmetic of Kleinian groups*, Handbook of Group Actions, Vol. III,
  ALM 40 (2018), Theorems 2.1–2.2.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Exercise 3.18.
-/

public section

namespace TauCeti

variable {K : Type*}

/-- The sharp numerical bound for a hyperbolic triple of natural numbers, read in a linearly
ordered field. The equality case is realized by the indices `(2, 3, 7)`. -/
theorem one_div_forty_two_le_hyperbolic_triangle_deficit
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hhyper : (1 : K) / a + 1 / b + 1 / c < 1) :
    (1 : K) / 42 ≤ 1 - 1 / a - 1 / b - 1 / c := by
  wlog hab : a ≤ b generalizing a b c
  · linarith [this hb ha hc (by linarith) (by omega)]
  wlog hbc : b ≤ c generalizing a b c
  · rcases le_total a c with hac | hca
    · linarith [this ha hc hb (by linarith) hac (by omega)]
    · linarith [this hc ha hb (by linarith) hca hab]
  -- A sorted hyperbolic triple dominates `(2, 3, 7)`, `(2, 4, 5)` or `(3, 3, 4)` entrywise, and
  -- the deficit increases in each entry.
  rcases (by omega : a = 2 ∧ b = 2 ∨ a = 2 ∧ b = 3 ∨ a = 2 ∧ 4 ≤ b ∨ 3 ≤ a) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hb4⟩ | ha3
  · norm_num at hhyper
    exact absurd hhyper c.cast_nonneg.not_gt
  · have hc7 : 7 ≤ c := by
      by_contra
      interval_cases c <;> norm_num at hhyper
    calc (1 : K) / 42 = 1 - 1 / (2 : ℕ) - 1 / (3 : ℕ) - 1 / (7 : ℕ) := by norm_num
      _ ≤ _ := by gcongr
  · have hc5 : 5 ≤ c := by
      by_contra
      obtain ⟨rfl, rfl⟩ : b = 4 ∧ c = 4 := by omega
      norm_num at hhyper
    calc (1 : K) / 42 ≤ 1 - 1 / (2 : ℕ) - 1 / (4 : ℕ) - 1 / (5 : ℕ) := by norm_num
      _ ≤ _ := by gcongr
  · have hc4 : 4 ≤ c := by
      by_contra
      obtain ⟨rfl, rfl, rfl⟩ : a = 3 ∧ b = 3 ∧ c = 3 := by omega
      norm_num at hhyper
    calc (1 : K) / 42 ≤ 1 - 1 / (3 : ℕ) - 1 / (3 : ℕ) - 1 / (4 : ℕ) := by norm_num
      _ ≤ _ := by gcongr; omega

/-- The triangle indices `(2, 3, 7)` attain the bound. -/
theorem two_three_seven_deficit_eq_one_div_forty_two [DivisionRing K] [CharZero K] :
    (1 : K) - 1 / 2 - 1 / 3 - 1 / 7 = 1 / 42 := by
  norm_num

/-! ### Hyperbolic pairs -/

private theorem pair_deficit_eq_of_multiset_eq [DivisionRing K] [CharZero K] {a b : ℕ}
    (h : ({a, b} : Multiset ℕ) = {2, 3}) :
    (1 : K) - 1 / a - 1 / b = 1 / 6 := by
  have hsum := congrArg (fun s : Multiset ℕ ↦ (s.map fun n : ℕ ↦ (1 : K) - 1 / n).sum) h
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton, Nat.cast_ofNat] at hsum
  calc (1 : K) - 1 / a - 1 / b = (1 - 1 / a) + (1 - 1 / b) - 1 := by abel
    _ = (1 - 1 / 2) + (1 - 1 / 3) - 1 := by rw [hsum]
    _ = 1 / 6 := by norm_num

/-- Every pair `{a, b} ≠ {2, 3}` of natural numbers satisfying `1/a + 1/b < 1` has deficit
`1 - 1/a - 1/b` at least `1/4`, read in any linearly ordered field. The bound `1/4` is attained at
`{2, 4}`. -/
theorem one_div_four_le_hyperbolic_pair_deficit_of_ne
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b : ℕ} (hhyper : (1 : K) / a + 1 / b < 1) (hne : ({a, b} : Multiset ℕ) ≠ {2, 3}) :
    (1 : K) / 4 ≤ 1 - 1 / a - 1 / b := by
  wlog hab : a ≤ b generalizing a b
  · linarith [this (a := b) (b := a) (by linarith) (by rwa [Multiset.pair_comm]) (by omega)]
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ 3 ≤ a) with rfl | rfl | rfl | ha3
  · rcases (by omega : b = 0 ∨ b = 1 ∨ 2 ≤ b) with rfl | rfl | hb2
    · norm_num
    · norm_num at hhyper
    · calc (1 : K) / 4 ≤ 1 - 1 / (0 : ℕ) - 1 / (2 : ℕ) := by norm_num
        _ ≤ 1 - 1 / (0 : ℕ) - 1 / b := by gcongr
  · have hb0 : (0 : K) ≤ 1 / b := by positivity
    have ha1 : (1 : K) / (1 : ℕ) = 1 := by norm_num
    linarith [hb0, ha1]
  · have hb4 : 4 ≤ b := by
      by_contra hb4
      interval_cases b
      · norm_num at hhyper
      · exact hne rfl
    calc (1 : K) / 4 = 1 - 1 / (2 : ℕ) - 1 / (4 : ℕ) := by norm_num
      _ ≤ 1 - 1 / (2 : ℕ) - 1 / b := by gcongr
  · calc (1 : K) / 4 ≤ 1 - 1 / (3 : ℕ) - 1 / (3 : ℕ) := by norm_num
      _ ≤ 1 - 1 / a - 1 / b := by gcongr; omega

/-- Sharp numerical bound for a hyperbolic pair of natural numbers: if `1/a + 1/b < 1`, then
`1/6 ≤ 1 - 1/a - 1/b`. Equality holds precisely at `{2, 3}`. -/
theorem one_div_six_le_hyperbolic_pair_deficit
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b : ℕ} (hhyper : (1 : K) / a + 1 / b < 1) :
    (1 : K) / 6 ≤ 1 - 1 / a - 1 / b := by
  by_cases h : ({a, b} : Multiset ℕ) = {2, 3}
  · exact (pair_deficit_eq_of_multiset_eq h).symm.le
  · exact (by norm_num : (1 : K) / 6 ≤ 1 / 4).trans
      (one_div_four_le_hyperbolic_pair_deficit_of_ne hhyper h)

/-- Any pair `{a, b} ≠ {2, 3}` of natural numbers with `1/a + 1/b < 1` has deficit strictly greater
than `1/6`. -/
theorem one_div_six_lt_hyperbolic_pair_deficit_of_ne
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b : ℕ} (hhyper : (1 : K) / a + 1 / b < 1) (hne : ({a, b} : Multiset ℕ) ≠ {2, 3}) :
    (1 : K) / 6 < 1 - 1 / a - 1 / b :=
  (by norm_num : (1 : K) / 6 < 1 / 4).trans_le
    (one_div_four_le_hyperbolic_pair_deficit_of_ne hhyper hne)

/-- For natural numbers `a, b`, the deficit `1 - 1/a - 1/b` equals `1/6` in a linearly ordered
field if and only if `{a, b} = {2, 3}`. -/
theorem hyperbolic_pair_deficit_eq_one_div_six_iff
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b : ℕ} :
    (1 : K) - 1 / a - 1 / b = 1 / 6 ↔ ({a, b} : Multiset ℕ) = {2, 3} := by
  refine ⟨fun heq ↦ ?_, pair_deficit_eq_of_multiset_eq⟩
  by_contra hne
  have hhyper : (1 : K) / a + 1 / b < 1 := by linarith
  exact (one_div_six_lt_hyperbolic_pair_deficit_of_ne hhyper hne).ne' heq

/-- The pair indices `(2, 3)` attain the `1/6` bound. -/
theorem two_three_deficit_eq_one_div_six [DivisionRing K] [CharZero K] :
    (1 : K) - 1 / 2 - 1 / 3 = 1 / 6 := by
  norm_num

/-- The pair indices `(2, 4)` attain the second-smallest pair deficit `1/4`. -/
theorem two_four_deficit_eq_one_div_four [DivisionRing K] [CharZero K] :
    (1 : K) - 1 / 2 - 1 / 4 = 1 / 4 := by
  norm_num

/-! ### Equality case and spectral gap for hyperbolic triples -/

private theorem triple_multiset_swap₁₂ (a b c : ℕ) :
    ({b, a, c} : Multiset ℕ) = {a, b, c} := by
  simp only [Multiset.insert_eq_cons]
  exact Multiset.cons_swap b a {c}

private theorem triple_multiset_swap₂₃ (a b c : ℕ) :
    ({a, c, b} : Multiset ℕ) = {a, b, c} := by
  simp only [Multiset.insert_eq_cons, Multiset.pair_comm c b]

private theorem triangle_deficit_eq_of_multiset_eq [DivisionRing K] [CharZero K] {a b c : ℕ}
    (h : ({a, b, c} : Multiset ℕ) = {2, 3, 7}) :
    (1 : K) - 1 / a - 1 / b - 1 / c = 1 / 42 := by
  have hsum := congrArg (fun s : Multiset ℕ ↦ (s.map fun n : ℕ ↦ (1 : K) - 1 / n).sum) h
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton, Nat.cast_ofNat] at hsum
  calc (1 : K) - 1 / a - 1 / b - 1 / c
      = (1 - 1 / a) + ((1 - 1 / b) + (1 - 1 / c)) - 1 - 1 := by abel
    _ = (1 - 1 / 2) + ((1 - 1 / 3) + (1 - 1 / 7)) - 1 - 1 := by rw [hsum]
    _ = 1 / 42 := by norm_num

/-- Every triple `{a, b, c} ≠ {2, 3, 7}` of natural numbers satisfying `1/a + 1/b + 1/c < 1` has
deficit `1 - 1/a - 1/b - 1/c` at least `1/24`, read in any linearly ordered field. The bound `1/24`
is attained at `{2, 3, 8}`. -/
theorem one_div_twenty_four_le_hyperbolic_triangle_deficit_of_ne
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : ℕ} (hhyper : (1 : K) / a + 1 / b + 1 / c < 1)
    (hne : ({a, b, c} : Multiset ℕ) ≠ {2, 3, 7}) :
    (1 : K) / 24 ≤ 1 - 1 / a - 1 / b - 1 / c := by
  wlog hab : a ≤ b generalizing a b c
  · linarith [this (a := b) (b := a) (c := c) (by linarith) (by rwa [triple_multiset_swap₁₂])
      (by omega)]
  wlog hbc : b ≤ c generalizing a b c
  · rcases le_total a c with hac | hca
    · linarith [this (a := a) (b := c) (c := b) (by linarith) (by rwa [triple_multiset_swap₂₃])
        hac (by omega)]
    · have hperm : ({c, a, b} : Multiset ℕ) = {a, b, c} :=
        (triple_multiset_swap₁₂ a c b).trans (triple_multiset_swap₂₃ a b c)
      linarith [this (a := c) (b := a) (c := b) (by linarith) (by rwa [hperm]) hca hab]
  -- After handling `a ≤ 1`, a sorted hyperbolic triple other than `(2, 3, 7)` dominates
  -- `(2, 3, 8)`, `(2, 4, 5)` or `(3, 3, 4)` entrywise, with deficits `1/24`, `1/20` and `1/12`.
  rcases (by omega :
      a = 0 ∨ a = 1 ∨ a = 2 ∧ b = 2 ∨ a = 2 ∧ b = 3 ∨ a = 2 ∧ 4 ≤ b ∨ 3 ≤ a) with
    rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hb4⟩ | ha3
  · simp only [Nat.cast_zero, div_zero, zero_add, sub_zero] at hhyper ⊢
    exact (by norm_num : (1 : K) / 24 ≤ 1 / 6).trans
      (one_div_six_le_hyperbolic_pair_deficit hhyper)
  · have hbc0 : (0 : K) ≤ 1 / b + 1 / c := by positivity
    have ha1 : (1 : K) / (1 : ℕ) = 1 := by norm_num
    linarith [hbc0, ha1]
  · norm_num at hhyper
    exact absurd hhyper c.cast_nonneg.not_gt
  · have hc8 : 8 ≤ c := by
      by_contra hc8
      interval_cases c <;> try (norm_num at hhyper; done)
      exact hne rfl
    calc (1 : K) / 24 = 1 - 1 / (2 : ℕ) - 1 / (3 : ℕ) - 1 / (8 : ℕ) := by norm_num
      _ ≤ _ := by gcongr
  · have hc5 : 5 ≤ c := by
      by_contra hc5
      obtain ⟨rfl, rfl⟩ : b = 4 ∧ c = 4 := by omega
      norm_num at hhyper
    calc (1 : K) / 24 ≤ 1 - 1 / (2 : ℕ) - 1 / (4 : ℕ) - 1 / (5 : ℕ) := by norm_num
      _ ≤ _ := by gcongr
  · have hc4 : 4 ≤ c := by
      by_contra hc4
      obtain ⟨rfl, rfl, rfl⟩ : a = 3 ∧ b = 3 ∧ c = 3 := by omega
      norm_num at hhyper
    calc (1 : K) / 24 ≤ 1 - 1 / (3 : ℕ) - 1 / (3 : ℕ) - 1 / (4 : ℕ) := by norm_num
      _ ≤ _ := by gcongr; omega

/-- Any triple `{a, b, c} ≠ {2, 3, 7}` of natural numbers with `1/a + 1/b + 1/c < 1` has deficit
strictly greater than `1/42`. -/
theorem one_div_forty_two_lt_hyperbolic_triangle_deficit_of_ne
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : ℕ} (hhyper : (1 : K) / a + 1 / b + 1 / c < 1)
    (hne : ({a, b, c} : Multiset ℕ) ≠ {2, 3, 7}) :
    (1 : K) / 42 < 1 - 1 / a - 1 / b - 1 / c :=
  (by norm_num : (1 : K) / 42 < 1 / 24).trans_le
    (one_div_twenty_four_le_hyperbolic_triangle_deficit_of_ne hhyper hne)

/-- For natural numbers `a, b, c`, the deficit `1 - 1/a - 1/b - 1/c` equals `1/42` in a linearly
ordered field if and only if `{a, b, c} = {2, 3, 7}`. -/
theorem hyperbolic_triangle_deficit_eq_one_div_forty_two_iff
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b c : ℕ} :
    (1 : K) - 1 / a - 1 / b - 1 / c = 1 / 42 ↔ ({a, b, c} : Multiset ℕ) = {2, 3, 7} := by
  refine ⟨fun heq ↦ ?_, triangle_deficit_eq_of_multiset_eq⟩
  by_contra hne
  have hhyper : (1 : K) / a + 1 / b + 1 / c < 1 := by linarith
  exact (one_div_forty_two_lt_hyperbolic_triangle_deficit_of_ne hhyper hne).ne' heq

/-- The triangle indices `(2, 3, 8)` attain the second-smallest hyperbolic triangle deficit
`1/24`. -/
theorem two_three_eight_deficit_eq_one_div_twenty_four [DivisionRing K] [CharZero K] :
    (1 : K) - 1 / 2 - 1 / 3 - 1 / 8 = 1 / 24 := by
  norm_num

end TauCeti

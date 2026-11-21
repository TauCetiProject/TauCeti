/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Field
import TauCeti.Algebra.BigOperators.Intervals

/-!
# Finite sums of truncations

In a canonically ordered additive monoid with ordered subtraction, a finite family `f` splits
against a second family `g` into the part `min (f x) (g x)` matched by `g` and the excess
`f x - g x` above `g`, so the sums of these two parts add up to the sum of `f`.

For a finite family `c` of natural numbers, the truncated sums `∑ l, min k (c l)` count the boxes
in the first `k` columns of the Young diagram with rows `c l`. Their second differences count
the members of the family in a range: for `p < q`, the combination of the truncated sums at
`p + 1`, `q - 1`, `p` and `q` is the number of members strictly between `p` and `q`. In
particular the truncated sums determine a finite family of positive natural numbers up to
reindexing; this is the counting step in the uniqueness of elementary divisors.

For the uniform range `0, …, S - 1`, twice the truncated sum `2 * ∑ s ∈ range S, min k s` is bounded
below by the quadratic `2 * S * k - k ^ 2 - k` in any ordered ring (with equality for `k ≤ S`), and
summing over `k = r / p` for `r < R` yields a quantitative lower bound in any strictly ordered
field.

## Main results

* `Finset.sum_min_add_sum_tsub`: the matched part and the excess add up to the total.
* `Finset.sum_min_add_sum_min_eq`: the second-difference identity for truncated sums.
* `Fintype.exists_equiv_of_forall_sum_min_eq`: two finite families of positive natural numbers
  with the same truncated sums agree up to a bijection of their index types.
* `Finset.exists_ne_forall_sum_min_lt`: if the sum of a family `a` is at most that of a family
  `b` and, for some `k`, the column count of `b` is strictly smaller than that of `a`, then two
  distinct members `a j ≤ a i` of `a` keep the inequality strict for all `a j ≤ k ≤ a i`.
  Moving a box between these two rows is the key step in generating dominance of partitions by
  box moves.
* `Finset.le_two_mul_sum_range_min`: quadratic lower bound `2 * S * k - k ^ 2 - k ≤
  2 * ∑ s ∈ range S, min k s` in any ordered ring.
* `Finset.le_two_mul_sum_range_min_div`: double-sum lower bound on
  `2 * ∑ r ∈ range R, ∑ s ∈ range S, min (r / p) s` in any strictly ordered field.
-/

public section

namespace Finset

variable {α ι κ : Type*}

/-- The mass of `f` matched by `g` and the mass of `f` above `g` add up to `f`. -/
theorem sum_min_add_sum_tsub {M : Type*} [AddCommMonoid M] [LinearOrder M]
    [CanonicallyOrderedAdd M] [Sub M] [OrderedSub M] (s : Finset ι) (f g : ι → M) :
    ∑ x ∈ s, min (f x) (g x) + ∑ x ∈ s, (f x - g x) = ∑ x ∈ s, f x := by
  simp_rw [← sum_add_distrib, add_comm (min _ _), tsub_add_min]

/-- For `p < q`, the second differences of the truncated sums `∑ l, min k (c l)` at `p` and `q`
count the members of the family `c` strictly between `p` and `q`. -/
theorem sum_min_add_sum_min_eq (u : Finset α) (c : α → ℕ) {p q : ℕ} (hpq : p < q) :
    ∑ l ∈ u, min (p + 1) (c l) + ∑ l ∈ u, min (q - 1) (c l) =
      ∑ l ∈ u, min p (c l) + ∑ l ∈ u, min q (c l) + #{l ∈ u | p < c l ∧ c l < q} := by
  rw [card_filter, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun l _ => by split_ifs <;> omega

/-- A pair of rows realising a strict inequality of column counts. Let `a` and `b` be finite
families of natural numbers, the sum of `a` being at most the sum of `b`, such that for some `k`
the column count
`∑ min k (b l)` of `b` is strictly smaller than the column count `∑ min k (a l)` of `a`.
Then `a` has two distinct members `a j ≤ a i` such that the inequality is strict for every `k`
with `a j ≤ k ≤ a i`. Moving one box from row `j` to row `i` lowers the column count of `a`
by one exactly for `a j ≤ k ≤ a i`. -/
theorem exists_ne_forall_sum_min_lt {s : Finset ι} {t : Finset κ} {a : ι → ℕ} {b : κ → ℕ}
    (hsum : ∑ l ∈ s, a l ≤ ∑ l ∈ t, b l)
    (hlt : ∃ k, ∑ l ∈ t, min k (b l) < ∑ l ∈ s, min k (a l)) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ a j ≤ a i ∧
      ∀ k, a j ≤ k → k ≤ a i → ∑ l ∈ t, min k (b l) < ∑ l ∈ s, min k (a l) := by
  classical
  obtain ⟨k₀, hk₀⟩ := hlt
  -- From the largest member of either family on, the column counts are the sums.
  have hbig : ∀ k, s.sup a ⊔ t.sup b ≤ k →
      ∑ l ∈ s, min k (a l) ≤ ∑ l ∈ t, min k (b l) := by
    intro k hk
    rw [sum_congr rfl fun l hl => min_eq_right ((le_sup hl).trans (le_sup_left.trans hk)),
      sum_congr rfl fun l hl => min_eq_right ((le_sup hl).trans (le_sup_right.trans hk))]
    exact hsum
  -- `p < k₀ < q` are the nearest arguments around `k₀` where the column count of `a` is at most
  -- that of `b`.
  have hex : ∃ k, k₀ ≤ k ∧ ∑ l ∈ s, min k (a l) ≤ ∑ l ∈ t, min k (b l) :=
    ⟨max k₀ (s.sup a ⊔ t.sup b), le_max_left _ _, hbig _ (le_max_right _ _)⟩
  let p := Nat.findGreatest (fun k => ∑ l ∈ s, min k (a l) ≤ ∑ l ∈ t, min k (b l)) k₀
  let q := Nat.find hex
  have hp : ∑ l ∈ s, min p (a l) ≤ ∑ l ∈ t, min p (b l) :=
    Nat.findGreatest_spec (P := fun k => ∑ l ∈ s, min k (a l) ≤ ∑ l ∈ t, min k (b l))
      (Nat.zero_le k₀) (by simp)
  have hq : ∑ l ∈ s, min q (a l) ≤ ∑ l ∈ t, min q (b l) := (Nat.find_spec hex).2
  have hpk₀ : p < k₀ := lt_of_le_of_ne (Nat.findGreatest_le k₀) fun h => by
    rw [h] at hp
    exact hk₀.not_ge hp
  have hk₀q : k₀ < q := lt_of_le_of_ne (Nat.find_spec hex).1 fun h => by
    rw [← h] at hq
    exact hk₀.not_ge hq
  -- Strictly between `p` and `q` the inequality is strict.
  have hrun : ∀ k, p < k → k < q → ∑ l ∈ t, min k (b l) < ∑ l ∈ s, min k (a l) := by
    intro k hpk hkq
    by_contra! hge
    rcases le_total k k₀ with hk | hk
    · exact Nat.findGreatest_is_greatest hpk hk hge
    · exact Nat.find_min hex hkq ⟨hk, hge⟩
  -- Comparing second differences at `p` and `q` gives two members of `a` strictly between them.
  have h₁ := hrun (p + 1) (Nat.lt_succ_self p) (by omega)
  have h₂ := hrun (q - 1) (by omega) (by omega)
  have hs := sum_min_add_sum_min_eq s a (hpk₀.trans hk₀q)
  have ht := sum_min_add_sum_min_eq t b (hpk₀.trans hk₀q)
  have htwo : 1 < #{l ∈ s | p < a l ∧ a l < q} := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp htwo
  rw [mem_filter] at hx hy
  have hint (i j : ι) (hi : p < a i ∧ a i < q) (hj : p < a j ∧ a j < q) :
      ∀ k, a j ≤ k → k ≤ a i → ∑ l ∈ t, min k (b l) < ∑ l ∈ s, min k (a l) :=
    fun k hjk hki => hrun k (by omega) (by omega)
  rcases le_total (a y) (a x) with hyx | hxy'
  · exact ⟨x, hx.1, y, hy.1, hxy, hyx, hint x y hx.2 hy.2⟩
  · exact ⟨y, hy.1, x, hx.1, hxy.symm, hxy', hint y x hy.2 hx.2⟩

/-- Quadratic lower bound on the truncated range sum:
`2 * S * k - k ^ 2 - k ≤ 2 * ∑ s ∈ range S, min k s` in any ordered ring
(with equality whenever `k ≤ S`). -/
theorem le_two_mul_sum_range_min {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    (S k : ℕ) :
    2 * (S : R) * k - (k : R) ^ 2 - k ≤ 2 * ∑ s ∈ range S, ((min k s : ℕ) : R) := by
  have hZ : 2 * (S : ℤ) * k - (k : ℤ) ^ 2 - k ≤ 2 * ∑ s ∈ range S, ((min k s : ℕ) : ℤ) := by
    rcases le_or_gt k S with hkS | hSk
    · conv_rhs => rw [(Nat.add_sub_of_le hkS).symm, sum_range_add]
      rw [mul_add, sum_congr rfl fun s hs ↦ by rw [min_eq_right (Nat.le_of_lt (mem_range.mp hs))],
        mul_comm 2 (∑ s ∈ range k, (s : ℤ)), sum_range_natCast_mul_two,
        sum_congr rfl fun x _ ↦ by rw [min_eq_left (Nat.le_add_right k x)],
        sum_const, card_range, nsmul_eq_mul, Nat.cast_sub hkS]
      exact le_of_eq (by ring)
    · rw [sum_congr rfl fun s hs ↦ by
          rw [min_eq_right (Nat.le_of_lt ((mem_range.mp hs).trans hSk))],
        mul_comm 2 (∑ s ∈ range S, (s : ℤ)), sum_range_natCast_mul_two]
      have hSkZ : (S : ℤ) ≤ k := by exact_mod_cast hSk.le
      nlinarith [sq_nonneg ((k : ℤ) - S), hSkZ]
  set d : ℕ := (2 * ∑ s ∈ range S, ((min k s : ℕ) : ℤ) -
    (2 * (S : ℤ) * k - (k : ℤ) ^ 2 - k)).toNat
  have hd : 2 * ∑ s ∈ range S, ((min k s : ℕ) : ℤ) =
      (2 * (S : ℤ) * k - (k : ℤ) ^ 2 - k) + (d : ℤ) := by omega
  have hR := congrArg (Int.cast (R := R)) hd
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_sum,
    Int.cast_natCast, Int.cast_ofNat] at hR
  rw [hR]
  exact le_add_of_nonneg_right (Nat.cast_nonneg d)

/-- Lower bound on the double truncated sum `2 * ∑ r ∈ range R, ∑ s ∈ range S, min (r / p) s`
in any strictly ordered field `K`. -/
theorem le_two_mul_sum_range_min_div {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (p R S : ℕ) :
    (R : K) ^ 2 * S / p - (R : K) * S / p - (R : K) ^ 2 / p - 2 * R * S - (R : K) ^ 3 / p ^ 2 ≤
      2 * ∑ r ∈ range R, ∑ s ∈ range S, ((min (r / p) s : ℕ) : K) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp only [Nat.cast_zero, div_zero, zero_sub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero, Nat.div_zero, Nat.zero_min, sum_const_zero, mul_zero]
    have hRS : (0 : K) ≤ 2 * R * S := by positivity
    linarith
  have hpK : (0 : K) < p := by exact_mod_cast hp
  have hr_term (r : ℕ) (hr : r ∈ range R) :
      2 * (S : K) * r / p - 2 * S - (R : K) ^ 2 / p ^ 2 - (R : K) / p ≤
        2 * ∑ s ∈ range S, ((min (r / p) s : ℕ) : K) := by
    set k := r / p
    have hk_le : (k : K) ≤ (R : K) / p :=
      (le_div_iff₀ hpK).mpr (by exact_mod_cast (Nat.div_mul_le_self r p).trans (mem_range.mp hr).le)
    have hk_ge : (r : K) / p - 1 ≤ k := by
      rw [sub_le_iff_le_add, div_le_iff₀ hpK]
      exact_mod_cast (by rw [add_mul, one_mul]; exact (Nat.lt_div_mul_add hp).le : r ≤ (k + 1) * p)
    have hksq : (k : K) ^ 2 ≤ (R : K) ^ 2 / p ^ 2 := by rw [← div_pow]; gcongr
    have h2Sk : 2 * (S : K) * r / p - 2 * S ≤ 2 * (S : K) * k := by
      have hmul := mul_le_mul_of_nonneg_left hk_ge (by positivity : (0 : K) ≤ 2 * S)
      have hnorm : 2 * (S : K) * ((r : K) / p - 1) = 2 * (S : K) * r / p - 2 * S := by ring
      linarith
    linarith [le_two_mul_sum_range_min (R := K) S k]
  have hsum_r : ∑ r ∈ range R, (2 * (S : K) * r / p) = (S : K) * ((R : K) * (R - 1)) / p := by
    calc ∑ r ∈ range R, (2 * (S : K) * r / p)
        = ∑ r ∈ range R, (2 * (S : K) / p) * (r : K) :=
          sum_congr rfl fun r _ ↦ by ring
      _ = (2 * (S : K) / p) * ∑ r ∈ range R, (r : K) := (mul_sum ..).symm
      _ = (S : K) * ((R : K) * (R - 1)) / p := by rw [sum_range_natCast]; ring
  rw [mul_sum]
  calc (R : K) ^ 2 * S / p - (R : K) * S / p - (R : K) ^ 2 / p - 2 * R * S - (R : K) ^ 3 / p ^ 2
      = (S : K) * ((R : K) * (R - 1)) / p - (R : K) * (2 * S) -
          (R : K) * ((R : K) ^ 2 / p ^ 2) - (R : K) * ((R : K) / p) := by ring
    _ = ∑ r ∈ range R, (2 * (S : K) * r / p - 2 * S - (R : K) ^ 2 / p ^ 2 - (R : K) / p) := by
        simp only [sub_eq_add_neg, sum_add_distrib, sum_neg_distrib, sum_const, card_range,
          nsmul_eq_mul, hsum_r]
    _ ≤ ∑ r ∈ range R, 2 * ∑ s ∈ range S, ((min (r / p) s : ℕ) : K) := sum_le_sum hr_term

end Finset

namespace Fintype

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Truncated sums determine a family of positive naturals up to reindexing.** If two finite
families `e` and `e'` of positive natural numbers have the same truncated sums
`∑ min k (e i) = ∑ min k (e' j)` for every `k`, then they agree after a bijection of their index
types. Positivity is needed: members equal to `0` contribute nothing to any truncated sum. -/
theorem exists_equiv_of_forall_sum_min_eq {e : ι → ℕ} {e' : κ → ℕ} (he : ∀ i, 0 < e i)
    (he' : ∀ j, 0 < e' j) (h : ∀ k, ∑ i, min k (e i) = ∑ j, min k (e' j)) :
    ∃ σ : ι ≃ κ, ∀ i, e i = e' (σ i) := by
  classical
  have hcard (k : ℕ) : Fintype.card {i // e i = k} = Fintype.card {j // e' j = k} := by
    cases k with
    | zero =>
      have : IsEmpty {i // e i = 0} := ⟨fun i ↦ (he i.val).ne' i.property⟩
      have : IsEmpty {j // e' j = 0} := ⟨fun j ↦ (he' j.val).ne' j.property⟩
      simp
    | succ k =>
      -- The multiplicity of `k + 1` is a second difference of `k ↦ ∑ i, min k (e i)`.
      have hk (n : ℕ) : k < n ∧ n < k + 1 + 1 ↔ n = k + 1 := by omega
      have h₁ := Finset.sum_min_add_sum_min_eq Finset.univ e (by omega : k < k + 1 + 1)
      have h₂ := Finset.sum_min_add_sum_min_eq Finset.univ e' (by omega : k < k + 1 + 1)
      simp only [hk, Nat.add_sub_cancel] at h₁ h₂
      rw [Fintype.card_subtype, Fintype.card_subtype]
      have := h k
      have := h (k + 1)
      have := h (k + 1 + 1)
      omega
  exact ⟨.ofFiberEquiv fun k ↦ Fintype.equivOfCardEq (hcard k),
    fun i ↦ (Equiv.ofFiberEquiv_map _ i).symm⟩

end Fintype

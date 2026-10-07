/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.Order.SuccPred.IntervalSucc

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Basic results about finite ordinal types

This file collects elementary facts about finite ordinal types, including the classification of
permutations of `Fin 2`, sums of reversed indices, indicator sums indexed by `Fin n`, the final
value of a partial product, and the cyclic index arithmetic of `Fin 3`.

`Fintype.sum_ite_eq` evaluates a sum whose indicator compares two elements of the index type.
When the comparison is instead between a natural number and the `Fin.val` of the index — as it is
whenever a family is indexed by `ℕ` and summed over `Fin n` — the index may fall outside the
range, so the value is a `dite` rather than a plain application.

## Main results

* `TauCeti.perm_fin_two_eq_one_or_swap`: every permutation of `Fin 2` is the identity or the
  transposition.
* `TauCeti.forall_cons_swap_eq_zero_iff`: vanishing of the final coordinates after swapping
  coordinate zero with coordinate `d` in a vector built with `Fin.cons`.
* `Fin.rev_finRotate_rev` and `Fin.rev_finRotate_symm`: reversal carries forward rotation to
  backward rotation and conversely.
* `Fin.finRotate_rev_finRotate_rev`: negation modulo `n`, written as `i ↦ finRotate n i.rev`, is
  an involution.
* `Fin.coe_finRotate_pow`: a power of the rotation `finRotate n` adds its exponent modulo `n`.
* `Finset.sum_range_const_sub_succ`: the sum of a reversed initial segment of natural numbers.
* `Fin.sum_rev_castLE`: the sum of the values of a reversed embedded finite ordinal.
* `Fin.castSucc_add_one_of_ne_last`, `Fin.castSucc_sub_one_of_ne_zero`: how `Fin.castSucc`
  interacts with the cyclic successor and predecessor.
* `Fin.zero_sub_one_eq_last`: subtracting one from `0` gives the last index.
* `Fin.eq_castSucc_last_or_eq_last`: an index `≥ n` of `Fin (n + 2)` is the penultimate or the
  last one.
* `Fin.last_ne_zero`, `Fin.castSucc_last_ne_zero`, `Fin.castSucc_last_ne_one`, `Fin.last_ne_one`:
  the last and penultimate indices differ from `0` and `1` in the nondegenerate cases.
* `Fin.sum_univ_eq_zero_add_last_add_sum_erase`: a sum over `Fin (n + 1)` with its first and last
  summands split off.
* `Fin.natCast_ne_zero`: the cast of a natural number `0 < a < n` to `Fin n` (under
  `open Fin.NatCast`) is nonzero.
* `Fin.predAbove_succ_succAbove`: `Fin.predAbove p` inverts `p.succ.succAbove`, the
  counterpart of Mathlib's `Fin.predAbove_succAbove` for `p.castSucc.succAbove`.
* `Fin.val_succAbove`: the value of `p.succAbove i`, read off the comparison of `i` with `p`.
* `Fin.finRotate_succ_eq_succ_succAbove` and `Fin.finRotate_succ_succAbove_of_ne`: the cyclic
  successor of `Fin (n + 1)` against the embeddings `Fin.succ` and `i.succ.succAbove` of `Fin n`,
  as used when a new entry is inserted into a cyclic sequence.
* `Fin.succAbove_adjacent_cases`: the positions `p` of `Fin (n + 1)` cyclically adjacent to
  `p.succAbove i`.
* `Fin.swap_castSucc_succ_succAbove`: the transposition of `k.castSucc` and `k.succ` exchanges the
  embeddings of `Fin n` skipping either of them.
* `Fin.card_filter_prod_succAbove`: a count of pairs in `Fin (n + 1)` split at a point in each
  coordinate.
* `Fin.val_orderSucc_of_lt` and `Fin.orderSucc_eq_self_of_not_lt`: the order successor of `Fin n`
  read off the value, below and at the top element.  Mathlib's `Fin.orderSucc_castSucc` and
  `Fin.orderSucc_last` state the same thing in the `castSucc`/`last` normal form; these are the
  versions keyed on the inequality `i + 1 < n`.
* `Fin.partialProd_last`: the final partial product is the product of all the entries.
* `Fin.partialSum_last`: the final partial sum is the sum of all the entries.
* `TauCeti.add_one_ne_self`: adding one in `Fin n` is nontrivial when `2 ≤ n`.
* `TauCeti.add_one_add_one_ne_self`: adding one twice in `Fin n` is nontrivial when `3 ≤ n`;
  `TauCeti.sub_one_ne_self` and `TauCeti.add_one_ne_sub_one` are the companions for subtraction.
* `TauCeti.apply_eq_apply_zero_of_add_one`: a function on `Fin (n + 1)` unchanged by adding one
  is constant.
* `TauCeti.eq_add_one_or_eq_add_two_fin_three`: a distinct index of `Fin 3` is one of the two
  shifts of the other.
* `TauCeti.add_one_add_one_fin_three`, `TauCeti.add_one_add_two_fin_three`,
  `TauCeti.add_two_add_one_fin_three` and `TauCeti.add_two_add_two_fin_three`: the shifts by `1`
  and `2` compose cyclically in `Fin 3`.
* `TauCeti.sum_fin_three_rotate`: a sum over `Fin 3` read off starting from an arbitrary index.
* `TauCeti.neg_one_pow_val_add_one`: for `n` even, adding one in `Fin n` flips the sign `(-1) ^ ·`
  read off the value.
* `TauCeti.sum_ite_val_add`: a sum against the indicator of `b = k + j` picks out the summand at
  `b - j`, or vanishes when there is no such index.
* `TauCeti.exists_foldl_eq_of_parent`: a decreasing parent table gives paths from its root.
* `TauCeti.not_mem_Ioo_castSucc_succ`: a monotone `Fin` family has no value strictly between
  consecutive entries.
* `TauCeti.exists_mem_Icc_castSucc_succ`: consecutive closed intervals cover the interval
  between the first and last values of a monotone `Fin` family.
-/

public section

open scoped BigOperators

namespace Finset

/-- The sum of the first `k` entries of the reversed range `N - 1, ..., 0`. -/
theorem sum_range_const_sub_succ (N k : ℕ) (hk : k ≤ N) :
    Finset.sum (Finset.range k) (fun x => N - (x + 1)) =
      k.choose 2 + k * (N - k) := by
  calc
    Finset.sum (Finset.range k) (fun x => N - (x + 1)) =
        Finset.sum (Finset.range k) (fun x => (N - k) + (k - 1 - x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxk := Finset.mem_range.mp hx
      omega
    _ = k * (N - k) + Finset.sum (Finset.range k) (fun x => k - 1 - x) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = k * (N - k) + Finset.sum (Finset.range k) (fun x => x) := by
      rw [Finset.sum_range_reflect (fun x => x) k]
    _ = k.choose 2 + k * (N - k) := by
      rw [Finset.sum_range_id, Nat.choose_two_right]
      omega

end Finset

namespace Fin

/-- The sum of the values in the first `k` positions of the reversed finite ordinal `Fin N`. -/
theorem sum_rev_castLE (N k : ℕ) (hk : k ≤ N) :
    (∑ i : Fin k, (Fin.rev (Fin.castLE hk i) : ℕ)) =
      k.choose 2 + k * (N - k) := by
  rw [Finset.sum_fin_eq_sum_range]
  simp only [Fin.rev, Fin.castLE]
  calc
    Finset.sum (Finset.range k)
        (fun x => if h : x < k then N - (x + 1) else 0) =
        Finset.sum (Finset.range k) (fun x => N - (x + 1)) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.mem_range.mp hx]
    _ = _ := Finset.sum_range_const_sub_succ N k hk

/-- The final partial product is the product of all the entries. -/
@[to_additive /-- The final partial sum is the sum of all the entries. -/]
theorem partialProd_last {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin n → M) :
    Fin.partialProd f (Fin.last n) = ∏ i, f i := by
  rw [Fin.partialProd, Fin.val_last]
  rw [(List.take_eq_self_iff _).mpr (by simp), Fin.prod_ofFn]

/-- Conjugating forward rotation of a finite ordinal by reversal gives backward rotation. -/
@[simp]
theorem rev_finRotate_rev {n : ℕ} (i : Fin n) :
    haveI := i.neZero
    Fin.rev (Fin.rev i + 1) = (finRotate n).symm i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [finRotate_symm_apply, ← Fin.last_sub, ← Fin.last_sub]
    have hlast : Fin.last n = (-1 : Fin (n + 1)) := by
      apply Fin.ext
      simp
    simp [sub_eq_add_neg, hlast, add_comm, add_left_comm]

/-- Reversal carries backward rotation of a finite ordinal to forward rotation. -/
@[simp]
theorem rev_finRotate_symm {n : ℕ} (i : Fin n) :
    haveI := i.neZero
    Fin.rev (i - 1) = finRotate n (Fin.rev i) := by
  apply Fin.rev_injective
  simp only [Fin.rev_rev]
  simpa only [finRotate_apply, finRotate_symm_apply] using (rev_finRotate_rev i).symm

/-- The map `i ↦ finRotate n i.rev`, which is negation modulo `n`, is an involution. -/
theorem finRotate_rev_finRotate_rev {n : ℕ} (i : Fin n) :
    finRotate n (finRotate n i.rev).rev = i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have := i.isLt
    ext
    simp only [coe_finRotate, Fin.ext_iff, Fin.val_last, Fin.val_rev]
    split_ifs <;> omega

/-- The value of a power of the cyclic permutation `finRotate n`: it adds `k` modulo `n`. -/
theorem coe_finRotate_pow {n : ℕ} (k : ℕ) (c : Fin n) :
    ((finRotate n ^ k) c : ℕ) = (c + k) % n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt c.isLt]
  | succ k ih =>
    have : NeZero n := ⟨Nat.pos_iff_ne_zero.mp c.pos⟩
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add, ih, Fin.val_one',
      ← Nat.add_mod, ← add_assoc]

/-- Collapsing the hole opened immediately after `p` back onto `p` inverts the embedding
`p.succ.succAbove`. -/
@[simp]
theorem predAbove_succ_succAbove {n : ℕ} (p i : Fin n) : p.predAbove (p.succ.succAbove i) = i := by
  rcases le_or_gt i p with h | h
  · rw [succAbove_succ_of_le _ _ h, predAbove_castSucc_of_le _ _ h]
  · rw [succAbove_succ_of_lt _ _ h, predAbove_succ_of_le _ _ h.le]

/-- The value of `p.succAbove i`: the value of `i` below `p`, and one more from `p` on. -/
theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    (p.succAbove i : ℕ) = if (i : ℕ) < p then (i : ℕ) else (i : ℕ) + 1 := by
  unfold succAbove
  split_ifs <;> simp_all [lt_def]

/-- The cyclic successor of `i.succ` in `Fin (n + 1)` is the cyclic successor of `i` in `Fin n`,
read through the embedding `i.succ.succAbove` that skips `i.succ`. -/
theorem finRotate_succ_eq_succ_succAbove {n : ℕ} (i : Fin n) :
    finRotate (n + 1) i.succ = i.succ.succAbove (finRotate n i) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  have := i.isLt
  ext
  simp only [succAbove]
  split_ifs <;> simp only [lt_def, val_castSucc, val_succ, coe_finRotate, Fin.ext_iff,
    val_last] at * <;> split_ifs at * <;> omega

/-- Away from `i`, the embedding `i.succ.succAbove : Fin n → Fin (n + 1)`, which skips `i.succ`,
commutes with the cyclic successors. -/
theorem finRotate_succ_succAbove_of_ne {n : ℕ} {i k : Fin n} (hk : k ≠ i) :
    finRotate (n + 1) (i.succ.succAbove k) = i.succ.succAbove (finRotate n k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  rw [Ne, Fin.ext_iff] at hk
  have := k.isLt
  have := i.isLt
  ext
  simp only [succAbove]
  split_ifs <;> simp only [lt_def, val_castSucc, val_succ, coe_finRotate, Fin.ext_iff,
    val_last] at * <;> split_ifs at * <;> omega

/-- A position `p` of `Fin (n + 1)` cyclically adjacent to `p.succAbove i` is `i.castSucc` or
`i.succ`, or wraps around: `p` is last and `p.succAbove i` is `0`, or `p` is `0` and
`p.succAbove i` is last. -/
theorem succAbove_adjacent_cases {n : ℕ} {p : Fin (n + 1)} {i : Fin n}
    (h : finRotate (n + 1) p = p.succAbove i ∨ finRotate (n + 1) (p.succAbove i) = p) :
    p = i.castSucc ∨ p = i.succ ∨ (p = last n ∧ i.castSucc = 0) ∨ (p = 0 ∧ i.succ = last n) := by
  have hv := val_succAbove p i
  have := i.isLt
  simp only [Fin.ext_iff, coe_finRotate, val_last, val_zero, val_castSucc, val_succ] at h hv ⊢
  split_ifs at h hv <;> omega

/-- The transposition of `k.castSucc` and `k.succ` carries the embedding `k.castSucc.succAbove`,
which skips `k.castSucc`, to the embedding `k.succ.succAbove`, which skips `k.succ`. -/
theorem swap_castSucc_succ_succAbove {n : ℕ} (k i : Fin n) :
    Equiv.swap k.castSucc k.succ (k.castSucc.succAbove i) = k.succ.succAbove i := by
  rcases eq_or_ne i k with rfl | hik
  · simp
  have h : k.castSucc.succAbove i = k.succ.succAbove i := by
    ext
    simp only [val_succAbove, val_castSucc, val_succ]
    rw [Ne, Fin.ext_iff] at hik
    split_ifs <;> omega
  rw [h, Equiv.swap_apply_of_ne_of_ne]
  · rw [← succAbove_succ_self]
    exact fun h' ↦ hik (succAbove_right_injective h')
  · rw [← h, ← succAbove_castSucc_self]
    exact fun h' ↦ hik (succAbove_right_injective h')

/-- A count of pairs in `Fin (n + 1)`, split at `a` in the first coordinate and at `b` in the
second: the pair `(a, b)`, the pairs with exactly one coordinate at its split point, and the pairs
embedded by `a.succAbove` and `b.succAbove`. -/
theorem card_filter_prod_succAbove {n : ℕ} (P : Fin (n + 1) × Fin (n + 1) → Prop)
    [DecidablePred P] (a b : Fin (n + 1)) :
    (Finset.univ.filter P).card =
      (if P (a, b) then 1 else 0) +
        (Finset.univ.filter fun j : Fin n => P (a, b.succAbove j)).card +
        (Finset.univ.filter fun i : Fin n => P (a.succAbove i, b)).card +
        (Finset.univ.filter fun p : Fin n × Fin n =>
          P (a.succAbove p.1, b.succAbove p.2)).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [sum_univ_succAbove _ a]
  simp_rw [sum_univ_succAbove _ b]
  rw [Finset.sum_add_distrib, ← add_assoc]

/-- Adding one commutes with `Fin.castSucc` away from the last index. -/
theorem castSucc_add_one_of_ne_last {n : ℕ} {i : Fin (n + 1)} (hi : i ≠ last n) :
    castSucc (i + 1) = castSucc i + 1 := by
  simp [Fin.ext_iff, val_add_one, hi]

/-- Subtracting one commutes with `Fin.castSucc` away from `0`. -/
theorem castSucc_sub_one_of_ne_zero {n : ℕ} {i : Fin (n + 1)} (hi : i ≠ 0) :
    castSucc (i - 1) = castSucc i - 1 := by
  simp [Fin.ext_iff, coe_sub_one, hi]

/-- Subtracting one from `0` gives the last index. -/
theorem zero_sub_one_eq_last {n : ℕ} : (0 : Fin (n + 1)) - 1 = last n :=
  (eq_sub_of_add_eq (last_add_one n)).symm

/-- The last index of `Fin (n + 1)` is not `0` when `n ≠ 0`. -/
theorem last_ne_zero {n : ℕ} (hn : n ≠ 0) : last n ≠ (0 : Fin (n + 1)) :=
  mt last_eq_zero_iff.1 hn

/-- The penultimate index of `Fin (n + 2)` is not `0` when `n ≠ 0`. -/
theorem castSucc_last_ne_zero {n : ℕ} (hn : n ≠ 0) : castSucc (last n) ≠ (0 : Fin (n + 2)) :=
  castSucc_ne_zero_iff.2 (last_ne_zero hn)

/-- The penultimate index of `Fin (n + 2)` is not `1` when `n ≠ 1`. -/
theorem castSucc_last_ne_one {n : ℕ} (hn : n ≠ 1) : castSucc (last n) ≠ (1 : Fin (n + 2)) :=
  ne_of_val_ne (by simp only [val_castSucc, val_last, val_one]; omega)

/-- The last index of `Fin (n + 2)` is not `1` when `n ≠ 0`. -/
theorem last_ne_one {n : ℕ} (hn : n ≠ 0) : last (n + 1) ≠ (1 : Fin (n + 2)) :=
  ne_of_val_ne (by simp only [val_last, val_one]; omega)

/-- An index of `Fin (n + 2)` that is at least `n` is the penultimate or the last one. -/
theorem eq_castSucc_last_or_eq_last {n : ℕ} {i : Fin (n + 2)} (hi : n ≤ i.val) :
    i = castSucc (last n) ∨ i = last (n + 1) := by
  have := i.isLt
  simp only [Fin.ext_iff, val_castSucc, val_last]
  omega

/-- A sum over `Fin (n + 1)` with the first and the last summands split off. -/
theorem sum_univ_eq_zero_add_last_add_sum_erase {n : ℕ} {M : Type*} [AddCommMonoid M]
    (hn : n ≠ 0)
    (f : Fin (n + 1) → M) :
    ∑ i, f i = f 0 + f (last n) + ∑ i ∈ (Finset.univ.erase 0).erase (last n), f i := by
  rw [add_assoc, Finset.add_sum_erase _ _
    (Finset.mem_erase.2 ⟨mt last_eq_zero_iff.1 hn, Finset.mem_univ _⟩),
    Finset.add_sum_erase _ _ (Finset.mem_univ 0)]

open Fin.NatCast in
/-- The cast of a natural number `0 < a < n` to `Fin n` is nonzero. -/
theorem natCast_ne_zero {n a : ℕ} [NeZero n] (ha : a ≠ 0) (han : a < n) : (a : Fin n) ≠ 0 :=
  natCast_eq_zero.not.2 (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero ha) han)

/-- Below the top element of `Fin n`, the order successor increments the value. -/
theorem val_orderSucc_of_lt {n : ℕ} {i : Fin n} (h : (i : ℕ) + 1 < n) :
    ((Order.succ i : Fin n) : ℕ) = (i : ℕ) + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j : Fin m, i = j.castSucc := ⟨⟨(i : ℕ), by omega⟩, by ext; simp⟩
  simp

/-- At the top element of `Fin n` the order successor is that element itself. -/
theorem orderSucc_eq_self_of_not_lt {n : ℕ} {i : Fin n} (h : ¬(i : ℕ) + 1 < n) :
    (Order.succ i : Fin n) = i :=
  IsMax.succ_eq fun b _ => Fin.le_def.2 (by have := b.isLt; have := i.isLt; omega)

end Fin

namespace TauCeti

/-- After swapping coordinates zero and `d`, the entries of `Fin.cons a y` at indices at least
`d` vanish exactly when `a` and the entries of `y` at indices at least `d` vanish. -/
theorem forall_cons_swap_eq_zero_iff {α : Type*} [Zero α] {n d : ℕ}
    (hd : d ≤ n) (a : α) (y : Fin n → α) :
    (∀ i : Fin (n + 1), d ≤ i.val →
      (Fin.cons a y : Fin (n + 1) → α) (Equiv.swap 0 ⟨d, by omega⟩ i) = 0) ↔
      a = 0 ∧ ∀ j : Fin n, d ≤ j.val → y j = 0 := by
  constructor
  · intro h
    refine ⟨?_, fun j hj ↦ ?_⟩
    · simpa using h ⟨d, by omega⟩ (by simp)
    · have h0 : j.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero j
      have hd' : j.succ ≠ (⟨d, by omega⟩ : Fin (n + 1)) := by
        intro heq
        have := congrArg Fin.val heq
        simp only [Fin.val_succ] at this
        omega
      simpa [Equiv.swap_apply_of_ne_of_ne h0 hd'] using h j.succ (by simp; omega)
  · rintro ⟨ha, hy⟩ i hi
    by_cases hid : i = ⟨d, by omega⟩
    · rw [hid, Equiv.swap_apply_right, Fin.cons_zero]
      exact ha
    have hi0 : i ≠ 0 := by
      intro h0
      subst i
      have : d = 0 := by simpa using hi
      apply hid
      ext
      simp [this]
    rw [Equiv.swap_apply_of_ne_of_ne hi0 hid]
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (i := i) hi0
    have hne : j.val + 1 ≠ d := fun h ↦ hid (Fin.ext h)
    exact hy j (by simp only [Fin.val_succ] at hi; omega)

/-- A decreasing parent table gives a word carrying its root to every vertex. -/
theorem exists_foldl_eq_of_parent {n : ℕ} {J : Type*}
    (step : Fin (n + 1) → J → Fin (n + 1))
    (parent : Fin n → Fin (n + 1)) (edge : Fin n → J)
    (hparent : ∀ a, (parent a : ℕ) < (a.succ : ℕ))
    (hstep : ∀ a, step (parent a) (edge a) = a.succ) (a : Fin (n + 1)) :
    ∃ l : List J, l.foldl step 0 = a := by
  have aux : ∀ m, ∀ hm : m < n + 1,
      ∃ l : List J, l.foldl step 0 = (⟨m, hm⟩ : Fin (n + 1)) := by
    intro m hm
    induction m using Nat.strong_induction_on with
    | h m ih =>
        by_cases hzero : m = 0
        · subst m
          exact ⟨[], rfl⟩
        · let c : Fin n := ⟨m - 1, by omega⟩
          have hsucc : c.succ = (⟨m, hm⟩ : Fin (n + 1)) := by
            apply Fin.ext
            simp [c]
            omega
          obtain ⟨l, hl⟩ := ih (parent c)
            (by
              have hlt := hparent c
              have hval : (c.succ : ℕ) = m := congrArg Fin.val hsucc
              rwa [hval] at hlt)
            (parent c).isLt
          refine ⟨l ++ [edge c], ?_⟩
          rw [List.foldl_append, hl]
          simpa only [List.foldl_cons, List.foldl_nil, hstep] using hsucc
  exact aux a a.isLt

open Set

/-- No value of a monotone `Fin` family lies strictly between consecutive entries. -/
theorem not_mem_Ioo_castSucc_succ {β : Type*} [Preorder β] {n : ℕ} (a : Fin (n + 1) → β)
    (ha : Monotone a) (i : Fin n) (k : Fin (n + 1)) :
    a k ∉ Set.Ioo (a i.castSucc) (a i.succ) := by
  intro hk
  by_cases hki : k ≤ i.castSucc
  · exact (not_lt_of_ge (ha hki)) hk.1
  · have hik : i.succ ≤ k := by
      simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc] at hki ⊢
      omega
    exact (not_lt_of_ge (ha hik)) hk.2

/-- A point between the first and last values of a monotone `Fin` family lies between
consecutive values. -/
theorem exists_mem_Icc_castSucc_succ {β : Type*} [LinearOrder β] {n : ℕ}
    (a : Fin (n + 1) → β) (ha : Monotone a)
    (hn : n ≠ 0) {x : β} (hx : x ∈ Set.Icc (a 0) (a (Fin.last n))) :
    ∃ i : Fin n, x ∈ Set.Icc (a i.castSucc) (a i.succ) := by
  rcases hx.1.eq_or_lt with h | h
  · refine ⟨⟨0, Nat.pos_of_ne_zero hn⟩, ?_⟩
    rw [← h]
    exact ⟨le_rfl, ha (Fin.zero_le _)⟩
  · have hx' : x ∈ ⋃ j ∈ Ico 0 (Fin.last n), Ioc (a j) (a (Order.succ j)) := by
      rw [ha.biUnion_Ico_Ioc_map_succ]
      exact ⟨h, hx.2⟩
    simp only [mem_iUnion, mem_Ico] at hx'
    obtain ⟨j, ⟨-, hj⟩, hxj⟩ := hx'
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj.ne
    exact ⟨i, Ioc_subset_Icc_self (by simpa only [Fin.orderSucc_castSucc] using hxj)⟩

/-- **Adding one in `Fin n` never returns to the same element** when `2 ≤ n`. -/
theorem add_one_ne_self {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) : i + 1 ≠ i := by
  intro h
  have hone : (1 : Fin n) = 0 := by
    apply add_left_cancel (a := i)
    simpa using h
  have hval := congrArg Fin.val hone
  simp [Nat.mod_eq_of_lt (by omega : 1 < n)] at hval

/-- **Adding one twice in `Fin n` never returns to the same element** when `3 ≤ n`. -/
theorem add_one_add_one_ne_self {n : ℕ} [NeZero n] (hn : 3 ≤ n) (i : Fin n) :
    i + 1 + 1 ≠ i := by
  intro h
  have htwo : (1 + 1 : Fin n) = 0 := by
    apply add_left_cancel (a := i)
    simpa [add_assoc] using h
  have hval := congrArg Fin.val htwo
  simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < n)] at hval

/-- Subtracting one in `Fin n` never returns to the same element when `2 ≤ n`. -/
theorem sub_one_ne_self {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) : i - 1 ≠ i := fun h ↦
  add_one_ne_self hn (i - 1) (by rw [sub_add_cancel, h])

/-- In `Fin n` with `3 ≤ n`, the successor and the predecessor of an element are distinct. -/
theorem add_one_ne_sub_one {n : ℕ} [NeZero n] (hn : 3 ≤ n) (i : Fin n) : i + 1 ≠ i - 1 :=
  mt eq_sub_iff_add_eq.1 (add_one_add_one_ne_self hn i)

/-- **A function on `Fin (n + 1)` unchanged by adding one is constant.** -/
theorem apply_eq_apply_zero_of_add_one {β : Type*} {n : ℕ} {f : Fin (n + 1) → β}
    (h : ∀ i, f (i + 1) = f i) (i : Fin (n + 1)) : f i = f 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => rw [← Fin.coeSucc_eq_succ, h, ih]

/-- **Adding one in `Fin n` flips the sign `(-1) ^ ·` read off the value** when `n` is even.  The
wraparound at the last index respects the sign exactly because `n` is even. -/
theorem neg_one_pow_val_add_one {M : Type*} [Monoid M] [HasDistribNeg M] {n : ℕ} [NeZero n]
    (hn : Even n) (i : Fin n) : (-1 : M) ^ ((i + 1 : Fin n) : ℕ) = -(-1 : M) ^ (i : ℕ) := by
  have hval : ((i + 1 : Fin n) : ℕ) = (i.val + 1) % n := by
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [hval]
  rcases Nat.lt_or_ge (i.val + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_succ, mul_neg_one]
  · have hi : i.val + 1 = n := by have := i.isLt; omega
    have hn' : Even (i.val + 1) := by rw [hi]; exact hn
    have hodd : Odd i.val := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hn')
    rw [hi, Nat.mod_self, pow_zero, hodd.neg_one_pow, neg_neg]

/-- A permutation of `Fin 2` is either the identity or the transposition. -/
theorem perm_fin_two_eq_one_or_swap (e : Equiv.Perm (Fin 2)) :
    e = 1 ∨ e = Equiv.swap 0 1 := by
  by_cases h0 : e 0 = 0
  · left
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · apply Fin.eq_one_of_ne_zero
      intro h1
      exact Fin.zero_ne_one (e.injective (h1.trans h0.symm)).symm
  · right
    have h0' : e 0 = 1 := Fin.eq_one_of_ne_zero _ h0
    apply Equiv.ext
    intro i
    fin_cases i
    · simpa using h0'
    · have h1 : e 1 = 0 := by
        by_contra h
        have h1' : e 1 = 1 := Fin.eq_one_of_ne_zero _ h
        exact Fin.zero_ne_one (e.injective (h1'.trans h0'.symm)).symm
      simpa using h1

/-- **A shifted indicator picks out one summand.** Summing `f` over `Fin n` against the indicator
of `b = k + j` gives `f` at the index `b - j` when that is a valid index and `j ≤ b`, and `0`
otherwise. -/
theorem sum_ite_val_add {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) (b j : ℕ) :
    ∑ k : Fin n, (if b = (k : ℕ) + j then f k else 0)
      = if h : b - j < n ∧ j ≤ b then f ⟨b - j, h.1⟩ else 0 := by
  by_cases h : b - j < n ∧ j ≤ b
  · have hb : ∀ k : Fin n, (b = (k : ℕ) + j) = (k = (⟨b - j, h.1⟩ : Fin n)) := by
      intro k
      have := h.2
      simp only [Fin.ext_iff, eq_iff_iff]
      omega
    simp only [hb, dite_eq_left h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · rw [dite_eq_right h, Finset.sum_eq_zero]
    intro k _
    have := k.isLt
    exact ite_eq_right (by omega)

/-! ### Cyclic index arithmetic in `Fin 3` -/

/-- **A distinct index of `Fin 3` is one of the two shifts of the other.** -/
theorem eq_add_one_or_eq_add_two_fin_three {i j : Fin 3} (h : i ≠ j) : i = j + 1 ∨ i = j + 2 := by
  revert h; revert i j; decide

/-- **Shifting an index of `Fin 3` by one twice is shifting it by two.** -/
theorem add_one_add_one_fin_three (j : Fin 3) : j + 1 + 1 = j + 2 := by revert j; decide

/-- **Shifting an index of `Fin 3` by one and then by two returns to it.** -/
theorem add_one_add_two_fin_three (j : Fin 3) : j + 1 + 2 = j := by revert j; decide

/-- **Shifting an index of `Fin 3` by two and then by one returns to it.** -/
theorem add_two_add_one_fin_three (j : Fin 3) : j + 2 + 1 = j := by revert j; decide

/-- **Shifting an index of `Fin 3` by two twice is shifting it by one.** -/
theorem add_two_add_two_fin_three (j : Fin 3) : j + 2 + 2 = j + 1 := by revert j; decide

/-- **A sum over `Fin 3` read off starting from an arbitrary index.** -/
theorem sum_fin_three_rotate {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) (j : Fin 3) :
    ∑ m, f m = f j + f (j + 1) + f (j + 2) := by
  have h : ∑ m : Fin 3, f (j + m) = ∑ m : Fin 3, f m :=
    Fintype.sum_equiv (Equiv.addLeft j) _ _ fun _ => rfl
  rw [← h, Fin.sum_univ_three, add_zero]

end TauCeti

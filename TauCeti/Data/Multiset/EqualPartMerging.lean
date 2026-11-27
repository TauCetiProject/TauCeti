/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import TauCeti.Data.Multiset.Map

/-!
# Bounded equal-part merging

A multiset `b` of natural numbers is a `y`-merging of a multiset `a` when the occurrences of `a`
can be grouped into nonempty blocks of equal entries, each block having at most `y` entries, and
`b` lists the sums of the blocks. For instance `{1, 1, 2, 2, 2, 3}` merges at bound `2` into
`{1, 1, 2, 3, 4}`, by combining two of the three occurrences of `2`.

This is the relation by which the cycle type of a Frobenius element at a ramified prime is
compared with the degrees of the irreducible factors of a polynomial modulo that prime: a factor
of degree `d` occurring with exponent `m` contributes `m` occurrences of `d`, which the cycles of
the Frobenius element may merge into blocks of at most `m` of them (Bary-Soroker, Koukoulopoulos
and Kozma, *Irreducibility of random polynomials: general measures*, Definition 11.2 and
Lemma 12.9).

A nonempty block of equal entries is determined by its cardinality `m` and its entry `k`, so a
merging is recorded by a multiset of pairs `(m, k)`: the block is `Multiset.replicate m k` and
its sum is `m * k`. `TauCeti.equalPartMerging_iff_exists_blocks` restates the definition with the
blocks as multisets.

## Main definitions

* `TauCeti.EqualPartMerging y a b`: `b` is a merging of `a` by equal-entry blocks of at most `y`
  entries.

## Main results

* `TauCeti.equalPartMerging_iff_exists_blocks`: the definition in terms of a multiset of
  equal-entry blocks whose flattening is `a` and whose block sums are `b`.
* `TauCeti.equalPartMerging_zero`, `TauCeti.equalPartMerging_replicate_singleton`,
  `TauCeti.EqualPartMerging.add`, `TauCeti.equalPartMerging_sum`: mergings are generated from
  single blocks by addition.
* `TauCeti.equalPartMerging_self`: for `1 ≤ y`, every multiset merges into itself.
* `TauCeti.EqualPartMerging.mono`: enlarging the bound preserves mergings.
* `TauCeti.EqualPartMerging.sum_eq`: a merging conserves the total sum.
* `TauCeti.EqualPartMerging.eq_of_lt_two`, `TauCeti.equalPartMerging_iff_eq_of_lt_two`: below
  bound `2` every block is a single occurrence, so a merging is an equality.
* `TauCeti.EqualPartMerging.exists_le_of_le`: the occurrence blocks producing a submultiset
  `v ≤ b` flatten to a submultiset `u ≤ a`, which merges into `v`, while `a - u` merges into
  `b - v`; in particular `u.sum = v.sum`.
-/

public section

open Multiset

namespace TauCeti

/-- `EqualPartMerging y a b` says that `b` is obtained from `a` by grouping the occurrences of
`a` into nonempty blocks of equal entries, each with at most `y` entries, and replacing every
block by its sum.

A block of `m` copies of `k` is recorded by the pair `(m, k)`: it is the multiset
`Multiset.replicate m k` and contributes the part `m * k` to `b`. The multiset of these pairs is
the witness. `TauCeti.equalPartMerging_iff_exists_blocks` gives the equivalent form with the
blocks themselves as multisets. -/
def EqualPartMerging (y : ℝ) (a b : Multiset ℕ) : Prop :=
  ∃ blocks : Multiset (ℕ × ℕ), (∀ p ∈ blocks, 0 < p.1 ∧ (p.1 : ℝ) ≤ y) ∧
    (blocks.map fun p => replicate p.1 p.2).sum = a ∧ blocks.map (fun p => p.1 * p.2) = b

variable {y z : ℝ} {a b a' b' : Multiset ℕ}

/-- A multiset of nonempty blocks with equal entries is the image of the multiset of pairs
(cardinality, entry) under `Multiset.replicate`. -/
private theorem exists_pairs_of_blocks (blocks : Multiset (Multiset ℕ))
    (h : ∀ B ∈ blocks, B ≠ 0 ∧ (card B : ℝ) ≤ y ∧ ∀ u ∈ B, ∀ v ∈ B, u = v) :
    ∃ pairs : Multiset (ℕ × ℕ), (∀ p ∈ pairs, 0 < p.1 ∧ (p.1 : ℝ) ≤ y) ∧
      pairs.map (fun p => replicate p.1 p.2) = blocks := by
  induction blocks using Multiset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | cons B blocks ih =>
    obtain ⟨hB0, hBy, hBeq⟩ := h B (mem_cons_self _ _)
    obtain ⟨pairs, hpairs, hmap⟩ := ih fun C hC => h C (mem_cons_of_mem hC)
    obtain ⟨k, hk⟩ := exists_mem_of_ne_zero hB0
    refine ⟨(card B, k) ::ₘ pairs, ?_, ?_⟩
    · simp only [mem_cons, forall_eq_or_imp]
      exact ⟨⟨card_pos.2 hB0, hBy⟩, hpairs⟩
    · rw [map_cons, hmap, ← eq_replicate_card.2 fun u hu => hBeq u hu k hk]

/-- **Blocks form of equal-part merging.** `b` is a `y`-merging of `a` exactly when some
multiset of nonempty blocks with equal entries and at most `y` entries each flattens to `a` and
has block sums `b`. -/
theorem equalPartMerging_iff_exists_blocks :
    EqualPartMerging y a b ↔ ∃ blocks : Multiset (Multiset ℕ), blocks.sum = a ∧
      blocks.map Multiset.sum = b ∧
        ∀ B ∈ blocks, B ≠ 0 ∧ (card B : ℝ) ≤ y ∧ ∀ u ∈ B, ∀ v ∈ B, u = v := by
  constructor
  · rintro ⟨pairs, hpairs, rfl, rfl⟩
    refine ⟨pairs.map fun p => replicate p.1 p.2, rfl, ?_, ?_⟩
    · simp [sum_replicate]
    · simp only [mem_map, forall_exists_index, and_imp]
      rintro _ p hp rfl
      refine ⟨?_, by simpa using (hpairs p hp).2, fun u hu v hv => ?_⟩
      · rw [Ne, ← card_eq_zero, card_replicate]
        exact (hpairs p hp).1.ne'
      · rw [eq_of_mem_replicate hu, eq_of_mem_replicate hv]
  · rintro ⟨blocks, rfl, rfl, hblocks⟩
    obtain ⟨pairs, hpairs, rfl⟩ := exists_pairs_of_blocks blocks hblocks
    exact ⟨pairs, hpairs, rfl, by simp [sum_replicate]⟩

/-! ### Generators -/

/-- The empty multiset merges into itself at every bound, with no blocks. -/
@[simp]
theorem equalPartMerging_zero (y : ℝ) : EqualPartMerging y 0 0 :=
  ⟨0, by simp, by simp, by simp⟩

/-- A single block of `m` copies of `k`, with `0 < m ≤ y`, merges into the single part
`m * k`. -/
theorem equalPartMerging_replicate_singleton {m : ℕ} (hm : 0 < m) (hmy : (m : ℝ) ≤ y) (k : ℕ) :
    EqualPartMerging y (replicate m k) {m * k} :=
  ⟨{(m, k)}, by simpa using ⟨hm, hmy⟩, by simp, by simp⟩

/-- Mergings of two multisets add up to a merging of their sum. -/
theorem EqualPartMerging.add (h : EqualPartMerging y a b) (h' : EqualPartMerging y a' b') :
    EqualPartMerging y (a + a') (b + b') := by
  obtain ⟨P, hP, rfl, rfl⟩ := h
  obtain ⟨P', hP', rfl, rfl⟩ := h'
  refine ⟨P + P', fun p hp => ?_, by simp, by simp⟩
  rcases mem_add.1 hp with hp | hp
  exacts [hP p hp, hP' p hp]

/-- A finite family of mergings adds up to a merging of the sums. -/
theorem equalPartMerging_sum {ι : Type*} (s : Finset ι) {f g : ι → Multiset ℕ}
    (h : ∀ i ∈ s, EqualPartMerging y (f i) (g i)) :
    EqualPartMerging y (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ### Basic properties -/

/-- For `1 ≤ y`, every multiset merges into itself, by singleton blocks. -/
theorem equalPartMerging_self (hy : 1 ≤ y) (a : Multiset ℕ) : EqualPartMerging y a a :=
  ⟨a.map fun k => (1, k), by simp [hy], by simp [Function.comp_def, sum_map_singleton],
    by simp⟩

/-- Enlarging the bound preserves a merging. -/
theorem EqualPartMerging.mono (h : EqualPartMerging y a b) (hyz : y ≤ z) :
    EqualPartMerging z a b := by
  obtain ⟨P, hP, ha, hb⟩ := h
  exact ⟨P, fun p hp => ⟨(hP p hp).1, (hP p hp).2.trans hyz⟩, ha, hb⟩

/-- A merging conserves the total sum. -/
theorem EqualPartMerging.sum_eq (h : EqualPartMerging y a b) : a.sum = b.sum := by
  obtain ⟨P, -, rfl, rfl⟩ := h
  induction P using Multiset.induction_on with
  | empty => simp
  | cons p P ih => simp [ih, sum_replicate]

/-- Below bound `2` every nonempty block is a single occurrence, so a merging is an equality.
No positivity of the entries is needed. -/
theorem EqualPartMerging.eq_of_lt_two (h : EqualPartMerging y a b) (hy : y < 2) : a = b := by
  obtain ⟨P, hP, rfl, rfl⟩ := h
  have h1 : ∀ p ∈ P, p.1 = 1 := fun p hp => by
    have := (hP p hp).1
    have : (p.1 : ℝ) < 2 := (hP p hp).2.trans_lt hy
    norm_cast at this
    omega
  have e1 : P.map (fun p => replicate p.1 p.2) = P.map fun p => {p.2} :=
    map_congr rfl fun p hp => by rw [h1 p hp, replicate_one]
  have e2 : P.map (fun p => p.1 * p.2) = P.map Prod.snd :=
    map_congr rfl fun p hp => by rw [h1 p hp, one_mul]
  rw [e1, e2, ← sum_map_singleton (P.map Prod.snd), map_map, Function.comp_def]

/-- For `1 ≤ y < 2`, `b` is a `y`-merging of `a` exactly when `b = a`. -/
theorem equalPartMerging_iff_eq_of_lt_two (hy₁ : 1 ≤ y) (hy₂ : y < 2) :
    EqualPartMerging y a b ↔ a = b :=
  ⟨fun h => h.eq_of_lt_two hy₂, by rintro rfl; exact equalPartMerging_self hy₁ a⟩

/-- **Selecting occurrence blocks.** If `b` is a `y`-merging of `a` and `v ≤ b`, then the blocks
producing the occurrences of `v` flatten to some `u ≤ a` which merges into `v`, and the remaining
blocks merge `a - u` into `b - v`. Occurrences are retained even when several block sums are
equal. In particular `u.sum = v.sum`, by `TauCeti.EqualPartMerging.sum_eq`. -/
theorem EqualPartMerging.exists_le_of_le (h : EqualPartMerging y a b) {v : Multiset ℕ}
    (hv : v ≤ b) :
    ∃ u ≤ a, EqualPartMerging y u v ∧ EqualPartMerging y (a - u) (b - v) := by
  obtain ⟨P, hP, rfl, rfl⟩ := h
  obtain ⟨T, hT, rfl⟩ := le_map_iff.1 hv
  obtain ⟨R, rfl⟩ := Multiset.le_iff_exists_add.1 hT
  refine ⟨(T.map fun p => replicate p.1 p.2).sum, ?_, ⟨T, fun p hp => hP p
    (mem_add.2 (Or.inl hp)), rfl, rfl⟩, ⟨R, fun p hp => hP p (mem_add.2 (Or.inr hp)), ?_, ?_⟩⟩
  · rw [map_add, sum_add]
    exact Multiset.le_add_right _ _
  · simp
  · simp

/-! ### Checks -/

/-- Two of the three occurrences of `2` in `{1, 1, 2, 2, 2, 3}` merge at bound `2`. -/
example : EqualPartMerging 2 {1, 1, 2, 2, 2, 3} {1, 1, 2, 3, 4} :=
  ⟨{(1, 1), (1, 1), (1, 2), (1, 3), (2, 2)}, by norm_num, by decide, by decide⟩

/-- Two successive mergings at bound `2` need not compose to a merging, even at bound `4`: the
only block producing `4` from `{1, 1, 2}` would mix `1` and `2`. -/
example : EqualPartMerging 2 {1, 1, 2} {2, 2} ∧ EqualPartMerging 2 {2, 2} {4} ∧
    ¬ EqualPartMerging 4 {1, 1, 2} {4} := by
  refine ⟨⟨{(2, 1), (1, 2)}, by norm_num, by decide, by decide⟩,
    ⟨{(2, 2)}, by norm_num, by decide, by decide⟩, ?_⟩
  rw [equalPartMerging_iff_exists_blocks]
  rintro ⟨blocks, hs, hm, hb⟩
  obtain ⟨B, rfl, -⟩ := map_eq_singleton.1 hm
  rw [sum_singleton] at hs
  subst hs
  have := (hb _ (mem_singleton_self _)).2.2 1 (by simp) 2 (by simp)
  omega

end TauCeti

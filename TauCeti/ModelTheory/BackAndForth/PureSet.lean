/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Equivalence
public import Mathlib.Data.Set.Card

/-!
# Back-and-forth equivalence of pure sets

A pure set is a structure in the empty language. Tuples of two pure sets have the same atomic
type exactly when they have the same equality pattern, and the back-and-forth levels then only
measure how many elements lie outside each tuple. Writing `cₐ` for the number of elements, in
`ℕ∞`, outside the range of the tuple `a`:

* at a finite level `k`, tuples with the same equality pattern are equivalent exactly when
  `min cₐ k = min c_b k`: every round can use up one fresh element, and `k` rounds cannot tell
  apart two supplies of at least `k` fresh elements;
* at every level from `ω` on, they are equivalent exactly when `cₐ = c_b`.

For the empty tuples this compares the cardinalities of the two sets. In particular an infinite
set and a finite set with `m` elements are equivalent exactly at the levels `k ≤ m`, and never at
level `ω`. This is the basic separation of finite components from infinite ones used when
structures are assembled from pure-set fibers.

These are the classical Ehrenfeucht–Fraïssé computations for pure sets; see Wilfrid Hodges,
*Model Theory* (1993), Chapter 3, for back-and-forth equivalence and its games.

## Main results

* `TauCeti.sameAtomicType_empty_iff`: atomic types of pure sets are equality patterns.
* `TauCeti.bfEquiv_empty_natCast_iff`: back-and-forth equivalence at a finite level.
* `TauCeti.bfEquiv_empty_iff_of_omega0_le`: back-and-forth equivalence from level `ω` on.
* `TauCeti.bfEquiv_empty_elim0_natCast_iff_le_card`: an infinite pure set and a pure set `N` are
  equivalent at level `k` exactly when `N` has at least `k` elements.
-/

public section

universe w w' o

namespace TauCeti

open FirstOrder Fin Set

variable {M : Type w} {N : Type w'} {n : ℕ} {a : Fin n → M} {b : Fin n → N}

/-- Appending one element to each tuple preserves the equality pattern exactly when the old
patterns agree and the new element repeats the same entries on both sides. -/
private theorem snoc_eq_iff_snoc_eq {x : M} {y : N} :
    (∀ i j, (snoc a x : Fin (n + 1) → M) i = (snoc a x : Fin (n + 1) → M) j ↔
      (snoc b y : Fin (n + 1) → N) i = (snoc b y : Fin (n + 1) → N) j) ↔
      (∀ i j, a i = a j ↔ b i = b j) ∧ ∀ i, a i = x ↔ b i = y := by
  simp only [Fin.forall_fin_succ', snoc_castSucc, snoc_last, eq_comm (a := x), eq_comm (a := y),
    iff_self, and_true]
  exact ⟨fun h => ⟨fun i => (h.1 i).1, fun i => (h.1 i).2⟩,
    fun h => ⟨fun i => ⟨h.1 i, h.2 i⟩, h.2⟩⟩

/-- Adding a fresh element to a set removes one element from its complement. -/
private theorem encard_compl_insert_add_one {s : Set M} {x : M} (hx : x ∉ s) :
    (insert x s)ᶜ.encard + 1 = sᶜ.encard := by
  rw [← encard_sdiff_singleton_add_one (mem_compl hx), insert_eq, compl_union, sdiff_eq,
    inter_comm]

/-- Truncating at `t + 1` and then at `t` is truncating at `t`. -/
private theorem min_min_add_one (c t : ℕ∞) : min (min c (t + 1)) t = min c t := by
  rw [min_assoc, min_eq_right le_self_add]

/-- The forth step for pure sets: if the numbers of fresh elements agree up to `t + 1`, then
every element of `M` has a match in `N` repeating the same entries, after which the numbers of
fresh elements agree up to `t`. The level `t = ⊤` compares the numbers themselves. -/
private theorem exists_forth (hab : ∀ i j, a i = a j ↔ b i = b j) {t : ℕ∞}
    (h : min (range a)ᶜ.encard (t + 1) = min (range b)ᶜ.encard (t + 1)) (x : M) :
    ∃ y : N, (∀ i, a i = x ↔ b i = y) ∧
      min (range (snoc a x))ᶜ.encard t = min (range (snoc b y))ᶜ.encard t := by
  by_cases hx : x ∈ range a
  · obtain ⟨i₀, rfl⟩ := hx
    refine ⟨b i₀, fun i => hab i i₀, ?_⟩
    rw [range_snoc, range_snoc, insert_eq_of_mem (mem_range_self i₀),
      insert_eq_of_mem (mem_range_self i₀), ← min_min_add_one, h, min_min_add_one]
  · rw [← encard_compl_insert_add_one hx] at h
    obtain ⟨y, hy⟩ : (range b)ᶜ.Nonempty := by
      rw [← one_le_encard_iff_nonempty]
      calc (1 : ℕ∞) ≤ min ((insert x (range a))ᶜ.encard + 1) (t + 1) :=
            le_min le_add_self le_add_self
        _ ≤ (range b)ᶜ.encard := h ▸ min_le_left _ _
    refine ⟨y, fun i => iff_of_false (fun hi => hx ⟨i, hi⟩) fun hi => hy ⟨i, hi⟩, ?_⟩
    rw [← encard_compl_insert_add_one hy, min_add_add_right, min_add_add_right] at h
    simpa only [range_snoc] using ENat.add_left_injective_of_ne_top ENat.one_ne_top h

/-- The converse of the forth step at a fresh element: a match repeating the same entries,
after which the numbers of fresh elements agree up to `t`, shows that they agreed up to
`t + 1` before. -/
private theorem min_encard_add_one_eq_of_snoc {x : M} {y : N} (hx : x ∉ range a)
    (hxy : ∀ i, a i = x ↔ b i = y) {t : ℕ∞}
    (h : min (range (snoc a x))ᶜ.encard t = min (range (snoc b y))ᶜ.encard t) :
    min (range a)ᶜ.encard (t + 1) = min (range b)ᶜ.encard (t + 1) := by
  have hy : y ∉ range b := fun ⟨i, hi⟩ => hx ⟨i, (hxy i).mpr hi⟩
  rw [← encard_compl_insert_add_one hx, ← encard_compl_insert_add_one hy, min_add_add_right,
    min_add_add_right]
  simp only [range_snoc] at h
  rw [h]

variable [Language.empty.Structure M] [Language.empty.Structure N]

/-- Tuples of pure sets have the same atomic type exactly when they have the same equality
pattern. -/
theorem sameAtomicType_empty_iff (a : Fin n → M) (b : Fin n → N) :
    SameAtomicType (L := Language.empty) a b ↔ ∀ i j, a i = a j ↔ b i = b j := by
  rw [sameAtomicType_iff]
  exact and_iff_left fun r => isEmptyElim r

/-- Tuples of pure sets with the same equality pattern and the same number of elements outside
their ranges are back-and-forth equivalent at every level. -/
theorem bfEquiv_empty_of_encard_compl_range_eq (hab : ∀ i j, a i = a j ↔ b i = b j)
    (h : (range a)ᶜ.encard = (range b)ᶜ.encard) (α : Ordinal.{o}) :
    BFEquiv (L := Language.empty) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero => exact BFEquiv.zero.mpr ((sameAtomicType_empty_iff a b).mpr hab)
  | add_one α ih =>
    have h' : min (range a)ᶜ.encard (⊤ + 1) = min (range b)ᶜ.encard (⊤ + 1) := by simpa
    refine (BFEquiv.add_one α a b).mpr ⟨ih hab h, fun x => ?_, fun y => ?_⟩
    · obtain ⟨y, hxy, hm⟩ := exists_forth hab h' x
      exact ⟨y, ih (snoc_eq_iff_snoc_eq.mpr ⟨hab, hxy⟩) (by simpa using hm)⟩
    · obtain ⟨x, hxy, hm⟩ := exists_forth (fun i j => (hab i j).symm) h'.symm y
      exact ⟨x, ih (snoc_eq_iff_snoc_eq.mpr ⟨hab, fun i => (hxy i).symm⟩)
        (by simpa using hm.symm)⟩
  | limit α hα ih => exact (BFEquiv.limit hα a b).mpr fun β hβ => ih β hβ hab h

/-- Tuples of pure sets are back-and-forth equivalent at a finite level `k` exactly when they
have the same equality pattern and the numbers of elements outside their ranges agree after
truncation at `k`. -/
theorem bfEquiv_empty_natCast_iff (k : ℕ) (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := Language.empty) (k : Ordinal.{o}) n a b ↔
      (∀ i j, a i = a j ↔ b i = b j) ∧
        min (range a)ᶜ.encard k = min (range b)ᶜ.encard k := by
  induction k generalizing n with
  | zero => simp [sameAtomicType_empty_iff]
  | succ k ih =>
    rw [Nat.cast_succ, BFEquiv.add_one]
    simp only [ih, snoc_eq_iff_snoc_eq, Nat.cast_succ]
    constructor
    · rintro ⟨⟨hab, -⟩, hforth, hback⟩
      refine ⟨hab, ?_⟩
      by_cases hA : (range a)ᶜ.Nonempty
      · obtain ⟨x, hx⟩ := hA
        obtain ⟨y, ⟨-, hxy⟩, hm⟩ := hforth x
        exact min_encard_add_one_eq_of_snoc hx hxy hm
      by_cases hB : (range b)ᶜ.Nonempty
      · obtain ⟨y, hy⟩ := hB
        obtain ⟨x, ⟨-, hxy⟩, hm⟩ := hback y
        exact (min_encard_add_one_eq_of_snoc hy (fun i => (hxy i).symm) hm.symm).symm
      simp [not_nonempty_iff_eq_empty.mp hA, not_nonempty_iff_eq_empty.mp hB]
    · rintro ⟨hab, hm⟩
      refine ⟨⟨hab, by rw [← min_min_add_one, hm, min_min_add_one]⟩, fun x => ?_, fun y => ?_⟩
      · obtain ⟨y, hxy, hm'⟩ := exists_forth hab hm x
        exact ⟨y, ⟨hab, hxy⟩, hm'⟩
      · obtain ⟨x, hxy, hm'⟩ := exists_forth (fun i j => (hab i j).symm) hm.symm y
        exact ⟨x, ⟨hab, fun i => (hxy i).symm⟩, hm'.symm⟩

/-- From level `ω` on, tuples of pure sets are back-and-forth equivalent exactly when they have
the same equality pattern and the same number of elements outside their ranges. -/
theorem bfEquiv_empty_iff_of_omega0_le {α : Ordinal.{o}} (hα : Ordinal.omega0 ≤ α)
    (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := Language.empty) α n a b ↔
      (∀ i j, a i = a j ↔ b i = b j) ∧ (range a)ᶜ.encard = (range b)ᶜ.encard := by
  refine ⟨fun h => ?_, fun h => bfEquiv_empty_of_encard_compl_range_eq h.1 h.2 α⟩
  have hk (k : ℕ) := (bfEquiv_empty_natCast_iff k a b).mp
    (h.mono ((Ordinal.natCast_lt_omega0 k).le.trans hα))
  refine ⟨(hk 0).1, ENat.eq_of_forall_natCast_le_iff fun k => ?_⟩
  simp only [← min_eq_left_iff, min_comm (k : ℕ∞), (hk k).2]

/-- The empty tuples of two pure sets are back-and-forth equivalent at a finite level `k`
exactly when the sizes of the sets agree after truncation at `k`. -/
theorem bfEquiv_empty_elim0_natCast_iff (k : ℕ) :
    BFEquiv (L := Language.empty) (k : Ordinal.{o}) 0 (Fin.elim0 : Fin 0 → M)
      (Fin.elim0 : Fin 0 → N) ↔
      min (ENat.card M) k = min (ENat.card N) k := by
  simp [bfEquiv_empty_natCast_iff, range_eq_empty]

/-- An infinite pure set and a pure set `N` are back-and-forth equivalent at a finite level `k`
exactly when `N` has at least `k` elements. In particular an infinite set and a finite set with
`m` elements are equivalent exactly at the levels `k ≤ m`. -/
theorem bfEquiv_empty_elim0_natCast_iff_le_card [Infinite M] (k : ℕ) :
    BFEquiv (L := Language.empty) (k : Ordinal.{o}) 0 (Fin.elim0 : Fin 0 → M)
      (Fin.elim0 : Fin 0 → N) ↔ k ≤ ENat.card N := by
  rw [bfEquiv_empty_elim0_natCast_iff, ENat.card_eq_top_of_infinite, min_top_left, eq_comm,
    min_eq_right_iff]

end TauCeti

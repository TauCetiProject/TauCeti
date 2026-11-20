/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Duplicating an entry of a finite tuple

`TauCeti.duplicateAt e j z` replaces the `j`-th entry of an `L`-tuple `z : Fin L → α` by two
adjacent copies of `e` at positions `j` and `j + 1`, shifting subsequent entries up by one index.
Equivalently, it updates `z` at `j` to `e` and inserts `e` at `j.succ` via `Fin.insertNth`.

This file records the defining identity, the coordinate formula, and the total and prefix sum
identities in any additive commutative monoid when the replaced entry already equals `a`.

## Main definitions

* `TauCeti.duplicateAt`: replaces `z j` by two adjacent copies of `e` at positions `j` and `j + 1`.

## Main results

* `TauCeti.duplicateAt_def`: explicit formula via `Fin.insertNth` and `Function.update`.
* `TauCeti.duplicateAt_apply`: coordinate formula on `Fin (L + 1)`.
* `TauCeti.sum_duplicateAt`: total sum of `duplicateAt a j z` when `z j = a`.
* `TauCeti.sum_duplicateAt_range_le`: prefix sums of length at most `j` agree with those of `z`.
* `TauCeti.sum_duplicateAt_range_succ_ge`: prefix sums of length `q + 1` with `j ≤ q ≤ L` exceed
  the length-`q` prefix sum of `z` by `a` when `z j = a`.
-/

public section

namespace TauCeti

/-- Replace `z j` in an `L`-tuple `z` by two adjacent copies of `e` at positions `j` and `j + 1`. -/
def duplicateAt {α : Sort*} (e : α) {L : ℕ} (j : Fin L) (z : Fin L → α) : Fin (L + 1) → α :=
  j.succ.insertNth e (Function.update z j e)

/-- Explicit definition of `duplicateAt` via `Fin.insertNth` and `Function.update`. -/
theorem duplicateAt_def {α : Sort*} (e : α) {L : ℕ} (j : Fin L) (z : Fin L → α) :
    duplicateAt e j z = j.succ.insertNth e (Function.update z j e) := by rfl

/-- Coordinate formula for `duplicateAt`: `< j` unchanged, `j` and `j + 1` equal `e`, `> j + 1`
shifted down by `1`. -/
theorem duplicateAt_apply {α : Sort*} (e : α) {L : ℕ} (j : Fin L) (z : Fin L → α)
    (k : Fin (L + 1)) :
    duplicateAt e j z k =
      if hk : k.val < j.val then z ⟨k.val, by omega⟩
      else if k.val = j.val ∨ k.val = j.val + 1 then e else z ⟨k.val - 1, by omega⟩ := by
  rw [duplicateAt]
  cases k using Fin.succAboveCases j.succ with
  | x => simp
  | p r =>
    rw [Fin.insertNth_apply_succAbove]
    rcases lt_trichotomy r.val j.val with hlt | heq | hgt
    · rw [Function.update_of_ne (fun h ↦ Nat.ne_of_lt hlt (congrArg Fin.val h)),
        Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.2 (by simp; omega))]; simp [hlt]
    · obtain rfl := Fin.ext heq
      rw [Function.update_self, Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.2 (by simp))]; simp
    · rw [Function.update_of_ne (fun h ↦ Nat.ne_of_gt hgt (congrArg Fin.val h)),
        Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.2 (by simp; omega)),
        dite_eq_right (by rw [Fin.val_succ]; omega), ite_eq_right (by rw [Fin.val_succ]; omega)]
      exact congrArg z (Fin.ext (by simp))

/-- Sum of `duplicateAt a j z` when `z j = a`: replacing `a` at `j` by two copies adds `a`. -/
theorem sum_duplicateAt {M : Type*} [AddCommMonoid M] {L : ℕ} (j : Fin L) {a : M}
    {z : Fin L → M} (hzj : z j = a) :
    ∑ k : Fin (L + 1), duplicateAt a j z k = (∑ r : Fin L, z r) + a := by
  rw [duplicateAt, Fin.sum_univ_succAbove _ j.succ, Fin.insertNth_apply_same]
  simp only [Fin.insertNth_apply_succAbove]
  rw [Finset.sum_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.add_sum_erase Finset.univ z (Finset.mem_univ j)
  rw [hzj] at hsum; rw [hsum, add_comm]

/-- Prefix sums of `duplicateAt a j z` of length at most `j` agree with those of `z`. -/
theorem sum_duplicateAt_range_le {M : Type*} [AddCommMonoid M] {L : ℕ} (a : M) (j : Fin L)
    (z : Fin L → M) {p : ℕ} (hp : p ≤ j.val) :
    (∑ r ∈ Finset.range p, if h : r < L + 1 then duplicateAt a j z ⟨r, h⟩ else 0) =
      ∑ r ∈ Finset.range p, if h : r < L then z ⟨r, h⟩ else 0 :=
  Finset.sum_congr rfl fun r hr ↦ by
    rw [Finset.mem_range] at hr
    rw [dite_eq_left (by omega), dite_eq_left (by omega), duplicateAt_apply,
      dite_eq_left (by rw [Fin.val_mk]; omega)]

/-- Prefix sums of `duplicateAt a j z` of length `q + 1` with `j ≤ q ≤ L` exceed the length-`q`
prefix sum of `z` by `a` when `z j = a`. -/
theorem sum_duplicateAt_range_succ_ge {M : Type*} [AddCommMonoid M] {L : ℕ} (j : Fin L) {a : M}
    {z : Fin L → M} (hzj : z j = a) {q : ℕ} (hq₁ : j.val ≤ q) (hq₂ : q ≤ L) :
    (∑ r ∈ Finset.range (q + 1), if h : r < L + 1 then duplicateAt a j z ⟨r, h⟩ else 0) =
      (∑ r ∈ Finset.range q, if h : r < L then z ⟨r, h⟩ else 0) + a := by
  revert hq₂
  induction q, hq₁ using Nat.le_induction with
  | base =>
    intro _
    rw [Finset.sum_range_succ, sum_duplicateAt_range_le a j z le_rfl, dite_eq_left (by omega),
      duplicateAt_apply, dite_eq_right (lt_irrefl _), ite_eq_left (.inl rfl)]
  | succ q hjq ih =>
    intro hq₂
    rw [Finset.sum_range_succ _ (q + 1), ih (by omega), Finset.sum_range_succ _ q,
      dite_eq_left (by omega), dite_eq_left (by omega), duplicateAt_apply]
    rcases eq_or_lt_of_le hjq with heq | hlt
    · rw [show (⟨q, by omega⟩ : Fin L) = j from Fin.ext heq.symm, hzj,
        dite_eq_right (by rw [Fin.val_mk]; omega), ite_eq_left (.inr (by rw [Fin.val_mk]; omega))]
    · rw [dite_eq_right (by rw [Fin.val_mk]; omega), ite_eq_right (by rw [Fin.val_mk]; omega),
        show (⟨(⟨q + 1, by omega⟩ : Fin (L + 1)).val - 1, by omega⟩ : Fin L) = ⟨q, by omega⟩
          from Fin.ext (by simp), add_right_comm]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Basic
public import TauCeti.Algebra.BigOperators.Finset.PartialSum
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
* `TauCeti.duplicateAt_castSucc`, `TauCeti.duplicateAt_succ`: the two duplicated coordinates equal
  `e`.
* `TauCeti.duplicateAt_castSucc_of_lt`, `TauCeti.duplicateAt_succ_of_gt`: coordinates away from `j`
  recover `z`.
* `TauCeti.sum_duplicateAt`: total sum of `duplicateAt a j z` when `z j = a`.
* `TauCeti.prefixSum_duplicateAt_le`: prefix sums of length at most `j` agree with those of `z`.
* `TauCeti.prefixSum_duplicateAt_succ_ge`: prefix sums of length `q + 1` with `j ≤ q ≤ L` exceed
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

/-- The first of the two duplicated coordinates (`j.castSucc`) equals `e`. -/
@[simp]
theorem duplicateAt_castSucc {α : Sort*} (e : α) {L : ℕ} (j : Fin L) (z : Fin L → α) :
    duplicateAt e j z j.castSucc = e := by
  rw [duplicateAt_apply]; simp

/-- The second of the two duplicated coordinates (`j.succ`) equals `e`. -/
@[simp]
theorem duplicateAt_succ {α : Sort*} (e : α) {L : ℕ} (j : Fin L) (z : Fin L → α) :
    duplicateAt e j z j.succ = e := by
  rw [duplicateAt_apply]; simp

/-- Coordinates strictly before `j` are unchanged by `duplicateAt e j`. -/
theorem duplicateAt_castSucc_of_lt {α : Sort*} (e : α) {L : ℕ} {j : Fin L} (z : Fin L → α)
    {i : Fin L} (hij : i < j) : duplicateAt e j z i.castSucc = z i := by
  rw [duplicateAt_apply, dite_eq_left (by simpa using hij)]; simp

/-- Coordinates strictly after `j` in `z` sit one position higher in `duplicateAt e j z`. -/
theorem duplicateAt_succ_of_gt {α : Sort*} (e : α) {L : ℕ} {j : Fin L} (z : Fin L → α)
    {i : Fin L} (hji : j < i) : duplicateAt e j z i.succ = z i := by
  rw [duplicateAt_apply, dite_eq_right (by simp; omega), ite_eq_right (by simp; omega)]
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
theorem prefixSum_duplicateAt_le {M : Type*} [AddCommMonoid M] {L : ℕ} (a : M) (j : Fin L)
    (z : Fin L → M) {p : ℕ} (hp : p ≤ j.val) :
    prefixSum p (duplicateAt a j z) = prefixSum p z := by
  rw [prefixSum_eq_sum_castLE (by omega), prefixSum_eq_sum_castLE (by omega)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi : (Fin.castLE (by omega) i : Fin (L + 1)) = (Fin.castLE (by omega) i : Fin L).castSucc :=
    Fin.ext (by simp)
  rw [hi, duplicateAt_castSucc_of_lt a z (i := Fin.castLE (by omega) i)
    (Fin.lt_def.2 (by simp; omega))]

/-- Prefix sums of `duplicateAt a j z` of length `q + 1` with `j ≤ q ≤ L` exceed the length-`q`
prefix sum of `z` by `a` when `z j = a`. -/
theorem prefixSum_duplicateAt_succ_ge {M : Type*} [AddCommMonoid M] {L : ℕ} (j : Fin L) {a : M}
    {z : Fin L → M} (hzj : z j = a) {q : ℕ} (hq₁ : j.val ≤ q) (hq₂ : q ≤ L) :
    prefixSum (q + 1) (duplicateAt a j z) = prefixSum q z + a := by
  induction q, hq₁ using Nat.le_induction with
  | base =>
    rw [prefixSum_succ (by omega), prefixSum_duplicateAt_le a j z le_rfl]
    have hj_cast : (⟨j.val, by omega⟩ : Fin (L + 1)) = j.castSucc := Fin.ext (by simp)
    rw [hj_cast, duplicateAt_castSucc]
  | succ q hjq ih =>
    rw [prefixSum_succ (by omega), ih (by omega), prefixSum_succ (by omega)]
    rcases eq_or_lt_of_le hjq with rfl | hlt
    · rw [Fin.eta, hzj]
      have hj_succ : (⟨j.val + 1, by omega⟩ : Fin (L + 1)) = j.succ := Fin.ext (by simp)
      rw [hj_succ, duplicateAt_succ, add_right_comm]
    · have hq_succ : (⟨q + 1, by omega⟩ : Fin (L + 1)) = (⟨q, by omega⟩ : Fin L).succ :=
        Fin.ext (by simp)
      rw [hq_succ, duplicateAt_succ_of_gt a z (i := ⟨q, by omega⟩) (Fin.lt_def.2 hlt),
        add_right_comm]

end TauCeti

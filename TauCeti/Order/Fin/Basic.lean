/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Set.Defs

/-!
# Order characterizations on `Fin`

This file characterizes elements of `Fin (k + 1)` by how they sit relative to the embedded indices
`i'.castSucc` (`i' : Fin k`), and records the Galois connections between codegeneracy
(`Fin.predAbove`) and coface (`Fin.succAbove`) maps.

## Main results

* `Fin.succ_eq_or_castSucc_eq_iff_forall_le`: an index `j : Fin (k + 1)` equals `i.succ` or
  `i.castSucc` if and only if `i` lies weakly above every `i'` with `i'.castSucc < j` and weakly
  below every `i'` with `j ≤ i'.castSucc`.
* `Fin.eq_iff_forall_castSucc_lt_and_le`: two indices `r, j : Fin (k + 1)` are equal if and only
  if they determine the same order cut on the embedded indices `i'.castSucc` (`i' : Fin k`).
* `Fin.galoisConnection_predAbove_castSucc_succAbove`: `i.predAbove ⊣ i.castSucc.succAbove`.
* `Fin.galoisConnection_succ_succAbove_predAbove`: `i.succ.succAbove ⊣ i.predAbove`.
* `Fin.strictMono_of_forall_mem_Ioo`: a tuple separated by a sequence, `a k < w k < a (k + 1)`,
  is strictly increasing.
-/

public section

open Set

namespace Fin

/-- An index `j : Fin (k + 1)` equals `i.succ` or `i.castSucc` if and only if `i` lies weakly
above every `i' : Fin k` with `i'.castSucc < j` and weakly below every `i' : Fin k` with
`j ≤ i'.castSucc`. -/
theorem succ_eq_or_castSucc_eq_iff_forall_le {k : ℕ} {i : Fin k} {j : Fin (k + 1)} :
    (i.succ = j ∨ i.castSucc = j) ↔
      (∀ i' : Fin k, i'.castSucc < j → i' ≤ i) ∧
        ∀ i' : Fin k, j ≤ i'.castSucc → i ≤ i' := by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨fun i' hi' ↦ castSucc_lt_succ_iff.mp hi',
        fun i' hi' ↦ castSucc_le_castSucc_iff.mp (i.castSucc_lt_succ.le.trans hi')⟩
    · exact ⟨fun i' hi' ↦ (castSucc_lt_castSucc_iff.mp hi').le,
        fun i' hi' ↦ castSucc_le_castSucc_iff.mp hi'⟩
  · rintro ⟨hlow, hhigh⟩
    rcases lt_trichotomy i.castSucc j with hij | hij | hij
    · have hij_val : i.val + 1 ≤ j.val := Nat.succ_le_of_lt (by simpa using lt_def.mp hij)
      rcases eq_or_lt_of_le hij_val with heq | hlt
      · exact Or.inl (eq_of_val_eq heq)
      · exfalso
        let i' : Fin k := ⟨i.val + 1, by omega⟩
        exact Nat.not_succ_le_self i.val (le_def.mp (hlow i' (lt_def.mpr hlt)))
    · exact Or.inr hij
    · exfalso
      let i' : Fin k := ⟨j.val, by omega⟩
      exact (not_le_of_gt hij) (castSucc_le_castSucc_iff.mpr (hhigh i' le_rfl))

/-- Two indices `r, j : Fin (k + 1)` are equal if and only if every `i' : Fin k` with
`i'.castSucc < j` satisfies `i'.castSucc < r` and every `i' : Fin k` with `j ≤ i'.castSucc`
satisfies `r ≤ i'.castSucc`. -/
theorem eq_iff_forall_castSucc_lt_and_le {k : ℕ} {r j : Fin (k + 1)} :
    r = j ↔
      (∀ i' : Fin k, i'.castSucc < j → i'.castSucc < r) ∧
        ∀ i' : Fin k, j ≤ i'.castSucc → r ≤ i'.castSucc := by
  constructor
  · rintro rfl
    exact ⟨fun _ h ↦ h, fun _ h ↦ h⟩
  · rintro ⟨hlow, hhigh⟩
    refine le_antisymm ?_ ?_
    · by_contra hlt
      replace hlt := lt_of_not_ge hlt
      let i' : Fin k := ⟨j.val, by omega⟩
      exact (not_le_of_gt hlt) (hhigh i' le_rfl)
    · by_contra hlt
      replace hlt := lt_of_not_ge hlt
      let i' : Fin k := ⟨r.val, by omega⟩
      exact (lt_irrefl r) (hlow i' hlt)

/-- For `i : Fin (n + 1)`, the codegeneracy map `i.predAbove` is left adjoint to the coface map
`i.castSucc.succAbove`. -/
theorem galoisConnection_predAbove_castSucc_succAbove {n : ℕ} (i : Fin (n + 1)) :
    GaloisConnection i.predAbove i.castSucc.succAbove := by
  refine GaloisConnection.monotone_intro (Fin.succAboveOrderEmb i.castSucc).monotone
    (Fin.predAbove_right_monotone i) (fun y ↦ ?_) fun x ↦ ?_
  · by_cases hy : y = i.castSucc
    · subst hy
      rw [Fin.predAbove_of_le_castSucc i i.castSucc le_rfl, Fin.castPred_castSucc,
        Fin.succAbove_castSucc_self]
      exact Fin.castSucc_le_succ i
    · rw [Fin.succAbove_predAbove hy]
  · rw [Fin.predAbove_succAbove]

/-- For `i : Fin (n + 1)`, the coface map `i.succ.succAbove` is left adjoint to the codegeneracy
map `i.predAbove`. -/
theorem galoisConnection_succ_succAbove_predAbove {n : ℕ} (i : Fin (n + 1)) :
    GaloisConnection i.succ.succAbove i.predAbove := by
  refine GaloisConnection.monotone_intro (Fin.predAbove_right_monotone i)
    (Fin.succAboveOrderEmb i.succ).monotone (fun y ↦ ?_) fun x ↦ ?_
  · obtain hy | hy := le_or_gt y i
    · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr hy),
        Fin.predAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hy),
        Fin.castPred_castSucc]
    · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.succ_le_castSucc_iff.mpr hy),
        Fin.predAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr hy.le),
        Fin.pred_succ]
  · by_cases hx : x = i.succ
    · subst hx
      rw [Fin.predAbove_succ_self, Fin.succAbove_succ_self]
      exact Fin.castSucc_le_succ i
    · rw [Fin.succ_succAbove_predAbove hx]

/-- A tuple `w` separated by a `ℤ`-indexed sequence `a`, in the sense that
`a k < w k < a (k + 1)` for every index `k`, is strictly increasing. -/
theorem strictMono_of_forall_mem_Ioo {α : Type*} [Preorder α] {n : ℕ} {w : Fin n → α}
    {a : ℤ → α} (h : ∀ k : Fin n, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) : StrictMono w := by
  obtain _ | n := n
  · exact fun i ↦ i.elim0
  · exact strictMono_iff_lt_succ.2 fun i ↦
      ((h i.castSucc).2.trans_le (le_of_eq (by simp))).trans (h i.succ).1

end Fin

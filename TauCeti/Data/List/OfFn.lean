/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.Tuple.Basic
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Letter counts, duplicates, and permutations in `List.ofFn`

The number of occurrences of a letter `s` among the first `j` letters of the word
`f 0, …, f (k - 1)` is the number of positions `a < j` with `f a = s`
(`List.count_take_ofFn`). This is the occurrence-count form of `List.sum_take_ofFn`.

The concatenation `List.ofFn f ++ List.ofFn g` of the lists of two tuples has no duplicates if and
only if the map `Sum.elim f g` out of the sum of their index types is injective
(`List.nodup_ofFn_append_ofFn`), and similarly for three tuples
(`List.nodup_ofFn_append_ofFn_append_ofFn`). Inserting an element via `Fin.insertNth` yields a
permutation of `a :: List.ofFn f` (`List.ofFn_insertNth_perm`).

The list operation `List.contractNth l op`, which combines the entries `l` and `l + 1` of a list
with `op`, is the list analogue of `Fin.contractNth`: `List.ofFn (Fin.contractNth l op a)` is
`List.contractNth l op (List.ofFn a)` (`List.ofFn_contractNth`). Contracting shortens the list by
one when it has an entry `l + 1` (`List.length_contractNth_of_lt`) and leaves it unchanged
otherwise (`List.contractNth_of_length_le`).
-/

public section

open Finset

namespace List

/-- The number of occurrences of `s` among the first `j` letters of `List.ofFn f` is the number of
positions before `j` at which `f` takes the value `s`. -/
theorem count_take_ofFn {α : Type*} [DecidableEq α] {k : ℕ} (f : Fin k → α) (s : α) (j : ℕ) :
    ((ofFn f).take j).count s = #{a : Fin k | (a : ℕ) < j ∧ f a = s} := by
  induction j with
  | zero => simp
  | succ j ih =>
    -- Split off the position `j` from the positions before `j + 1`.
    simp_rw [Nat.lt_succ_iff_lt_or_eq, or_and_right, filter_or]
    rw [card_union_of_disjoint (disjoint_filter.mpr fun a _ h h' => by omega), ← ih,
      take_add_one, count_append, List.getElem?_ofFn]
    congr 1
    by_cases hj : j < k
    · have hfilt : ({a : Fin k | (a : ℕ) = j ∧ f a = s} : Finset (Fin k)) =
          ({⟨j, hj⟩} : Finset (Fin k)).filter (f · = s) := by
        ext a
        simp [Fin.ext_iff]
      rw [hfilt, Finset.filter_singleton]
      split_ifs with hs <;> simp [hs]
    · rw [card_eq_zero.mpr (filter_eq_empty_iff.mpr fun a _ ⟨h, _⟩ => hj (h ▸ a.isLt))]
      simp [hj]

variable {α : Type*} {l m n : ℕ}

/-- The concatenation of the lists of two tuples `f` and `g` has no duplicates if and only if the
map `Sum.elim f g` is injective. -/
theorem nodup_ofFn_append_ofFn {f : Fin m → α} {g : Fin n → α} :
    (ofFn f ++ ofFn g).Nodup ↔ Function.Injective (Sum.elim f g) := by
  rw [← ofFn_fin_append, nodup_ofFn, Fin.append_injective_iff, Sum.elim_injective]

/-- The concatenation of the lists of three tuples `f`, `g` and `h` has no duplicates if and only
if the map `Sum.elim (Sum.elim f g) h` is injective. -/
theorem nodup_ofFn_append_ofFn_append_ofFn {f : Fin l → α} {g : Fin m → α} {h : Fin n → α} :
    (ofFn f ++ ofFn g ++ ofFn h).Nodup ↔ Function.Injective (Sum.elim (Sum.elim f g) h) := by
  rw [nodup_append, nodup_ofFn_append_ofFn, nodup_ofFn, Sum.elim_injective]
  simp [mem_ofFn, Sum.forall, or_imp, forall_and]

/-- Inserting `a` at any position `p` of `f : Fin j → α` via `Fin.insertNth` yields a permutation
of `a :: List.ofFn f`. -/
theorem ofFn_insertNth_perm :
    ∀ {j : ℕ} (p : Fin (j + 1)) (a : α) (f : Fin j → α),
      (ofFn (p.insertNth a f)).Perm (a :: ofFn f)
  | 0, p, _, _ => p.cases (by simp) fun i => i.elim0
  | _ + 1, p, a, f => p.cases (by simp) fun q => by
      conv_lhs => rw [← Fin.cons_self_tail f, Fin.insertNth_succ_cons, ofFn_succ]
      conv_rhs => rw [← Fin.cons_self_tail f, ofFn_succ]
      simpa only [Fin.cons_zero, Fin.cons_succ] using
        ((ofFn_insertNth_perm q a (Fin.tail f)).cons (f 0)).trans (Perm.swap a (f 0) _)

/-- Combine the entries `l` and `l + 1` of a list with `op`, leaving the list unchanged when it has
no entry `l + 1`. This is the list analogue of `Fin.contractNth`. -/
def contractNth : ℕ → (α → α → α) → List α → List α
  | 0, op, x :: y :: L => op x y :: L
  | l + 1, op, x :: L => x :: contractNth l op L
  | _, _, L => L

/-- Contracting at position `0` combines the first two entries. -/
@[simp]
theorem contractNth_zero_cons_cons (op : α → α → α) (x y : α) (L : List α) :
    contractNth 0 op (x :: y :: L) = op x y :: L := by
  rw [contractNth]

/-- Contracting at position `l + 1` keeps the first entry and contracts the tail at `l`. -/
@[simp]
theorem contractNth_succ_cons (l : ℕ) (op : α → α → α) (x : α) (L : List α) :
    contractNth (l + 1) op (x :: L) = x :: contractNth l op L := by
  rw [contractNth]

/-- Contracting the empty list gives the empty list. -/
@[simp]
theorem contractNth_nil (l : ℕ) (op : α → α → α) : contractNth l op [] = [] := by
  cases l <;> simp [contractNth]

/-- Contracting a list of length one leaves it unchanged. -/
@[simp]
theorem contractNth_singleton (l : ℕ) (op : α → α → α) (x : α) : contractNth l op [x] = [x] := by
  cases l <;> simp [contractNth]

/-- Contracting two entries of a nonempty list leaves it nonempty. -/
theorem contractNth_cons_ne_nil (l : ℕ) (op : α → α → α) (x : α) (L : List α) :
    contractNth l op (x :: L) ≠ [] := by
  cases l <;> cases L <;> simp

/-- Contracting at a position `l` with no entry `l + 1` leaves the list unchanged. -/
theorem contractNth_of_length_le {l : ℕ} {L : List α} (op : α → α → α) (h : L.length ≤ l + 1) :
    contractNth l op L = L := by
  induction L generalizing l with
  | nil => simp
  | cons x L ih =>
    cases l with
    | zero => cases L <;> simp_all
    | succ l => simp [ih (l := l) (by simpa using h)]

/-- Contracting at a position `l` with an entry `l + 1` shortens the list by one. -/
theorem length_contractNth_of_lt {l : ℕ} {L : List α} (op : α → α → α) (h : l + 1 < L.length) :
    (contractNth l op L).length = L.length - 1 := by
  induction L generalizing l with
  | nil => simp at h
  | cons x L ih =>
    cases l with
    | zero =>
      cases L with
      | nil => simp at h
      | cons y L => simp
    | succ l =>
      simp only [contractNth_succ_cons, length_cons]
      rw [ih (by simpa using h)]
      simp only [length_cons] at h
      omega

/-- The list of entries of `Fin.contractNth l op a` is `List.contractNth l op` of the list of
entries of `a`. -/
theorem ofFn_contractNth {n : ℕ} (op : α → α → α) (a : Fin (n + 1) → α) (l : Fin n) :
    ofFn (Fin.contractNth l.castSucc op a) = contractNth l op (ofFn a) := by
  induction n with
  | zero => exact l.elim0
  | succ n ih =>
    cases l using Fin.cases with
    | zero =>
      rw [ofFn_succ, ofFn_succ (f := a), ofFn_succ (f := fun i ↦ a i.succ)]
      simp [Fin.contractNth]
    | succ l =>
      rw [ofFn_succ, ofFn_succ (f := a), Fin.val_succ, contractNth_succ_cons, ← ih]
      congr 2
      rw [← Fin.succ_castSucc]
      exact Fin.tail_contractNth_succ _ l.castSucc a

end List

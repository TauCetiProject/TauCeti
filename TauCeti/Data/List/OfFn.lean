/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.List.OfFn

/-!
# Letter counts, duplicates, and splits in `List.ofFn`

The number of occurrences of a letter `s` among the first `j` letters of the word
`f 0, …, f (k - 1)` is the number of positions `a < j` with `f a = s`
(`List.count_take_ofFn`). This is the occurrence-count form of `List.sum_take_ofFn`.

The concatenation `List.ofFn f ++ List.ofFn g` of the lists of two tuples has no duplicates if and
only if the map `Sum.elim f g` out of the sum of their index types is injective
(`List.nodup_ofFn_append_ofFn`), and similarly for three tuples
(`List.nodup_ofFn_append_ofFn_append_ofFn`). These extend `List.nodup_ofFn` from one tuple to
several.

This file also records two-index splits of `List.ofFn f` (`List.ofFn_eq_take_cons_of_lt`) and
their behaviour under swapping two positions (`List.ofFn_comp_swap_of_lt`).
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

/-- Splitting `List.ofFn f` at two indices `i < j`. -/
theorem ofFn_eq_take_cons_of_lt {α : Type*} {n : ℕ} (f : Fin n → α) {i j : Fin n}
    (hij : i.val < j.val) :
    ofFn f = (ofFn f).take i.val ++ f i ::
      ((ofFn f).drop (i.val + 1)).take (j.val - i.val - 1) ++
        f j :: (ofFn f).drop (j.val + 1) := by
  have _ := i.isLt; have _ := j.isLt
  refine ext_getElem (by simp; omega) fun k hk₁ _ ↦ ?_
  simp only [length_ofFn] at hk₁
  simp only [List.getElem_ofFn, getElem_append, getElem_cons, getElem_take, getElem_drop,
    length_append, length_cons, length_take, length_drop, length_ofFn]
  split_ifs <;> first | rfl | exact congrArg f (Fin.ext (by dsimp only; omega))

/-- Splitting `List.ofFn (f ∘ Equiv.swap i j)` at `i < j` swaps the entries at `i` and `j`. -/
theorem ofFn_comp_swap_of_lt {α : Type*} {n : ℕ} (f : Fin n → α) {i j : Fin n}
    (hij : i.val < j.val) :
    ofFn (f ∘ Equiv.swap i j) = (ofFn f).take i.val ++ f j ::
      ((ofFn f).drop (i.val + 1)).take (j.val - i.val - 1) ++
        f i :: (ofFn f).drop (j.val + 1) := by
  rw [ofFn_eq_take_cons_of_lt (f ∘ Equiv.swap i j) hij]
  have hswap (k : ℕ) (hk : k < n) (hki : k ≠ i.val) (hkj : k ≠ j.val) :
      (f ∘ Equiv.swap i j) ⟨k, hk⟩ = f ⟨k, hk⟩ := by
    rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne
      (mt (congrArg Fin.val) hki) (mt (congrArg Fin.val) hkj)]
  have htake : (ofFn (f ∘ Equiv.swap i j)).take i.val = (ofFn f).take i.val :=
    ext_getElem (by simp) fun k hk _ ↦ by
      simpa using hswap k (by simp at hk; omega) (by simp at hk; omega) (by simp at hk; omega)
  have hmid : ((ofFn (f ∘ Equiv.swap i j)).drop (i.val + 1)).take (j.val - i.val - 1) =
      ((ofFn f).drop (i.val + 1)).take (j.val - i.val - 1) :=
    ext_getElem (by simp) fun k hk _ ↦ by
      simpa using hswap (i.val + 1 + k) (by simp at hk; omega) (by omega) (by simp at hk; omega)
  have hdrop : (ofFn (f ∘ Equiv.swap i j)).drop (j.val + 1) = (ofFn f).drop (j.val + 1) :=
    ext_getElem (by simp) fun k hk _ ↦ by
      simpa using hswap (j.val + 1 + k) (by simp at hk; omega) (by omega) (by omega)
  simp only [htake, hmid, hdrop, Function.comp_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]

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

end List

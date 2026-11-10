/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Fin
import TauCeti.Data.Finset.Sort

/-!
# Sorted tuples

A monotone tuple `f : Fin n → α` is the sorted arrangement of its values, so it is determined by
how often each value occurs. Two monotone tuples in which every value `a` occurs equally often,
`#{i | f i = a} = #{i | g i = a}`, are therefore equal; the same holds for antitone tuples.

For an injective tuple `b` in a linear order, the increasing rearrangement `b ∘ Tuple.sort b` is
the increasing enumeration of the set of entries of `b`, so it only depends on that set. The entry
`b k` sits at position `(Tuple.sort b).symm k`, the number of entries below `b k`. For every tuple,
deleting the entry at `k` from `b` deletes the entry at that position from the rearrangement.

## Main results

* `Monotone.eq_of_card_filter_eq`: two monotone tuples with the same fibre cardinalities are equal.
* `Antitone.eq_of_card_filter_eq`: two antitone tuples with the same fibre cardinalities are equal.
* `Tuple.comp_sort_eq_comp_sort_of_range_eq`: injective tuples with the same set of entries have
  the same increasing rearrangement.
* `Tuple.val_sort_symm_apply`: the position of `b k` in the increasing rearrangement of an
  injective tuple `b` is the number of entries below `b k`.
* `Tuple.comp_succAbove_comp_sort`: deleting an entry of a tuple commutes with the increasing
  rearrangement.
-/

public section

open Finset

variable {n : ℕ} {α : Type*} [PartialOrder α] [DecidableEq α] {f g : Fin n → α}

/-- Two monotone tuples in which every value occurs equally often are equal. -/
theorem Monotone.eq_of_card_filter_eq (hf : Monotone f) (hg : Monotone g)
    (h : ∀ a, #{i | f i = a} = #{i | g i = a}) : f = g := by
  refine List.ofFn_injective ((List.perm_iff_count.2 fun a ↦ ?_).eq_of_sortedLE
    hf.sortedLE_ofFn hg.sortedLE_ofFn)
  have hcount (u : Fin n → α) : #{i | u i = a} = (List.ofFn u).count a := by
    simp
  rw [← hcount, ← hcount, h]

/-- Two antitone tuples in which every value occurs equally often are equal. -/
theorem Antitone.eq_of_card_filter_eq (hf : Antitone f) (hg : Antitone g)
    (h : ∀ a, #{i | f i = a} = #{i | g i = a}) : f = g :=
  Monotone.eq_of_card_filter_eq (α := αᵒᵈ) hf hg h

/-- A map from a finite type with the same range as an injective map is injective. -/
theorem Function.Injective.of_range_eq {ι β : Type*} [Finite ι] {f g : ι → β}
    (hf : Function.Injective f) (h : Set.range f = Set.range g) : Function.Injective g := by
  have e : ι ≃ Set.range g :=
    (Equiv.ofInjective f hf).trans (Equiv.subtypeEquivRight fun x => by rw [h])
  exact Subtype.val_injective.comp
    ((Finite.injective_iff_surjective_of_equiv e).2 Set.rangeFactorization_surjective)

namespace Tuple

variable {β : Type*} [LinearOrder β] {m : ℕ}

/-- The increasing rearrangement of an injective tuple is strictly increasing. -/
theorem strictMono_comp_sort {b : Fin m → β} (hb : Function.Injective b) :
    StrictMono (b ∘ sort b) :=
  (monotone_sort b).strictMono_of_injective (hb.comp (sort b).injective)

/-- Rearranging a tuple does not change its set of entries. -/
theorem range_comp_sort (b : Fin m → β) : Set.range (b ∘ sort b) = Set.range b :=
  (sort b).surjective.range_comp b

/-- The increasing rearrangement of an injective tuple only depends on its set of entries. -/
theorem comp_sort_eq_comp_sort_of_range_eq {b b' : Fin m → β} (hb : Function.Injective b)
    (h : Set.range b = Set.range b') : b ∘ sort b = b' ∘ sort b' := by
  have hb' : Function.Injective b' := hb.of_range_eq h
  exact ((strictMono_comp_sort hb).range_inj_of_wellFoundedLT (strictMono_comp_sort hb')).1 <| by
    rw [range_comp_sort, range_comp_sort, h]

/-- The increasing rearrangement of an injective tuple is the increasing enumeration of its set of
entries. -/
theorem comp_sort_eq_orderEmbOfFin {b : Fin m → β} (hb : Function.Injective b) :
    b ∘ sort b = (univ.image b).orderEmbOfFin (by rw [card_image_of_injective _ hb, card_fin]) :=
  orderEmbOfFin_unique _ (fun _ ↦ mem_image_of_mem _ (mem_univ _)) (strictMono_comp_sort hb)

/-- The position of the entry `b k` in the increasing rearrangement of an injective tuple `b` is
the number of entries smaller than `b k`. -/
theorem val_sort_symm_apply {b : Fin m → β} (hb : Function.Injective b) (k : Fin m) :
    ((sort b).symm k : ℕ) = #{i | b i < b k} := by
  have h := card_filter_lt_orderEmbOfFin (univ.image b)
    (by rw [card_image_of_injective _ hb, card_fin]) ((sort b).symm k)
  rw [← comp_sort_eq_orderEmbOfFin hb, Function.comp_apply, Equiv.apply_symm_apply,
    filter_image, card_image_of_injective _ hb] at h
  exact h.symm

/-- Deleting the entry at `k` from a tuple `b` deletes the entry at `(sort b).symm k` from its
increasing rearrangement. -/
theorem comp_succAbove_comp_sort {n : ℕ} {b : Fin (n + 1) → β} (k : Fin (n + 1)) :
    (b ∘ k.succAbove) ∘ sort (b ∘ k.succAbove) = (b ∘ sort b) ∘ ((sort b).symm k).succAbove := by
  refine Monotone.eq_of_card_filter_eq (monotone_sort _)
    ((monotone_sort b).comp (Fin.strictMono_succAbove _).monotone) fun a ↦ ?_
  have h1 := Fin.sum_univ_succAbove (fun x ↦ if b (sort b x) = a then 1 else 0 : Fin (n + 1) → ℕ)
    ((sort b).symm k)
  have h2 := Fin.sum_univ_succAbove (fun y ↦ if b y = a then 1 else 0 : Fin (n + 1) → ℕ) k
  have h3 := Equiv.sum_comp (sort b) (fun y ↦ if b y = a then 1 else 0 : Fin (n + 1) → ℕ)
  have h4 := Equiv.sum_comp (sort (b ∘ k.succAbove))
    (fun i : Fin n ↦ if b (k.succAbove i) = a then 1 else 0 : Fin n → ℕ)
  simp only [Equiv.apply_symm_apply, Function.comp_apply] at h1 h4 ⊢
  simp only [card_filter]
  -- Both sides count the occurrences of `a` among the entries of `b` other than the one at `k`:
  -- `h2` and `h3` reindex the total count along `sort b`, `h1` splits off the position
  -- `(sort b).symm k` from it, and `h4` reindexes the left-hand side along
  -- `sort (b ∘ k.succAbove)`.
  omega

end Tuple

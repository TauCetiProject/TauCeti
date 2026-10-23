/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Occurrence counts in finite families

`occCount f y` counts the indices at which a family `f` takes the value `y`.
For an infinite fiber its value is zero, following the convention of `Nat.card`.
Occurrence counts regroup sums over a finite family by fibers: each value in a finite set
covering the range is weighted by its occurrence count.

## Main results

* `Function.occCount_pos`: for a finite fiber, the count is positive exactly when it is nonempty.
* `Function.occCount_of_injective`: an injective function has count one on its range
  and zero outside.
* `Function.occCount_le_of_comp`, `Function.occCount_lt_of_comp`: comparison along embeddings.
* `Function.occCount_eq_card_preimage`: the count as the cardinality of a singleton preimage.
* `Function.prod_occCount_pow` and its additive form `Function.sum_occCount_nsmul`:
  regroup a product or sum by counting the occurrences of each value.
* `Function.occCount_castSucc`, `Function.occCount_succ`: split off the last or first position.
* `Function.sum_occCount_eq_card`: the total occurrence count is the cardinality of the index type.
* `Function.exists_perm_of_occCount_eq`: equal counts on finite families give a permutation.

-/

public section

open Finset

namespace Function

variable {X S : Type*}

/-- The cardinality of a fiber, counting occurrences of a value in a family. -/
noncomputable def occCount (f : X → S) (y : S) : ℕ := Nat.card {x // f x = y}

/-- Occurrence counts are natural cardinalities of fibers. -/
theorem occCount_def (f : X → S) (y : S) :
    occCount f y = Nat.card {x // f x = y} := (rfl)

/-- The occurrence count is the `Finset.card` of the indices taking the given value. -/
theorem occCount_eq_card_filter [Fintype X] [DecidableEq S] (f : X → S) (y : S) :
    occCount f y = (Finset.univ.filter (fun x => f x = y)).card := by
  rw [occCount_def, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The occurrence count as a sum of indicators over the positions. -/
theorem occCount_eq_sum [Fintype X] [DecidableEq S] (w : X → S) (a : S) :
    occCount w a = ∑ i : X, if w i = a then 1 else 0 := by
  rw [occCount_eq_card_filter, card_filter]

/-- When the target fiber is finite, occurrence counts grow along an embedding
preserving the values. -/
theorem occCount_le_of_comp {Y : Type*} {u : X → S} {v : Y → S}
    (e : X ↪ Y) (he : ∀ i, v (e i) = u i) (a : S) [Finite {y // v y = a}] :
    occCount u a ≤ occCount v a := by
  let f : {x // u x = a} ↪ {y // v y = a} :=
    e.subtypeMap (fun {x} hx => (he x).trans hx)
  exact Nat.card_le_card_of_injective f f.injective

/-- When the target fiber is finite, an embedding that misses an occurrence gives a
strictly smaller occurrence count. -/
theorem occCount_lt_of_comp {Y : Type*} {u : X → S} {v : Y → S} {a : S}
    [Finite {y // v y = a}] {j : Y} (e : X ↪ Y) (he : ∀ i, v (e i) = u i)
    (hj : v j = a) (hmiss : ∀ i, e i ≠ j) : occCount u a < occCount v a := by
  let f : {x // u x = a} ↪ {y // v y = a} :=
    e.subtypeMap (fun {x} hx => (he x).trans hx)
  have : Finite {x // u x = a} := Finite.of_injective f f.injective
  let _ := Fintype.ofFinite {x // u x = a}
  let _ := Fintype.ofFinite {y // v y = a}
  rw [occCount_def, occCount_def, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_not_surjective f f.injective
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj ⟨j, hj⟩
  exact hmiss x (congrArg Subtype.val hx)

/-- For a finite fiber, positive occurrence count is equivalent to the value being attained. -/
@[simp, grind =]
theorem occCount_pos (f : X → S) (y : S) [Finite {x // f x = y}] :
    0 < occCount f y ↔ ∃ x, f x = y := by
  simp only [occCount_def, Nat.card_pos_iff, nonempty_subtype,
    and_iff_left (inferInstance : Finite {x // f x = y})]

/-- Occurrence counts are the cardinalities of singleton preimages. -/
theorem occCount_eq_card_preimage (f : X → S) (y : S) :
    occCount f y = Nat.card (f ⁻¹' {y}) := by
  rw [occCount_def]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp only [Set.mem_preimage, Set.mem_singleton_iff])

/-- A value outside the range has occurrence count zero. -/
@[simp]
theorem occCount_of_notMem_range (f : X → S) (y : S) (h : y ∉ Set.range f) :
    occCount f y = 0 := by
  rw [occCount_eq_card_preimage, Set.preimage_singleton_eq_empty.mpr h]
  exact Nat.card_of_isEmpty

/-- An injective function gives occurrence count one precisely on its range. -/
theorem occCount_of_injective (f : X → S) (hinj : Function.Injective f) (y : S)
    [Decidable (∃ x, f x = y)] :
    occCount f y = if ∃ x, f x = y then 1 else 0 := by
  split_ifs with h
  · rw [occCount_eq_card_preimage]
    simpa only [Nat.card_unique] using
      Nat.card_preimage_of_injective hinj (Set.singleton_subset_iff.mpr h)
  · exact occCount_of_notMem_range f y h

/-- Every value of an injective function occurs exactly once. -/
@[simp]
theorem occCount_apply_of_injective (f : X → S) (hinj : Function.Injective f) (x : X) :
    occCount f (f x) = 1 := by
  classical
  rw [occCount_of_injective f hinj, ite_eq_left ⟨x, rfl⟩]

/-- Raising each weight to its occurrence count gives the product over all indices. -/
@[to_additive
  /-- Weighting each value by its occurrence count gives the sum over all indices. -/]
theorem prod_occCount_pow [Fintype X] {K : Type*} [CommMonoid K]
    (f : X → S) {T : Finset S} (hT : ∀ x, f x ∈ T) (weight : S → K) :
    ∏ y ∈ T, weight y ^ occCount f y = ∏ x, weight (f x) := by
  classical
  simpa only [Finset.prod_const, occCount_eq_card_filter] using
    Finset.prod_fiberwise_of_maps_to' (s := Finset.univ) (t := T) (g := f)
      (fun x _ => hT x) weight

/-- Occurrence counts over a finite set containing the range sum to the size of
the original family. -/
theorem sum_occCount_eq_card [Finite X] (f : X → S) {T : Finset S}
    (hT : ∀ x, f x ∈ T) : ∑ y ∈ T, occCount f y = Nat.card X := by
  classical
  let _ := Fintype.ofFinite X
  simpa [Nat.card_eq_fintype_card] using sum_occCount_nsmul f hT (fun _ => (1 : ℕ))

/-- Splitting off the last position: the occurrences of `a` in a word are those in its initial
segment together with a possible occurrence at the last position. -/
theorem occCount_castSucc [DecidableEq S] {n : ℕ} (w : Fin (n + 1) → S) (a : S) :
    occCount (w ∘ Fin.castSucc) a + (if w (Fin.last n) = a then 1 else 0) = occCount w a := by
  rw [occCount_eq_sum, occCount_eq_sum, Fin.sum_univ_castSucc]
  rfl

/-- Splitting off the first position: the occurrences of `a` in a word are those in its final
segment together with a possible occurrence at the first position. -/
theorem occCount_succ [DecidableEq S] {n : ℕ} (w : Fin (n + 1) → S) (a : S) :
    occCount (w ∘ Fin.succ) a + (if w 0 = a then 1 else 0) = occCount w a := by
  rw [occCount_eq_sum, occCount_eq_sum, Fin.sum_univ_succ, Nat.add_comm]
  rfl

/-- Two families on a finite index type with equal occurrence counts differ by a permutation. -/
theorem exists_perm_of_occCount_eq [Finite X] {u v : X → S}
    (h : ∀ a, occCount u a = occCount v a) :
    ∃ σ : Equiv.Perm X, v ∘ σ = u := by
  classical
  let _ := Fintype.ofFinite X
  refine ⟨Equiv.ofFiberEquiv (f := u) (g := v) fun c =>
    Fintype.equivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact (occCount_def u c).symm.trans ((h c).trans (occCount_def v c))), ?_⟩
  funext i
  exact Equiv.ofFiberEquiv_map _ i

end Function

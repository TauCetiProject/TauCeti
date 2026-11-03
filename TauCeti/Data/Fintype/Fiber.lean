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
public import Mathlib.Data.Multiset.Fintype

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
* `Function.exists_equiv_of_occCount_eq`, `Function.exists_perm_of_occCount_eq`: equal counts on
  finite families give a bijection of their index types.
* `Function.occCount_subtype_ne`, `Function.exists_equiv_subtype_ne_of_occCount_eq`: deleting the
  indices with value `z` keeps the other counts, so equal counts away from `z` match the
  remaining indices.
* `Finset.prod_filter_subtype_ne`: a product over one fiber ignores the deletion of another.
* `Finset.prod_filter_subtype_ne_equiv`: a product over one fiber is preserved by a value-preserving
  matching of the indices away from another fiber.
* `Function.occCount_eq_count_map_univ`: occurrence counts as multiset multiplicities.
* `Function.exists_perm_of_map_univ_eq`: equal multisets give a permutation.
* `Multiset.exists_map_univ_eq`: enumeration of a multiset by any type of matching size.

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

/-- Two finite families with equal occurrence counts are related by a bijection of their
index types. -/
theorem exists_equiv_of_occCount_eq {Y : Type*} [Finite X] [Finite Y] {u : X → S} {v : Y → S}
    (h : ∀ a, occCount u a = occCount v a) :
    ∃ σ : X ≃ Y, v ∘ σ = u := by
  classical
  let _ := Fintype.ofFinite X
  let _ := Fintype.ofFinite Y
  refine ⟨Equiv.ofFiberEquiv (f := u) (g := v) fun c =>
    Fintype.equivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact (occCount_def u c).symm.trans ((h c).trans (occCount_def v c))), ?_⟩
  funext i
  exact Equiv.ofFiberEquiv_map _ i

/-- Two families on a finite index type with equal occurrence counts differ by a permutation. -/
theorem exists_perm_of_occCount_eq [Finite X] {u v : X → S}
    (h : ∀ a, occCount u a = occCount v a) :
    ∃ σ : Equiv.Perm X, v ∘ σ = u :=
  exists_equiv_of_occCount_eq h

/-- Deleting the indices at which a family takes the value `z` does not change the occurrence
counts of the other values. -/
@[simp]
theorem occCount_subtype_ne (f : X → S) {z a : S} (ha : a ≠ z) :
    occCount (fun x : {x // f x ≠ z} => f x) a = occCount f a := by
  rw [occCount_def, occCount_def]
  exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtype (p := fun x => f x ≠ z)
    (q := fun x => f x = a) fun hx => hx ▸ ha)

/-- After deleting the indices at which a family takes the value `z`, the value `z` no longer
occurs. -/
theorem occCount_subtype_ne_self (f : X → S) (z : S) :
    occCount (fun x : {x // f x ≠ z} => f x) z = 0 := by
  rw [occCount_def, Nat.card_eq_zero]
  exact Or.inl ⟨fun x => x.1.2 x.2⟩

/-- Two finite families with the same occurrence counts away from a value `z` are related by a
bijection between the indices at which they do not take the value `z`. -/
theorem exists_equiv_subtype_ne_of_occCount_eq {Y : Type*} [Finite X] [Finite Y] {u : X → S}
    {v : Y → S} {z : S} (h : ∀ a, a ≠ z → occCount u a = occCount v a) :
    ∃ σ : {x // u x ≠ z} ≃ {y // v y ≠ z}, ∀ x, v (σ x) = u x := by
  obtain ⟨σ, hσ⟩ := exists_equiv_of_occCount_eq (u := fun x : {x // u x ≠ z} => u x)
    (v := fun y : {y // v y ≠ z} => v y) fun a => by
      by_cases ha : a = z
      · rw [ha, occCount_subtype_ne_self, occCount_subtype_ne_self]
      · rw [occCount_subtype_ne u ha, occCount_subtype_ne v ha, h a ha]
  exact ⟨σ, congrFun hσ⟩

/-- Occurrence counts are the multiplicities in the multiset of values of a finite family. -/
theorem occCount_eq_count_map_univ [Fintype X] [DecidableEq S] (f : X → S) (y : S) :
    occCount f y = (Finset.univ.val.map f).count y := by
  rw [occCount_eq_card_filter, Multiset.count_map, ← Finset.filter_val, Finset.card_val]
  congr 1
  exact Finset.filter_congr fun _ _ => eq_comm

/-- Finite families with the same multiset of values differ by a permutation of their indices. -/
theorem exists_perm_of_map_univ_eq [Fintype X] {u v : X → S}
    (h : Finset.univ.val.map u = Finset.univ.val.map v) :
    ∃ σ : Equiv.Perm X, v ∘ σ = u := by
  classical
  apply exists_perm_of_occCount_eq
  intro a
  rw [occCount_eq_count_map_univ, occCount_eq_count_map_univ, h]

end Function

namespace Finset

variable {X S : Type*}

/-- A product over the indices at which a family takes a value `a` is unchanged by first deleting
the indices at which it takes another value `z`. -/
@[to_additive /-- A sum over the indices at which a family takes a value `a` is unchanged by first
deleting the indices at which it takes another value `z`. -/]
theorem prod_filter_subtype_ne [Fintype X] [DecidableEq S] {M : Type*} [CommMonoid M]
    (f : X → S) (g : X → M) {z a : S} (ha : a ≠ z) :
    ∏ x ∈ ({x | f x = a} : Finset {x // f x ≠ z}), g x = ∏ x with f x = a, g x := by
  rw [prod_filter, prod_filter, ← Fintype.prod_subtype_mul_prod_subtype (fun x => f x ≠ z),
    Fintype.prod_eq_one (fun x : {x // ¬f x ≠ z} => if f x = a then g x else 1)
      fun x => ite_eq_right_iff.mpr fun hx => absurd (hx ▸ ha) x.2, mul_one]

/-- Matching the indices at which two families do not take a value `z` along a bijection that
preserves the values does not change a product over the indices at which they take another value
`a`. -/
@[to_additive /-- Matching the indices at which two families do not take a value `z` along a
bijection that preserves the values does not change a sum over the indices at which they take
another value `a`. -/]
theorem prod_filter_subtype_ne_equiv {Y : Type*} [Fintype X] [Fintype Y] [DecidableEq S]
    {M : Type*} [CommMonoid M] (u : X → S) (v : Y → S) (g : Y → M) {z a : S}
    (σ : {x // u x ≠ z} ≃ {y // v y ≠ z}) (hσ : ∀ x, v (σ x) = u x) (ha : a ≠ z) :
    ∏ x ∈ ({x | u x = a} : Finset {x // u x ≠ z}), g (σ x) = ∏ y with v y = a, g y := by
  rw [← prod_filter_subtype_ne v g ha, prod_filter, prod_filter]
  exact Fintype.prod_equiv σ _ _ fun x => by simp only [hσ x]

end Finset

namespace Multiset

variable {X S : Type*}

/-- Any multiset with as many entries as a finite type can be enumerated by that type. -/
theorem exists_map_univ_eq [Fintype X] (s : Multiset S) (h : s.card = Fintype.card X) :
    ∃ f : X → S, Finset.univ.val.map f = s := by
  classical
  let e : X ≃ s := Fintype.equivOfCardEq (by simp [h])
  refine ⟨(fun x : s => (x : S)) ∘ e, ?_⟩
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv, Multiset.map_univ_coe]

end Multiset

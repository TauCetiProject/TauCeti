/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Group.WordMetric
public import TauCeti.GroupTheory.TitsSystem.Basic

/-!
# The length function on the Weyl group of a Tits system

The simple reflections of a Tits system generate its Weyl group `W = N / (B ∩ N)`, so they form a
generating family `TauCeti.TitsSystem.simpleGenerators` in the sense of `Group.Generators`.
Mathlib's word length `Group.Generators.wordLength` with respect to that family is the length
function `ℓ` of the Weyl group: the least number of simple reflections whose product is a given
element.

Because every simple reflection is an involution, a word in the generators and their inverses
evaluates to the product of the underlying list of simple reflections. This file records that
translation, so that the length can be read off plain lists of simple reflections, together with
the elementary estimates that the multiplication rules for Bruhat cells rest on: a simple
reflection has length one, and multiplying by one changes the length by at most one.

## Main declarations

* `TauCeti.TitsSystem.simpleGenerators`: the simple reflections as a generating family of the
  Weyl group.
* `TauCeti.TitsSystem.wordLength_le_iff`: the length is at most `n` exactly when the element is
  the product of at most `n` simple reflections.
* `TauCeti.TitsSystem.exists_prod_eq_of_wordLength`: every element is the product of a list of
  simple reflections whose length is its word length, that is, of a reduced word.
* `TauCeti.TitsSystem.wordLength_simple`: a simple reflection has length one.
* `TauCeti.TitsSystem.wordLength_simple_mul_le` and
  `TauCeti.TitsSystem.wordLength_le_wordLength_simple_mul_add_one`: multiplication by a simple
  reflection changes the length by at most one.
* `TauCeti.TitsSystem.wordLength_mul_simple_eq_wordLength_simple_mul_inv`: since the length is
  invariant under inversion, right multiplication by a simple reflection is governed by left
  multiplication on the inverse.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §1, no. 1 and §2, no. 4.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 29.3.
-/

public section

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

/-- The simple reflections, as a generating family of the Weyl group. -/
noncomputable def simpleGenerators : Group.Generators T.WeylGroup T.simple :=
  Group.Generators.ofSet T.closure_simple

/-- The generating family of simple reflections is the inclusion of `T.simple`. -/
@[simp]
theorem simpleGenerators_val : T.simpleGenerators.val = Subtype.val :=
  Group.Generators.ofSet_val _

local prefix:100 "ℓ " => T.simpleGenerators.wordLength

/-- A word in the simple reflections and their inverses evaluates to the product of the
underlying list of simple reflections. -/
@[simp]
theorem wordProd_eq_prod (l : List (T.simple × Bool)) :
    T.simpleGenerators.wordProd l = (l.map fun x ↦ (x.1 : T.WeylGroup)).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨⟨s, hs⟩, b⟩ := x
    rw [Group.Generators.wordProd_cons, ih, List.map_cons, List.prod_cons]
    cases b <;> simp [T.inv_simple hs]

/-- Reversing a list of simple reflections inverts its product. -/
theorem prod_reverse_eq_inv_prod {l : List T.WeylGroup} (hl : ∀ s ∈ l, s ∈ T.simple) :
    l.reverse.prod = l.prod⁻¹ := by
  rw [List.prod_inv_reverse, List.map_congr_left (f := fun x ↦ x⁻¹) (g := fun x ↦ x)
    fun s hs ↦ T.inv_simple (hl s hs), List.map_id']

/-- **Length through lists of simple reflections.** The length of `w` is at most `n` exactly when
`w` is the product of a list of at most `n` simple reflections. -/
theorem wordLength_le_iff {w : T.WeylGroup} {n : ℕ} :
    ℓ w ≤ n ↔
      ∃ l : List T.WeylGroup, (∀ s ∈ l, s ∈ T.simple) ∧ l.length ≤ n ∧ l.prod = w := by
  rw [Group.Generators.wordLength_le_iff]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l.map fun x ↦ (x.1 : T.WeylGroup), ?_, by simpa using hl,
      (T.wordProd_eq_prod l).symm⟩
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ x _ rfl
    exact x.1.2
  · rintro ⟨l, hl, hlen, rfl⟩
    refine ⟨l.attach.map fun x ↦ ((⟨x.1, hl x.1 x.2⟩ : T.simple), true), by simpa using hlen, ?_⟩
    rw [T.wordProd_eq_prod, List.map_map]
    exact congrArg List.prod (List.attach_map_subtype_val l)

/-- The product of a list of simple reflections has length at most the length of the list. -/
theorem wordLength_prod_le {l : List T.WeylGroup} (hl : ∀ s ∈ l, s ∈ T.simple) :
    ℓ l.prod ≤ l.length :=
  T.wordLength_le_iff.mpr ⟨l, hl, le_rfl, rfl⟩

/-- Every element of the Weyl group is the product of a list of simple reflections whose length is
the word length of the element: a reduced word. -/
theorem exists_prod_eq_of_wordLength (w : T.WeylGroup) :
    ∃ l : List T.WeylGroup, (∀ s ∈ l, s ∈ T.simple) ∧ l.length = ℓ w ∧ l.prod = w := by
  obtain ⟨l, hl, hlen, rfl⟩ := (T.wordLength_le_iff (w := w)).mp le_rfl
  exact ⟨l, hl, le_antisymm hlen (T.wordLength_prod_le hl), rfl⟩

/-- A simple reflection has length one. -/
@[simp]
theorem wordLength_simple {s : T.WeylGroup} (hs : s ∈ T.simple) : ℓ s = 1 := by
  refine le_antisymm
    (T.wordLength_le_iff.mpr ⟨[s], by simpa using hs, le_rfl, List.prod_singleton⟩) ?_
  exact Nat.one_le_iff_ne_zero.mpr fun h ↦
    T.simple_ne_one hs ((Group.Generators.wordLength_eq_zero_iff _).mp h)

/-- Left multiplication by a simple reflection increases the length by at most one. -/
theorem wordLength_simple_mul_le {s : T.WeylGroup} (hs : s ∈ T.simple) (w : T.WeylGroup) :
    ℓ (s * w) ≤ ℓ w + 1 := by
  calc ℓ (s * w) ≤ ℓ s + ℓ w := Group.Generators.wordLength_mul_le _ _ _
    _ = ℓ w + 1 := by rw [T.wordLength_simple hs, add_comm]

/-- Right multiplication by a simple reflection increases the length by at most one. -/
theorem wordLength_mul_simple_le (w : T.WeylGroup) {s : T.WeylGroup} (hs : s ∈ T.simple) :
    ℓ (w * s) ≤ ℓ w + 1 := by
  calc ℓ (w * s) ≤ ℓ w + ℓ s := Group.Generators.wordLength_mul_le _ _ _
    _ = ℓ w + 1 := by rw [T.wordLength_simple hs]

/-- Left multiplication by a simple reflection decreases the length by at most one. -/
theorem wordLength_le_wordLength_simple_mul_add_one {s : T.WeylGroup} (hs : s ∈ T.simple)
    (w : T.WeylGroup) : ℓ w ≤ ℓ (s * w) + 1 := by
  simpa only [T.simple_mul_simple_cancel_left hs] using T.wordLength_simple_mul_le hs (s * w)

/-- Right multiplication by a simple reflection decreases the length by at most one. -/
theorem wordLength_le_wordLength_mul_simple_add_one (w : T.WeylGroup) {s : T.WeylGroup}
    (hs : s ∈ T.simple) : ℓ w ≤ ℓ (w * s) + 1 := by
  simpa only [T.simple_mul_simple_cancel_right w hs] using T.wordLength_mul_simple_le (w * s) hs

/-- The length of `w s` is the length of `s w⁻¹`. -/
theorem wordLength_mul_simple_eq_wordLength_simple_mul_inv (w : T.WeylGroup) {s : T.WeylGroup}
    (hs : s ∈ T.simple) : ℓ (w * s) = ℓ (s * w⁻¹) := by
  rw [← Group.Generators.wordLength_inv _ (w * s), mul_inv_rev, T.inv_simple hs]

end TauCeti.TitsSystem

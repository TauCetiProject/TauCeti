/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Prod

/-!
# Inversions of a map on a finset

For a map `f : α → β` between linear orders and a finset `s` of `α`, the inversions of `f` on `s`
are the pairs `a < b` of elements of `s` whose order `f` reverses, `f b < f a`. When `f` is
injective on `s`, the sign `(-1) ^ #(s.inversions f)` is the sign of the permutation comparing the
order of `s` with the order of its image: for `s = univ` and a permutation `σ` of `Fin n` it is the
sign of `σ`, by `TauCeti.sign_eq_neg_one_pow_card_inversion`.

These signs compare the Koszul signs of a finset with respect to two linear orders. Inserting a new
element `a` changes the inversion count by the number of elements of `s` lying on different sides
of `a` in the two orders, and the signs are multiplicative along a composite of injective maps.
They are the vertex signs of the reindexing isomorphism of a cube complex along a reordering of its
index set.

## Main definitions

* `Finset.inversions f s`: the pairs `(a, b)` of elements of `s` with `a < b` and `f b < f a`.

## Main results

* `Finset.inversions_eq_empty_of_strictMonoOn`: a strictly monotone map has no inversions.
* `Finset.card_inversions_insert`: the inversions created by inserting a new element.
* `Finset.neg_one_pow_card_inversions_insert`: the sign of `insert a s` is the sign of `s` times
  the two Koszul signs `(-1) ^ #{b ∈ s | b < a}` and `(-1) ^ #{b ∈ s | f b < f a}` of `a`.
* `Finset.neg_one_pow_card_inversions_comp`: the sign of a composite `g ∘ f` is the product of the
  sign of `f` on `s` and the sign of `g` on the image of `s`.
-/

public section

open Function

namespace Finset

variable {α β γ R : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- The inversions of a map `f` on a finset `s` of a linear order: the pairs `(a, b)` of elements
of `s` with `a < b` whose order `f` reverses, `f b < f a`. -/
def inversions (f : α → β) (s : Finset α) : Finset (α × α) :=
  {p ∈ s ×ˢ s | p.1 < p.2 ∧ f p.2 < f p.1}

@[simp]
theorem mem_inversions {f : α → β} {s : Finset α} {p : α × α} :
    p ∈ s.inversions f ↔ p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2 ∧ f p.2 < f p.1 := by
  simp [inversions, and_assoc]

@[simp]
theorem inversions_empty (f : α → β) : (∅ : Finset α).inversions f = ∅ := by
  ext
  simp

/-- A map that is strictly monotone on `s` has no inversions on `s`. -/
theorem inversions_eq_empty_of_strictMonoOn {f : α → β} {s : Finset α}
    (hf : StrictMonoOn f s) : s.inversions f = ∅ := by
  ext p
  simp only [mem_inversions, notMem_empty, iff_false, not_and]
  exact fun h₁ h₂ h ↦ (hf h₁ h₂ h).asymm

@[simp]
theorem inversions_id (s : Finset α) : s.inversions id = ∅ :=
  inversions_eq_empty_of_strictMonoOn (strictMono_id.strictMonoOn _)

/-- Inserting a new element `a` into `s` creates the inversions `(b, a)` for the `b < a` with
`f a < f b`, and `(a, b)` for the `a < b` with `f b < f a`. -/
theorem card_inversions_insert (f : α → β) {s : Finset α} {a : α} (ha : a ∉ s) :
    #((insert a s).inversions f) =
      #(s.inversions f) + #{b ∈ s | b < a ∧ f a < f b} + #{b ∈ s | a < b ∧ f b < f a} := by
  have h : (insert a s).inversions f = s.inversions f ∪ {b ∈ s | b < a ∧ f a < f b} ×ˢ {a} ∪
      {a} ×ˢ {b ∈ s | a < b ∧ f b < f a} := by
    ext ⟨x, y⟩
    simp only [mem_inversions, mem_insert, mem_union, mem_product, mem_filter, mem_singleton]
    constructor
    · rintro ⟨rfl | hx, rfl | hy, hxy, hf⟩
      · exact absurd hxy (lt_irrefl _)
      · exact Or.inr ⟨rfl, hy, hxy, hf⟩
      · exact Or.inl (Or.inr ⟨⟨hx, hxy, hf⟩, rfl⟩)
      · exact Or.inl (Or.inl ⟨hx, hy, hxy, hf⟩)
    · rintro ((⟨hx, hy, hxy, hf⟩ | ⟨⟨hx, hxy, hf⟩, rfl⟩) | ⟨rfl, hy, hxy, hf⟩)
      · exact ⟨Or.inr hx, Or.inr hy, hxy, hf⟩
      · exact ⟨Or.inr hx, Or.inl rfl, hxy, hf⟩
      · exact ⟨Or.inl rfl, Or.inr hy, hxy, hf⟩
  rw [h, card_union_of_disjoint, card_union_of_disjoint, card_product, card_product,
    card_singleton, mul_one, one_mul]
  · refine disjoint_left.2 ?_
    rintro ⟨x, y⟩ hp
    simp only [mem_inversions] at hp
    simp only [mem_product, mem_filter, mem_singleton, not_and]
    rintro - rfl
    exact ha hp.2.1
  · refine disjoint_left.2 ?_
    rintro ⟨x, y⟩ hp
    simp only [mem_union, mem_inversions, mem_product, mem_filter, mem_singleton] at hp
    simp only [mem_product, mem_singleton, not_and]
    rintro rfl
    rcases hp with ⟨hx, -⟩ | ⟨⟨hx, -⟩, -⟩ <;> exact absurd hx ha

/-- The exact form of `Finset.neg_one_pow_card_inversions_insert`, before reduction modulo `2`. -/
private theorem card_inversions_insert_add_two_mul {f : α → β} {s : Finset α} {a : α}
    (hf : Set.InjOn f ↑(insert a s)) (ha : a ∉ s) :
    #((insert a s).inversions f) + 2 * #{b ∈ s | b < a ∧ f b < f a} =
      #(s.inversions f) + #{b ∈ s | b < a} + #{b ∈ s | f b < f a} := by
  have hne : ∀ b ∈ s, f b ≠ f a := fun b hb h ↦
    ha (hf (by simp [hb]) (by simp) h ▸ hb)
  have hlt : #{b ∈ s | b < a} = #{b ∈ s | b < a ∧ f a < f b} + #{b ∈ s | b < a ∧ f b < f a} := by
    rw [← card_union_of_disjoint (disjoint_filter.2 fun _ _ h₁ h₂ ↦ h₁.2.asymm h₂.2), ← filter_or]
    refine congrArg card (filter_congr fun b hb ↦ ?_)
    rcases (hne b hb).lt_or_gt with h | h <;> simp [h, h.asymm]
  have hflt : #{b ∈ s | f b < f a} =
      #{b ∈ s | a < b ∧ f b < f a} + #{b ∈ s | b < a ∧ f b < f a} := by
    rw [← card_union_of_disjoint (disjoint_filter.2 fun _ _ h₁ h₂ ↦ h₁.1.asymm h₂.1), ← filter_or]
    refine congrArg card (filter_congr fun b hb ↦ ?_)
    have hab : b ≠ a := fun h ↦ ha (h ▸ hb)
    rcases hab.lt_or_gt with h | h <;> simp [h, h.asymm]
  rw [card_inversions_insert f ha, hlt, hflt]
  omega

/-- **The sign of inserting a new element.** For `f` injective on `insert a s` with `a ∉ s`, the
sign `(-1) ^ #(inversions f)` of `insert a s` is that of `s` times the Koszul signs of `a` in `s`
for the order of `α` and for the order pulled back along `f`. -/
theorem neg_one_pow_card_inversions_insert [Monoid R] [HasDistribNeg R] {f : α → β}
    {s : Finset α} {a : α} (hf : Set.InjOn f ↑(insert a s)) (ha : a ∉ s) :
    (-1 : R) ^ #((insert a s).inversions f) =
      (-1) ^ #{b ∈ s | b < a} * (-1) ^ #{b ∈ s | f b < f a} * (-1) ^ #(s.inversions f) := by
  rw [← pow_add, ← pow_add]
  refine neg_one_pow_congr ?_
  have := card_inversions_insert_add_two_mul hf ha
  simp only [Nat.even_iff]
  omega

/-- The inversion count of a composite has the parity of the sum of the inversion counts of the
two factors. -/
private theorem even_card_inversions_comp_add {g : β → γ} (f : α ↪ β) {s : Finset α}
    (hg : Set.InjOn g ↑(s.map f)) :
    Even (#(s.inversions (g ∘ f)) + #(s.inversions f) + #((s.map f).inversions g)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [map_insert] at hg ⊢
    have hfa : f a ∉ s.map f := by simpa using ha
    have hgs : Set.InjOn g ↑(s.map f) := hg.mono (by simp [Set.subset_insert])
    have hgf : Set.InjOn (g ∘ f) ↑(insert a s) := fun x hx y hy h ↦
      f.injective (hg (by simpa using hx) (by simpa using hy) h)
    have h₁ := card_inversions_insert_add_two_mul hgf ha
    have h₂ := card_inversions_insert_add_two_mul (f.injective.injOn (s := ↑(insert a s))) ha
    have h₃ := card_inversions_insert_add_two_mul hg hfa
    simp only [filter_map, card_map, comp_apply] at h₁ h₃
    have := ih hgs
    simp only [Nat.even_iff] at this ⊢
    omega

/-- **The sign of a composite.** For an embedding `f` and a map `g` injective on the image of
`s`, the sign of `g ∘ f` on `s` is the sign of `f` on `s` times the sign of `g` on `s.map f`. -/
theorem neg_one_pow_card_inversions_comp [Monoid R] [HasDistribNeg R] {g : β → γ} (f : α ↪ β)
    {s : Finset α} (hg : Set.InjOn g ↑(s.map f)) :
    (-1 : R) ^ #(s.inversions (g ∘ f)) =
      (-1) ^ #(s.inversions f) * (-1) ^ #((s.map f).inversions g) := by
  rw [← pow_add]
  refine neg_one_pow_congr ?_
  have := even_card_inversions_comp_add f hg
  simp only [Nat.even_iff] at this ⊢
  omega

end Finset

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Prod

/-!
# Inversions of a map on a finite set

For a map `f : α → β` between linear orders and a finite set `s ⊆ α`, the inversions of `f` on
`s` are the pairs `a < b` of elements of `s` whose order `f` reverses, `f b < f a`. When `f` is
injective, the parity of their number is the sign of the permutation of `s` obtained by comparing
the order of `s` with the order of its image `f(s)`. For a permutation `σ` of `Fin n`,
`TauCeti.sign_eq_neg_one_pow_card_inversion` identifies `(-1) ^ #(Finset.univ.inversions σ)` with
`Equiv.Perm.sign σ`.

These signs compare two orderings of the same finite set. In a signed cube totalization the edge
`S ⟶ S ∪ {a}` carries the sign `(-1) ^ #{b ∈ S | b < a}`, and reordering the indices of the cube
by `f` changes these signs by the inversion signs of `f` on the two vertices of the edge
(`Finset.neg_one_pow_card_inversions_insert`). Inversion signs are multiplicative under
composition (`Finset.neg_one_pow_card_inversions_comp`).

## Main definitions

* `Finset.inversions f s`: the pairs `(a, b)` of elements of `s` with `a < b` and `f b < f a`.

## Main results

* `Finset.inversions_univ`: on a whole finite type, the inversions are all pairs `a < b` with
  `f b < f a`.
* `Finset.card_inversions_insert`: adjoining a new element `a` to `s` adds the inversions
  involving `a`.
* `Finset.card_inversions_insert_add_card_filter_lt`: for an injective map, the same comparison
  of `insert a s` with `s` as a count of elements, up to an even number.
* `Finset.neg_one_pow_card_inversions_insert`: the inversion sign of an injective map on
  `insert a s`, compared with that on `s`, is the sign relating the position of `a` in `s` to the
  position of `f a` in `f(s)`.
* `Finset.even_card_inversions_comp`: the inversion counts of `f` on `s`, of `g` on `f(s)` and of
  `g ∘ f` on `s` add up to an even number.
* `Finset.neg_one_pow_card_inversions_comp`: the inversion sign of `g ∘ f` on `s` is the product
  of the inversion signs of `f` on `s` and of `g` on `f(s)`.
-/

public section

open Function

namespace Finset

variable {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- The inversions of `f` on `s`: the pairs `(a, b)` of elements of `s` with `a < b` whose order
`f` reverses, `f b < f a`. -/
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

/-- A monotone map has no inversions. -/
theorem inversions_eq_empty_of_monotone {f : α → β} (hf : Monotone f) (s : Finset α) :
    s.inversions f = ∅ := by
  ext p
  simp only [mem_inversions, notMem_empty, iff_false, not_and]
  exact fun _ _ h ↦ (hf h.le).not_gt

/-- On the whole of a finite type, the inversions of `f` are all the pairs `a < b` with
`f b < f a`. -/
theorem inversions_univ [Fintype α] (f : α → β) :
    univ.inversions f = univ.filter fun p : α × α ↦ p.1 < p.2 ∧ f p.2 < f p.1 := by
  rw [inversions, univ_product_univ]

@[simp]
theorem inversions_id (s : Finset α) : s.inversions id = ∅ :=
  inversions_eq_empty_of_monotone monotone_id s

/-- Adjoining a new element `a` to `s` adds the inversions `(b, a)` with `b < a` and the
inversions `(a, b)` with `a < b`. -/
theorem card_inversions_insert (f : α → β) {s : Finset α} {a : α} (ha : a ∉ s) :
    #((insert a s).inversions f) = #(s.inversions f) + #{b ∈ s | b < a ∧ f a < f b} +
      #{b ∈ s | a < b ∧ f b < f a} := by
  have hdecomp : (insert a s).inversions f = s.inversions f ∪
      {b ∈ s | b < a ∧ f a < f b}.image (·, a) ∪ {b ∈ s | a < b ∧ f b < f a}.image (a, ·) := by
    ext ⟨x, y⟩
    simp only [mem_inversions, mem_insert, mem_union, mem_image, mem_filter, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl | hx, rfl | hy, hxy, hf⟩
      · exact absurd hxy (lt_irrefl _)
      · exact Or.inr ⟨y, ⟨hy, hxy, hf⟩, rfl, rfl⟩
      · exact Or.inl (Or.inr ⟨x, ⟨hx, hxy, hf⟩, rfl, rfl⟩)
      · exact Or.inl (Or.inl ⟨hx, hy, hxy, hf⟩)
    · rintro ((⟨hx, hy, hxy, hf⟩ | ⟨b, ⟨hb, hba, hfb⟩, rfl, rfl⟩) | ⟨b, ⟨hb, hab, hfb⟩, rfl, rfl⟩)
      · exact ⟨Or.inr hx, Or.inr hy, hxy, hf⟩
      · exact ⟨Or.inr hb, Or.inl rfl, hba, hfb⟩
      · exact ⟨Or.inl rfl, Or.inr hb, hab, hfb⟩
  rw [hdecomp, card_union_of_disjoint, card_union_of_disjoint,
    card_image_of_injective _ (Prod.mk_left_injective a),
    card_image_of_injective _ (Prod.mk_right_injective a)]
  · rw [disjoint_left]
    simp only [mem_inversions, mem_image, mem_filter, not_exists, not_and]
    rintro p ⟨-, hp, -⟩ b - rfl
    exact ha hp
  · rw [disjoint_left]
    simp only [mem_union, mem_inversions, mem_image, mem_filter, not_exists, not_and]
    rintro p (⟨hp, -⟩ | ⟨b, ⟨hb, -⟩, rfl⟩) c - h
    · subst h
      exact ha hp
    · obtain ⟨rfl, -⟩ := Prod.mk.inj h
      exact ha hb

/-- For an injective map and `a ∉ s`, the inversions on `insert a s` and the elements of `s`
below `a` together count the inversions on `s` and the elements of `s` whose image lies below
`f a`, up to an even number. -/
theorem card_inversions_insert_add_card_filter_lt {f : α → β} (hf : Injective f)
    {s : Finset α} {a : α} (ha : a ∉ s) :
    #((insert a s).inversions f) + #{b ∈ s | b < a} =
      #(s.inversions f) + #{b ∈ s | f b < f a} + 2 * #{b ∈ s | b < a ∧ f a < f b} := by
  have hne {b : α} (hb : b ∈ s) : b ≠ a := fun h ↦ ha (h ▸ hb)
  -- Split the elements below `a`, and those whose image lies below `f a`, according to the
  -- other order.
  have h₁ := card_filter_add_card_filter_not (s := {b ∈ s | b < a}) (fun b ↦ f b < f a)
  have h₂ := card_filter_add_card_filter_not (s := {b ∈ s | f b < f a}) (fun b ↦ b < a)
  simp only [filter_filter] at h₁ h₂
  rw [filter_congr fun b hb ↦ show b < a ∧ ¬f b < f a ↔ b < a ∧ f a < f b by
    grind [hf.ne (hne hb)]] at h₁
  rw [filter_congr fun b hb ↦ show f b < f a ∧ ¬b < a ↔ a < b ∧ f b < f a by
    grind [hne hb]] at h₂
  rw [filter_congr fun b _ ↦ show f b < f a ∧ b < a ↔ b < a ∧ f b < f a from and_comm] at h₂
  rw [card_inversions_insert f ha]
  omega

/-- **Reordering signs along an edge.** For an injective map `f` and `a ∉ s`, the inversion sign
of `f` on `insert a s`, times the sign recording the position of `a` in `s`, is the inversion sign
of `f` on `s` times the sign recording the position of `f a` in `f(s)`. -/
theorem neg_one_pow_card_inversions_insert {R : Type*} [Monoid R] [HasDistribNeg R]
    {f : α → β} (hf : Injective f) {s : Finset α} {a : α} (ha : a ∉ s) :
    (-1 : R) ^ #((insert a s).inversions f) * (-1) ^ #{b ∈ s | b < a} =
      (-1) ^ #(s.inversions f) * (-1) ^ #{b ∈ s | f b < f a} := by
  rw [← pow_add, ← pow_add, card_inversions_insert_add_card_filter_lt hf ha, pow_add _ _ (2 * _),
    pow_mul, neg_one_sq, one_pow, mul_one]

/-- The parities of the inversion counts of `f` on `s`, of `g` on `f(s)` and of `g ∘ f` on `s` add
up to zero. -/
theorem even_card_inversions_comp {f : α ↪ β} {g : β → γ} (hg : Injective g)
    (s : Finset α) :
    Even (#(s.inversions (g ∘ f)) + #(s.inversions f) + #((s.map f).inversions g)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hfa : f a ∉ s.map f := by simpa using ha
    have h₁ := card_inversions_insert_add_card_filter_lt (hg.comp f.injective) ha
    have h₂ := card_inversions_insert_add_card_filter_lt f.injective ha
    have h₃ := card_inversions_insert_add_card_filter_lt hg hfa
    rw [map_insert]
    rw [filter_map, card_map, filter_map, card_map] at h₃
    simp only [comp_apply] at h₁ h₃ ⊢
    rw [Nat.even_iff] at ih ⊢
    omega

/-- **Inversion signs are multiplicative.** For an embedding `f` and an injective map `g`, the
inversion sign of `g ∘ f` on `s` is the product of the inversion signs of `f` on `s` and of `g` on
`f(s)`. -/
theorem neg_one_pow_card_inversions_comp {R : Type*} [Monoid R] [HasDistribNeg R] (f : α ↪ β)
    {g : β → γ} (hg : Injective g) (s : Finset α) :
    (-1 : R) ^ #(s.inversions (g ∘ f)) =
      (-1) ^ #(s.inversions f) * (-1) ^ #((s.map f).inversions g) := by
  have h := even_card_inversions_comp (f := f) hg s
  rw [add_assoc, Nat.even_add] at h
  rw [← pow_add]
  rcases Nat.even_or_odd #(s.inversions (g ∘ f)) with h' | h'
  · rw [h'.neg_one_pow, (h.1 h').neg_one_pow]
  · have h'' : Odd (#(s.inversions f) + #((s.map f).inversions g)) :=
      Nat.not_even_iff_odd.1 fun h'' ↦ Nat.not_even_iff_odd.2 h' (h.2 h'')
    rw [h'.neg_one_pow, h''.neg_one_pow]

end Finset

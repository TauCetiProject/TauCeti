/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import TauCeti.Order.Hom.Basic

/-!
# Lexicographic order on order embeddings

An order embedding `f : α ↪o β` has the componentwise partial order (`f ≤ g ↔ ∀ i, f i ≤ g i`).
Equipping the type synonym `Lex (α ↪o β)` with the lexicographic order of underlying functions
`Lex (α → β)` gives a partial order whenever `α` is a linear order and `β` is a partial order, and a
linear order when `α` is well-founded and `β` is a linear order. When `α` is well-founded, the
lexicographic order refines the componentwise order (`OrderEmbedding.toLex_monotone`,
`OrderEmbedding.toLex_strictMono`), agrees with it on comparable pairs
(`OrderEmbedding.le_iff_toLex_le_of_le_or_ge`), and equates `¬ f ≤ g` with componentwise
incomparability whenever `toLex f < toLex g`
(`OrderEmbedding.not_le_iff_not_le_or_ge_of_toLex_lt`).
-/

public section

namespace OrderEmbedding

variable {α β : Type*}

section LT

variable [LE α] [LT α] [LE β] [LT β]

/-- The lexicographic strict inequality on `Lex (α ↪o β)`, lifted from `Lex (α → β)`. -/
instance instLTLex : LT (Lex (α ↪o β)) :=
  ⟨fun f g ↦ toLex ⇑(ofLex f) < toLex ⇑(ofLex g)⟩

@[simp]
theorem toLex_lt_toLex_iff {f g : α ↪o β} : toLex f < toLex g ↔ toLex ⇑f < toLex ⇑g :=
  Iff.rfl

/-- An order embedding `f` precedes `g` lexicographically when `f` agrees with `g` below some
index `i` and `f i < g i`. -/
theorem toLex_lt_iff {f g : α ↪o β} :
    toLex f < toLex g ↔ ∃ i, (∀ j < i, f j = g j) ∧ f i < g i :=
  Iff.rfl

end LT

section PartialOrder

variable [LinearOrder α] [PartialOrder β]

/-- The lexicographic partial order on `Lex (α ↪o β)`, lifted from `Lex (α → β)`. -/
instance instPartialOrderLex : PartialOrder (Lex (α ↪o β)) :=
  PartialOrder.lift (fun f ↦ toLex ⇑(ofLex f)) fun _ _ h ↦
    ofLex.injective (DFunLike.coe_injective (ofLex.injective h))

@[simp]
theorem toLex_le_toLex_iff {f g : α ↪o β} : toLex f ≤ toLex g ↔ toLex ⇑f ≤ toLex ⇑g :=
  Iff.rfl

variable [WellFoundedLT α]

/-- Componentwise order on `α ↪o β` refines to the lexicographic order on `Lex (α ↪o β)`. -/
theorem toLex_monotone : Monotone (toLex : (α ↪o β) → Lex (α ↪o β)) :=
  fun _ _ h ↦ Pi.toLex_monotone h

/-- Strict componentwise inequality implies strict lexicographic inequality. -/
theorem toLex_strictMono : StrictMono (toLex : (α ↪o β) → Lex (α ↪o β)) :=
  fun _ _ h ↦ Pi.toLex_strictMono (coe_lt_coe.2 h)

/-- For two comparable order embeddings, the componentwise order agrees with the lexicographic
order. -/
theorem le_iff_toLex_le_of_le_or_ge {f g : α ↪o β} (h : f ≤ g ∨ g ≤ f) :
    f ≤ g ↔ toLex f ≤ toLex g := by
  refine ⟨fun hfg ↦ toLex_monotone hfg, fun hlex ↦ ?_⟩
  rcases h with hfg | hgf
  · exact hfg
  · exact le_of_eq (toLex.injective (le_antisymm hlex (toLex_monotone hgf)))

/-- When `toLex f < toLex g`, `¬ f ≤ g` is equivalent to componentwise incomparability
`¬ (f ≤ g ∨ g ≤ f)`, because `g ≤ f` would contradict `toLex f < toLex g`. -/
theorem not_le_iff_not_le_or_ge_of_toLex_lt {f g : α ↪o β} (hlt : toLex f < toLex g) :
    ¬ f ≤ g ↔ ¬ (f ≤ g ∨ g ≤ f) :=
  ⟨fun hfg h ↦ h.elim hfg fun hgf ↦ hlt.not_ge (toLex_monotone hgf),
    fun h hfg ↦ h (Or.inl hfg)⟩

/-- If `J` and `J'` are order embeddings of a well-founded linear order `α` into a partial order
`β` such that every `J c` with `c < k` lies in the range of `J'` while `J' k < J k`, then `J'`
precedes `J` lexicographically. -/
theorem toLex_lt_of_forall_lt_mem_range {J J' : α ↪o β} {k : α}
    (hmem : ∀ c < k, J c ∈ Set.range J') (hlt : J' k < J k) :
    toLex J' < toLex J := by
  let s : Set α := {c | J' c ≠ J c}
  have hs : s.Nonempty := ⟨k, hlt.ne⟩
  let c₀ : α := WellFounded.min wellFounded_lt s hs
  have hc₀_mem : J' c₀ ≠ J c₀ := WellFounded.min_mem wellFounded_lt s hs
  have hc₀_min (j : α) (hj : j < c₀) : J' j = J j :=
    not_not.1 fun h ↦ WellFounded.not_lt_min wellFounded_lt s h hj
  rw [toLex_lt_iff]
  refine ⟨c₀, hc₀_min, ?_⟩
  rcases lt_trichotomy c₀ k with hc₀k | rfl | hkc₀
  · obtain ⟨b, hb⟩ := hmem c₀ hc₀k
    have hlt_b : c₀ < b := by
      rcases lt_trichotomy b c₀ with hbc₀ | rfl | hc₀b
      · exact absurd (J.injective ((hc₀_min b hbc₀).symm.trans hb)) hbc₀.ne
      · exact absurd hb hc₀_mem
      · exact hc₀b
    exact hb ▸ J'.strictMono hlt_b
  · exact hlt
  · exact absurd (hc₀_min k hkc₀) hlt.ne

end PartialOrder

section LinearOrder

variable [LinearOrder α] [WellFoundedLT α] [LinearOrder β]

/-- The lexicographic linear order on `Lex (α ↪o β)`, lifted from `Lex (α → β)`. -/
noncomputable instance instLinearOrderLex : LinearOrder (Lex (α ↪o β)) :=
  LinearOrder.lift' (fun f ↦ toLex ⇑(ofLex f)) fun _ _ h ↦
    ofLex.injective (DFunLike.coe_injective (ofLex.injective h))

end LinearOrder

end OrderEmbedding

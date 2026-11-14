/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.PiLex
public import TauCeti.Order.Hom.Basic

/-!
# Lexicographic order on order embeddings

An order embedding `f : α ↪o β` has the componentwise partial order (`f ≤ g ↔ ∀ i, f i ≤ g i`).
When `α` is a well-founded linear order and `β` is a linear order, equipping the type synonym
`Lex (α ↪o β)` with the lexicographic order of underlying functions `Lex (α → β)` refines this
componentwise order to a linear order (`OrderEmbedding.toLex_monotone`,
`OrderEmbedding.toLex_strictMono`). On any comparable pair, the componentwise and lexicographic
orders coincide (`OrderEmbedding.le_iff_toLex_le_of_le_or_ge`).
-/

public section

namespace OrderEmbedding

variable {α β : Type*}

section LinearOrder

variable [LinearOrder α] [WellFoundedLT α] [LinearOrder β]

/-- The lexicographic linear order on `Lex (α ↪o β)`, lifted from `Lex (α → β)`. -/
noncomputable instance instLinearOrderLex : LinearOrder (Lex (α ↪o β)) :=
  LinearOrder.lift' (fun f ↦ toLex ⇑(ofLex f)) fun _ _ h ↦
    ofLex.injective (DFunLike.coe_injective (ofLex.injective h))

@[simp]
theorem toLex_lt_toLex_iff {f g : α ↪o β} : toLex f < toLex g ↔ toLex ⇑f < toLex ⇑g :=
  Iff.rfl

@[simp]
theorem toLex_le_toLex_iff {f g : α ↪o β} : toLex f ≤ toLex g ↔ toLex ⇑f ≤ toLex ⇑g :=
  Iff.rfl

/-- An order embedding `f` precedes `g` lexicographically when `f` agrees with `g` below some
index `i` and `f i < g i`. -/
theorem toLex_lt_iff {f g : α ↪o β} :
    toLex f < toLex g ↔ ∃ i, (∀ j < i, f j = g j) ∧ f i < g i :=
  Iff.rfl

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

end LinearOrder

/-- If `J` and `J'` are order embeddings of `Fin d` into a linear order `β` such that every
`J c` with `c < k` lies in the range of `J'` while `J' k < J k`, then `J'` precedes `J`
lexicographically. -/
theorem toLex_lt_of_forall_lt_mem_range {d : ℕ} [LinearOrder β] {J J' : Fin d ↪o β} {k : Fin d}
    (hmem : ∀ c < k, J c ∈ Set.range J') (hlt : J' k < J k) :
    toLex J' < toLex J := by
  by_contra! hle
  rcases hle.eq_or_lt with heq | hlt'
  · exact hlt.ne (congrFun (congrArg DFunLike.coe (toLex.injective heq)) k).symm
  · obtain ⟨c, hc, hJJ'⟩ := toLex_lt_iff.1 hlt'
    rcases lt_trichotomy c k with hck | rfl | hkc
    · obtain ⟨b, hb⟩ := hmem c hck
      have hbc : b < c := J'.lt_iff_lt.1 (hb.symm ▸ hJJ')
      exact hbc.ne (J.injective ((hc b hbc).trans hb))
    · exact hlt.not_gt hJJ'
    · exact hlt.ne (hc k hkc).symm

end OrderEmbedding

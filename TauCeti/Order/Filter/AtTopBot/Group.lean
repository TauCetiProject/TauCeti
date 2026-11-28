/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Negation and the ends of a subset of an ordered group

For a subset `s` of a linearly ordered additive group, the filter `map (↑) atBot` of `atBot` on
the subtype `s` describes the approach to the left end of `s` within `s`; for `s = (a, b)` in `ℝ`
it is `x → a+`. Negation reverses the order, so it maps this filter to the approach
`map (↑) atTop` to the right end of `-s` within `-s` (`TauCeti.map_neg_map_val_atBot`); for
`s = (a, b)` this is `t → (-a)-`. In particular negation tends from each of these filters to the
other (`TauCeti.tendsto_neg_map_val_atBot` and `TauCeti.tendsto_neg_map_val_atTop`). This reduces
statements at the left end of an interval to statements at its right end.
-/

public section

open Set Filter

namespace TauCeti

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- Negation maps the image of `atBot` on the subtype `s` (the approach to the left end of `s`
within `s`) to the image of `atTop` on the subtype `-s` (the approach to the right end of `-s`
within `-s`). -/
theorem map_neg_map_val_atBot (s : Set α) :
    map Neg.neg (map ((↑) : s → α) atBot) = map ((↑) : (Neg.neg ⁻¹' s : Set α) → α) atTop := by
  rcases isEmpty_or_nonempty s with hs0 | hne
  · have : IsEmpty (Neg.neg ⁻¹' s : Set α) := ⟨fun t ↦ hs0.false ⟨-t, t.property⟩⟩
    rw [filter_eq_bot_of_isEmpty (atBot : Filter s),
      filter_eq_bot_of_isEmpty (atTop : Filter (Neg.neg ⁻¹' s : Set α)), map_bot, map_bot,
      map_bot]
  obtain ⟨x₀⟩ := hne
  have : Nonempty s := ⟨x₀⟩
  have : Nonempty (Neg.neg ⁻¹' s : Set α) := ⟨⟨-x₀, by simp⟩⟩
  ext u
  simp only [mem_map, mem_atBot_sets, mem_atTop_sets, mem_preimage]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨⟨-a, by simp⟩, fun b hb ↦ ?_⟩
    simpa using ha ⟨-b, b.property⟩ (Subtype.coe_le_coe.1 (neg_le.1 (Subtype.coe_le_coe.2 hb)))
  · rintro ⟨a, ha⟩
    refine ⟨⟨-a, a.property⟩, fun b hb ↦ ?_⟩
    simpa using ha ⟨-b, by simp⟩ (Subtype.coe_le_coe.1 (le_neg.2 (Subtype.coe_le_coe.2 hb)))

/-- Negation tends from the image of `atBot` on the subtype `s` to the image of `atTop` on the
subtype `-s`. -/
theorem tendsto_neg_map_val_atBot (s : Set α) :
    Tendsto Neg.neg (map ((↑) : s → α) atBot) (map ((↑) : (Neg.neg ⁻¹' s : Set α) → α) atTop) :=
  (map_neg_map_val_atBot s).le

/-- Negation tends from the image of `atTop` on the subtype `-s` back to the image of `atBot` on
the subtype `s`. -/
theorem tendsto_neg_map_val_atTop (s : Set α) :
    Tendsto Neg.neg (map ((↑) : (Neg.neg ⁻¹' s : Set α) → α) atTop) (map ((↑) : s → α) atBot) := by
  rw [Tendsto, ← map_neg_map_val_atBot, map_map, neg_involutive.comp_self, map_id]

end TauCeti

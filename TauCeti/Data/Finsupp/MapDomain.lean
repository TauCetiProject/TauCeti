/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Lex

/-!
# Injective relabeling as extension by zero

For an injective index map, pushing forward a finitely supported function is ordinary
function extension by zero, over any additive commutative monoid.

Pushing forward along a strictly monotone map of linearly ordered indices preserves and reflects
the lexicographic order, since the relabeled functions vanish off the image and the order
relabels the positions where they first differ.
-/

public section

namespace Finsupp

/-- Pushing a finitely supported function along an injection extends its values by zero
outside the image. -/
theorem coe_mapDomain_eq_extend {α β M : Type*} [AddCommMonoid M]
    {e : α → β} (he : Function.Injective e) (x : α →₀ M) :
    (mapDomain e x : β → M) = Function.extend e x 0 := by
  classical
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simp [he]
  · simp [mapDomain_of_notMem_range _ _ hj, Function.extend_apply' _ _ _ hj]

/-- Pushing forward along a strictly monotone map of indices preserves and reflects the strict
lexicographic order: the first position at which two relabeled functions differ is the image of
the first position at which the original functions differ. -/
theorem toLex_mapDomain_lt_toLex_mapDomain_iff {α β M : Type*} [LinearOrder α] [Preorder β]
    [AddCommMonoid M] [Preorder M] {f : α → β} (hf : StrictMono f) {x y : α →₀ M} :
    toLex (mapDomain f x) < toLex (mapDomain f y) ↔ toLex x < toLex y := by
  simp only [Lex.lt_iff, ofLex_toLex]
  constructor
  · rintro ⟨k, hk, hlt⟩
    -- Off the image of `f` both relabeled functions vanish, so `k` is a value of `f`.
    obtain ⟨i, rfl⟩ : k ∈ Set.range f := by
      by_contra h
      simp [mapDomain_of_notMem_range _ _ h] at hlt
    refine ⟨i, fun j hj ↦ ?_, by simpa [hf.injective] using hlt⟩
    simpa [hf.injective] using hk (f j) (hf hj)
  · rintro ⟨i, hi, hlt⟩
    refine ⟨f i, fun l hl ↦ ?_, by simpa [hf.injective] using hlt⟩
    by_cases h : l ∈ Set.range f
    · obtain ⟨j, rfl⟩ := h
      simpa [hf.injective] using hi j (hf.lt_iff_lt.1 hl)
    · simp [mapDomain_of_notMem_range _ _ h]

end Finsupp

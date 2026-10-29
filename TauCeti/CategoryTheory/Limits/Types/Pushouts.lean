/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# The complement of the range in a pushout of types

Consider a pushout square of types
```
     g
  A ───> B
f │      │ f'
  v      v
  A' ──> B'
     g'
```
The map `g'` is injective off the range of `f` (`TauCeti.Types.injOn_compl_range_of_isPushout`),
and it carries the complement of the range of `f` exactly onto the complement of the range of
`f'` (`TauCeti.Types.image_compl_range_of_isPushout`). No injectivity of `f` is needed: the points
of `A'` outside the range of `f` are not identified with anything in the pushout.

When `f` attaches cells along their boundaries, the complement of the range of `f` is the union of
the interiors of the cells, so these statements say that the open cells of the pushout are copies
of the open cells of `A'`, disjoint from `B`.
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.Types

variable {A A' B B' : Type u} {g : A ⟶ B} {f : A ⟶ A'} {f' : B ⟶ B'} {g' : A' ⟶ B'}

/-- The map from a pushout to `Option A'` that remembers the points of `A'` outside the range of
`f` and forgets everything else. -/
private noncomputable def complRangeIndicator (sq : IsPushout g f f' g') : B' ⟶ Option A' := by
  classical
  exact sq.desc (TypeCat.ofHom fun _ ↦ none)
    (TypeCat.ofHom fun a' ↦ if a' ∈ Set.range f then none else some a') (by
      ext a
      simp)

private lemma complRangeIndicator_inl (sq : IsPushout g f f' g') (b : B) :
    complRangeIndicator sq (f' b) = none := by
  simp [complRangeIndicator, ← types_comp_apply f' (sq.desc _ _ _)]

private lemma complRangeIndicator_inr (sq : IsPushout g f f' g') {a' : A'}
    (ha' : a' ∉ Set.range f) : complRangeIndicator sq (g' a') = some a' := by
  simp [complRangeIndicator, ← types_comp_apply g' (sq.desc _ _ _), ha']

/-- In a pushout square of types, the map opposite to `f'` is injective on the complement of the
range of `f`. -/
theorem injOn_compl_range_of_isPushout (sq : IsPushout g f f' g') :
    Set.InjOn g' (Set.range f)ᶜ := fun a₁ h₁ a₂ h₂ h ↦ by
  simpa [complRangeIndicator_inr sq h₁, complRangeIndicator_inr sq h₂] using
    congr(complRangeIndicator sq $h)

/-- In a pushout square of types, the map opposite to `f'` carries the complement of the range of
`f` onto the complement of the range of `f'`. -/
theorem image_compl_range_of_isPushout (sq : IsPushout g f f' g') :
    g' '' (Set.range f)ᶜ = (Set.range f')ᶜ := by
  refine subset_antisymm ?_ fun b' hb' ↦ ?_
  · rintro _ ⟨a', ha', rfl⟩ ⟨b, hb⟩
    simpa [complRangeIndicator_inl sq, complRangeIndicator_inr sq ha'] using
      congr(complRangeIndicator sq $hb)
  · obtain ⟨b, rfl⟩ | ⟨a', rfl, ha'⟩ := Types.eq_or_eq_of_isPushout' sq b'
    · exact (hb' ⟨b, rfl⟩).elim
    · exact ⟨a', ha', rfl⟩

end TauCeti.Types

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sum

/-!
# Images and erasures of finite sets on sum types

These identities compute the image of a disjoint sum, the two projections of an image under
`Sum.map`, and the projections after erasing an element of the left summand. They are used to
calculate joins of simplicial complexes factor by factor.

## Main results

* `Finset.image_sumMap_disjSum`: mapping the summands commutes with disjoint union.
* `Finset.toLeft_image_sumMap` and `Finset.toRight_image_sumMap`: projections of an image
  under `Sum.map`.
* `Finset.toLeft_erase_inl` and `Finset.toRight_erase_inl`: projections after erasing a
  left-tagged element.
* `Finset.disjoint_disjSum_iff`: disjointness from a disjoint sum is characterized by disjointness
  from its two projections.
-/

public section

namespace Finset

variable {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
  [DecidableEq γ] [DecidableEq δ]

omit [DecidableEq α] [DecidableEq β] in
/-- Mapping the two summands commutes with disjoint union. -/
@[simp] theorem image_sumMap_disjSum (s : Finset α) (t : Finset β)
    (f : α → γ) (g : β → δ) :
    (s.disjSum t).image (Sum.map f g) = (s.image f).disjSum (t.image g) := by
  ext (x | x) <;> simp [mem_image, mem_disjSum, Sum.exists]

omit [DecidableEq α] [DecidableEq β] in
/-- The left projection of the image under a map of summands. -/
@[simp] theorem toLeft_image_sumMap (s : Finset (α ⊕ β)) (f : α → γ) (g : β → δ) :
    (s.image (Sum.map f g)).toLeft = s.toLeft.image f := by
  conv_lhs => rw [← toLeft_disjSum_toRight (u := s), image_sumMap_disjSum]
  simp

omit [DecidableEq α] [DecidableEq β] in
/-- The right projection of the image under a map of summands. -/
@[simp] theorem toRight_image_sumMap (s : Finset (α ⊕ β)) (f : α → γ) (g : β → δ) :
    (s.image (Sum.map f g)).toRight = s.toRight.image g := by
  conv_lhs => rw [← toLeft_disjSum_toRight (u := s), image_sumMap_disjSum]
  simp

/-- Erasing a left-tagged element erases it from the left projection. -/
@[simp] theorem toLeft_erase_inl (s : Finset (α ⊕ β)) (a : α) :
    (s.erase (Sum.inl a)).toLeft = s.toLeft.erase a := by
  ext x
  simp

/-- Erasing a left-tagged element leaves the right projection unchanged. -/
@[simp] theorem toRight_erase_inl (s : Finset (α ⊕ β)) (a : α) :
    (s.erase (Sum.inl a)).toRight = s.toRight := by
  ext x
  simp

omit [DecidableEq α] [DecidableEq β] in
/-- Disjointness from a disjoint sum is equivalent to disjointness from its two projections. -/
@[simp]
theorem disjoint_disjSum_iff {ρ : Finset (α ⊕ β)} {s : Finset α} {t : Finset β} :
    Disjoint ρ (s.disjSum t) ↔ Disjoint ρ.toLeft s ∧ Disjoint ρ.toRight t := by
  classical
  constructor
  · intro h
    constructor
    · refine Finset.disjoint_left.mpr ?_
      intro a haρ has
      exact (Finset.disjoint_left.mp h (Finset.mem_toLeft.mp haρ))
        (Finset.mem_disjSum.mpr (Or.inl ⟨a, has, rfl⟩))
    · refine Finset.disjoint_left.mpr ?_
      intro b hbρ hbt
      exact (Finset.disjoint_left.mp h (Finset.mem_toRight.mp hbρ))
        (Finset.mem_disjSum.mpr (Or.inr ⟨b, hbt, rfl⟩))
  · rintro ⟨hleft, hright⟩
    refine Finset.disjoint_left.mpr ?_
    intro x hxρ hxst
    rcases x with a | b
    · rcases Finset.mem_disjSum.mp hxst with ⟨a', ha', haa'⟩ | h
      · have : a' = a := Sum.inl.inj haa'
        subst a'
        exact (Finset.disjoint_left.mp hleft (Finset.mem_toLeft.mpr hxρ)) ha'
      · rcases h with ⟨b', hb', hab'⟩
        cases hab'
    · rcases Finset.mem_disjSum.mp hxst with h | ⟨b', hb', hbb'⟩
      · rcases h with ⟨a', ha', hab'⟩
        cases hab'
      · have : b' = b := Sum.inr.inj hbb'
        subst b'
        exact (Finset.disjoint_left.mp hright (Finset.mem_toRight.mpr hxρ)) hb'

end Finset

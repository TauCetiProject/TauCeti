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

variable {α β γ δ : Type*}

section

variable [DecidableEq γ] [DecidableEq δ]

/-- Mapping the two summands commutes with disjoint union. -/
@[simp] theorem image_sumMap_disjSum (s : Finset α) (t : Finset β)
    (f : α → γ) (g : β → δ) :
    (s.disjSum t).image (Sum.map f g) = (s.image f).disjSum (t.image g) := by
  ext (x | x) <;> simp [mem_image, mem_disjSum, Sum.exists]

/-- The left projection of the image under a map of summands. -/
@[simp] theorem toLeft_image_sumMap (s : Finset (α ⊕ β)) (f : α → γ) (g : β → δ) :
    (s.image (Sum.map f g)).toLeft = s.toLeft.image f := by
  conv_lhs => rw [← toLeft_disjSum_toRight (u := s), image_sumMap_disjSum]
  simp

/-- The right projection of the image under a map of summands. -/
@[simp] theorem toRight_image_sumMap (s : Finset (α ⊕ β)) (f : α → γ) (g : β → δ) :
    (s.image (Sum.map f g)).toRight = s.toRight.image g := by
  conv_lhs => rw [← toLeft_disjSum_toRight (u := s), image_sumMap_disjSum]
  simp

end

section

variable [DecidableEq α] [DecidableEq β]

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

end

/-- Disjointness from a disjoint sum is equivalent to disjointness from its two projections. -/
@[simp]
theorem disjoint_disjSum_iff {ρ : Finset (α ⊕ β)} {s : Finset α} {t : Finset β} :
    Disjoint ρ (s.disjSum t) ↔ Disjoint ρ.toLeft s ∧ Disjoint ρ.toRight t := by
  simp [disjoint_left, Sum.forall]

end Finset

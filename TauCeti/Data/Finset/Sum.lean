/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Finset.Sum

/-!
# Images and erasures of finite sets on sum types, and families indexed by them

These identities compute the image of a disjoint sum, the two projections of an image under
`Sum.map`, of a filtered set, and after erasing an element of either summand. They are used to
calculate joins of simplicial complexes factor by factor.

A family indexed by a finite set `s` of `α ⊕ β` is the pair of its restrictions to the left part
`s.toLeft` and the right part `s.toRight` (`Equiv.piFinsetSum`), the finite-set analogue of
`Equiv.sumPiEquivProdPi`; this splitting commutes with restriction to a smaller finite set.

## Main definitions

* `Equiv.piFinsetSum`: a family on a finite `s ⊆ α ⊕ β` is a pair of families on `s.toLeft` and
  `s.toRight`.

## Main results

* `Finset.image_sumMap_disjSum`: mapping the summands commutes with disjoint union.
* `Finset.toLeft_image_sumMap` and `Finset.toRight_image_sumMap`: projections of an image
  under `Sum.map`.
* `Finset.toLeft_erase_inl`, `Finset.toRight_erase_inl`, `Finset.toLeft_erase_inr` and
  `Finset.toRight_erase_inr`: projections after erasing an element of either summand.
* `Finset.toLeft_filter` and `Finset.toRight_filter`: projections of a filtered set.
* `Finset.disjoint_disjSum_iff`: disjointness from a disjoint sum is characterized by disjointness
  from its two projections.
* `Equiv.piFinsetSum_restrict₂`: splitting a family commutes with restriction.
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

/-- Erasing a right-tagged element leaves the left projection unchanged. -/
@[simp]
theorem toLeft_erase_inr [DecidableEq α] [DecidableEq β] (s : Finset (α ⊕ β)) (b : β) :
    (s.erase (Sum.inr b)).toLeft = s.toLeft := by
  ext a
  simp

/-- Erasing a right-tagged element erases that element from the right projection. -/
@[simp]
theorem toRight_erase_inr [DecidableEq α] [DecidableEq β] (s : Finset (α ⊕ β)) (b : β) :
    (s.erase (Sum.inr b)).toRight = s.toRight.erase b := by
  ext a
  simp

/-- The left projection of a filtered set is the filtered left projection. -/
@[simp]
theorem toLeft_filter (s : Finset (α ⊕ β)) (p : α ⊕ β → Prop) [DecidablePred p] :
    {x ∈ s | p x}.toLeft = {a ∈ s.toLeft | p (Sum.inl a)} := by
  ext
  simp

/-- The right projection of a filtered set is the filtered right projection. -/
@[simp]
theorem toRight_filter (s : Finset (α ⊕ β)) (p : α ⊕ β → Prop) [DecidablePred p] :
    {x ∈ s | p x}.toRight = {b ∈ s.toRight | p (Sum.inr b)} := by
  ext
  simp

/-- Disjointness from a disjoint sum is equivalent to disjointness from its two projections. -/
@[simp]
theorem disjoint_disjSum_iff {ρ : Finset (α ⊕ β)} {s : Finset α} {t : Finset β} :
    Disjoint ρ (s.disjSum t) ↔ Disjoint ρ.toLeft s ∧ Disjoint ρ.toRight t := by
  simp [disjoint_left, Sum.forall]

end Finset

open Finset

namespace Equiv

variable {α β : Type*} (π : α ⊕ β → Type*)

/-- A family on a finite set `s` of `α ⊕ β` is the pair of its restrictions to the left part
`s.toLeft` and the right part `s.toRight`. This is the finite-set analogue of
`Equiv.sumPiEquivProdPi`. -/
@[expose] def piFinsetSum (s : Finset (α ⊕ β)) :
    ((i : s) → π i) ≃ ((a : s.toLeft) → π (.inl a)) × ((b : s.toRight) → π (.inr b)) where
  toFun f := (fun a ↦ f ⟨.inl a, mem_toLeft.1 a.property⟩,
    fun b ↦ f ⟨.inr b, mem_toRight.1 b.property⟩)
  invFun p := fun
    | ⟨.inl a, h⟩ => p.1 ⟨a, mem_toLeft.2 h⟩
    | ⟨.inr b, h⟩ => p.2 ⟨b, mem_toRight.2 h⟩
  left_inv f := funext fun ⟨i, _⟩ ↦ by cases i <;> rfl
  right_inv _ := rfl

variable {π}

/-- The left part of a split family is its restriction to `s.toLeft`. -/
@[simp]
theorem piFinsetSum_apply_fst (s : Finset (α ⊕ β)) (f : (i : s) → π i) (a : s.toLeft) :
    (piFinsetSum π s f).1 a = f ⟨.inl a, mem_toLeft.1 a.property⟩ :=
  (rfl)

/-- The right part of a split family is its restriction to `s.toRight`. -/
@[simp]
theorem piFinsetSum_apply_snd (s : Finset (α ⊕ β)) (f : (i : s) → π i) (b : s.toRight) :
    (piFinsetSum π s f).2 b = f ⟨.inr b, mem_toRight.1 b.property⟩ :=
  (rfl)

/-- Gluing a pair of families reads the left family at a left-tagged index. -/
@[simp]
theorem piFinsetSum_symm_apply_inl (s : Finset (α ⊕ β))
    (p : ((a : s.toLeft) → π (.inl a)) × ((b : s.toRight) → π (.inr b))) (a : α)
    (h : .inl a ∈ s) : (piFinsetSum π s).symm p ⟨.inl a, h⟩ = p.1 ⟨a, mem_toLeft.2 h⟩ :=
  (rfl)

/-- Gluing a pair of families reads the right family at a right-tagged index. -/
@[simp]
theorem piFinsetSum_symm_apply_inr (s : Finset (α ⊕ β))
    (p : ((a : s.toLeft) → π (.inl a)) × ((b : s.toRight) → π (.inr b))) (b : β)
    (h : .inr b ∈ s) : (piFinsetSum π s).symm p ⟨.inr b, h⟩ = p.2 ⟨b, mem_toRight.2 h⟩ :=
  (rfl)

/-- Splitting a family on `t ⊆ α ⊕ β` commutes with restriction to `s ⊆ t`. -/
theorem piFinsetSum_restrict₂ {s t : Finset (α ⊕ β)} (h : s ⊆ t) (f : (i : t) → π i) :
    piFinsetSum π s (restrict₂ h f) =
      (restrict₂ (π := fun a ↦ π (.inl a)) (toLeft_subset_toLeft h) (piFinsetSum π t f).1,
        restrict₂ (π := fun b ↦ π (.inr b)) (toRight_subset_toRight h) (piFinsetSum π t f).2) :=
  (rfl)

end Equiv

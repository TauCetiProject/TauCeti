/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Subquiver
public import Mathlib.Combinatorics.Quiver.ConnectedComponent

/-!
# Edge maps for wide subquivers

This file relates the total-arrow type of a wide subquiver to its image as a set of ambient
arrows and forgets orientation tags in symmetrified wide subquivers.

## Main results

* `totalEquivSet`: identifies total arrows with their ambient image.
* `totalWideSubquiverSymmetrify`: forgets the orientation tag on a symmetrified edge.
* `totalWideSubquiverSymmetrify_apply_inl` and
  `totalWideSubquiverSymmetrify_apply_inr`: its orientation cases.
* `mem_wideSubquiverSymmetrify_iff`: membership in the symmetrification by either orientation.
-/

open Set Function Quiver

attribute [local implicit_reducible]
  _root_.WideSubquiver _root_.WideSubquiver.toType _root_.WideSubquiver.quiver

public section

universe u v

namespace TauCeti.WideSubquiver

variable {V : Type u} [Quiver.{v, u} V]

/-- Total arrows of a wide subquiver are equivalent to its set of ambient total arrows. -/
def totalEquivSet (H : _root_.WideSubquiver V) :
    Quiver.Total H ≃ {e : Quiver.Total V // e ∈ wideSubquiverEquivSetTotal H} where
  toFun e := ⟨⟨e.left, e.right, e.hom.val⟩, e.hom.property⟩
  invFun e := ⟨e.1.left, e.1.right, ⟨e.1.hom, e.2⟩⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

/-- The forward map of `totalEquivSet` sends an arrow to its ambient arrow. -/
@[simp] theorem totalEquivSet_apply (H : _root_.WideSubquiver V) (e : Quiver.Total H) :
    totalEquivSet H e = ⟨⟨e.left, e.right, e.hom.val⟩, e.hom.property⟩ := by
  simp only [totalEquivSet, Equiv.coe_fn_mk]

/-- The inverse map of `totalEquivSet` recovers the arrow in the wide subquiver. -/
@[simp] theorem totalEquivSet_symm_apply (H : _root_.WideSubquiver V)
    (e : {e : Quiver.Total V // e ∈ wideSubquiverEquivSetTotal H}) :
    (totalEquivSet H).symm e = ⟨e.1.left, e.1.right, ⟨e.1.hom, e.2⟩⟩ := by
  simp only [totalEquivSet, Equiv.coe_fn_symm_mk]

/-- Forget the orientation tag of an edge in a symmetrified wide subquiver. -/
def totalWideSubquiverSymmetrify (T : _root_.WideSubquiver (Quiver.Symmetrify V))
    (e : Quiver.Total T) : Quiver.Total (Quiver.wideSubquiverSymmetrify T) := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  cases f using Sum.casesOn with
  | inl f => exact ⟨a, b, ⟨f, Or.inl hf⟩⟩
  | inr f => exact ⟨b, a, ⟨f, Or.inr hf⟩⟩

/-- An arrow belongs to the symmetrification exactly when either orientation belongs to `T`. -/
@[simp] theorem mem_wideSubquiverSymmetrify_iff (T : _root_.WideSubquiver (Quiver.Symmetrify V))
    {a b : V} (e : @Quiver.Hom V _ a b) :
    e ∈ Quiver.wideSubquiverSymmetrify T a b ↔
      Sum.inl e ∈ T a b ∨ Sum.inr e ∈ T b a := Iff.rfl

/-- The forward map sends a forward-oriented edge to the same ambient edge. -/
@[simp] theorem totalWideSubquiverSymmetrify_apply_inl
    (T : _root_.WideSubquiver (Quiver.Symmetrify V))
    {a b : V} (e : @Quiver.Hom V _ a b) (he : Sum.inl e ∈ T a b) :
    totalWideSubquiverSymmetrify T ⟨a, b, ⟨Sum.inl e, he⟩⟩ = ⟨a, b, ⟨e, Or.inl he⟩⟩ := by
  simp [totalWideSubquiverSymmetrify]

/-- The forward map reverses an edge tagged with the reverse orientation. -/
@[simp] theorem totalWideSubquiverSymmetrify_apply_inr
    (T : _root_.WideSubquiver (Quiver.Symmetrify V))
    {a b : V} (e : @Quiver.Hom V _ b a) (he : Sum.inr e ∈ T a b) :
    totalWideSubquiverSymmetrify T ⟨a, b, ⟨Sum.inr e, he⟩⟩ = ⟨b, a, ⟨e, Or.inr he⟩⟩ := by
  simp [totalWideSubquiverSymmetrify]

end TauCeti.WideSubquiver

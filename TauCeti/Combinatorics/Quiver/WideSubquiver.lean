/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Subquiver

/-!
# Total arrows of a wide subquiver

This file relates the total-arrow type of a wide subquiver to its image as a set of ambient
arrows.
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

end TauCeti.WideSubquiver

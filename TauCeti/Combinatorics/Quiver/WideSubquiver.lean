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

universe u

namespace TauCeti.WideSubquiver

variable {V : Type u} [Quiver.{u} V]

/-- Total arrows of a wide subquiver are equivalent to its set of ambient total arrows. -/
def totalEquivSet (H : _root_.WideSubquiver V) :
    Quiver.Total H ≃ {e : Quiver.Total V // e ∈ wideSubquiverEquivSetTotal H} where
  toFun e := ⟨⟨e.left, e.right, e.hom.val⟩, e.hom.property⟩
  invFun e := ⟨e.1.left, e.1.right, ⟨e.1.hom, e.2⟩⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

end TauCeti.WideSubquiver

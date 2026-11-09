/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import TauCeti.GroupTheory.FreeGroup.Basic

/-!
# Words and changes of relators in presented groups

A signed word is a list of pairs `(x, b)`, with `true` denoting a generator and `false` its
inverse. This file gives the product formula for the image of such a word under the quotient map
to a presented group. The corresponding formulas for free groups are in
`TauCeti.GroupTheory.FreeGroup.Basic`.

Equality of the normal closures of two relator sets gives a canonical isomorphism of the
presented groups, preserving the image of every word.

## Main results

* `PresentedGroup.mk_mk`: the class of a word is the product of its signed generators.
-/

public section

namespace PresentedGroup

/-- Relator sets with the same normal closure present canonically isomorphic groups. -/
def equivOfNormalClosureEq {α : Type*} {S T : Set (FreeGroup α)}
    (h : Subgroup.normalClosure S = Subgroup.normalClosure T) :
    PresentedGroup S ≃* PresentedGroup T where
  toFun := QuotientGroup.quotientMulEquivOfEq h
  invFun := (QuotientGroup.quotientMulEquivOfEq h).symm
  left_inv := (QuotientGroup.quotientMulEquivOfEq h).left_inv
  right_inv := (QuotientGroup.quotientMulEquivOfEq h).right_inv
  map_mul' := (QuotientGroup.quotientMulEquivOfEq h).map_mul

/-- The canonical change of relators preserves every word. -/
@[simp]
theorem equivOfNormalClosureEq_mk {α : Type*} {S T : Set (FreeGroup α)}
    (h : Subgroup.normalClosure S = Subgroup.normalClosure T) (w : FreeGroup α) :
    equivOfNormalClosureEq h (mk S w) = mk T w :=
  QuotientGroup.quotientMulEquivOfEq_mk h w

/-- The inverse change of relators also preserves every word. -/
@[simp]
theorem equivOfNormalClosureEq_symm_mk {α : Type*} {S T : Set (FreeGroup α)}
    (h : Subgroup.normalClosure S = Subgroup.normalClosure T) (w : FreeGroup α) :
    (equivOfNormalClosureEq h).symm (mk T w) = mk S w := by
  apply (equivOfNormalClosureEq h).injective
  simp

/-- Relabeling generators relabels every word by the induced free-group isomorphism. -/
@[simp]
theorem equivPresentedGroup_mk {α β : Type*} (S : Set (FreeGroup α)) (e : α ≃ β)
    (w : FreeGroup α) :
    equivPresentedGroup S e (mk S w) = mk _ (FreeGroup.freeGroupCongr e w) :=
  (rfl)

/-- The image of a word in a presented group is the product of the images of its signed
letters. -/
theorem mk_mk {α : Type*} (S : Set (FreeGroup α)) (L : List (α × Bool)) :
    mk S (FreeGroup.mk L) =
      (L.map fun p => cond p.2 (of p.1) (of p.1)⁻¹).prod :=
  (mk S).apply_freeGroup_mk L

end PresentedGroup

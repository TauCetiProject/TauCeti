/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Order.Hom.Monoid

/-!
# The inclusion of a submonoid as an ordered monoid homomorphism

The inclusion `S → M` of a submonoid of a preordered monoid is monotone for the induced order on
`S`, so it is an injective ordered monoid homomorphism. This is the monoid analogue of
`Subring.orderedSubtype`; it is stated for every type of submonoids, so it applies in particular to
subgroups.

## Main definitions

* `SubmonoidClass.orderedSubtype`, `AddSubmonoidClass.orderedSubtype`: the inclusion of a
  submonoid, as an ordered monoid homomorphism.
-/

public section

namespace SubmonoidClass

variable {M A : Type*} [MulOneClass M] [Preorder M] [SetLike A M] [SubmonoidClass A M] (S : A)

/-- The inclusion of a submonoid `S` of a preordered monoid, as an ordered monoid homomorphism. -/
@[to_additive /-- The inclusion of an additive submonoid `S` of a preordered additive monoid, as an
ordered additive monoid homomorphism. -/]
def orderedSubtype : S →*o M where
  __ := SubmonoidClass.subtype S
  monotone' _ _ := id

@[to_additive (attr := simp)]
theorem coe_orderedSubtype : ⇑(orderedSubtype S) = Subtype.val :=
  (rfl)

@[to_additive]
theorem orderedSubtype_injective : Function.Injective (orderedSubtype S) :=
  Subtype.val_injective

end SubmonoidClass

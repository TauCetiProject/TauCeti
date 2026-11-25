/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.Algebra.Group.Subsemigroup.Defs

/-!
# Unique products in subobjects closed under multiplication

Subsemigroups, submonoids and subgroups, and more generally the members of any `MulMemClass`,
inherit unique products and two unique products from the ambient type. The additive instances
allow unique-sum results to apply directly to additive submonoids and additive subgroups.
-/

public section

namespace MulMemClass

variable {M S : Type*} [Mul M] [SetLike S M] [MulMemClass S M]

@[to_additive]
instance instUniqueProds [UniqueProds M] (s : S) : UniqueProds s :=
  UniqueProds.of_injective_mulHom ⟨Subtype.val, fun _ _ => rfl⟩ Subtype.val_injective
    inferInstance

@[to_additive]
instance instTwoUniqueProds [TwoUniqueProds M] (s : S) : TwoUniqueProds s :=
  TwoUniqueProds.of_injective_mulHom ⟨Subtype.val, fun _ _ => rfl⟩ Subtype.val_injective
    inferInstance

end MulMemClass

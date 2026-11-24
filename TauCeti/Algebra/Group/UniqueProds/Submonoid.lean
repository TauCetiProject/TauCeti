/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Unique products in submonoids and subgroups

Submonoids and subgroups inherit unique products and two unique products from the ambient monoid
or group. The additive instances allow unique-sum results to apply directly to additive submonoids
and additive subgroups.
-/

public section

namespace Submonoid

variable {M : Type*} [Monoid M]

@[to_additive]
instance instUniqueProds [UniqueProds M] (S : Submonoid M) : UniqueProds S :=
  UniqueProds.of_injective_mulHom S.subtype.toMulHom Subtype.val_injective inferInstance

@[to_additive]
instance instTwoUniqueProds [TwoUniqueProds M] (S : Submonoid M) : TwoUniqueProds S :=
  TwoUniqueProds.of_injective_mulHom S.subtype.toMulHom Subtype.val_injective inferInstance

end Submonoid

namespace Subgroup

variable {G : Type*} [Group G]

@[to_additive]
instance instUniqueProds [UniqueProds G] (H : Subgroup G) : UniqueProds H :=
  UniqueProds.of_injective_mulHom H.subtype.toMulHom Subtype.val_injective inferInstance

@[to_additive]
instance instTwoUniqueProds [TwoUniqueProds G] (H : Subgroup G) : TwoUniqueProds H :=
  TwoUniqueProds.of_injective_mulHom H.subtype.toMulHom Subtype.val_injective inferInstance

end Subgroup

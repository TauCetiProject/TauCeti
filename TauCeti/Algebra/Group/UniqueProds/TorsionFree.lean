/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Group.UniqueProds.Basic
import Mathlib.Algebra.Group.UniqueProds.VectorSpace
import Mathlib.GroupTheory.DivisibleHull
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Unique products in cancellative torsion-free commutative monoids

Every cancellative torsion-free commutative monoid has `TwoUniqueProds` (and additively
`TwoUniqueSums`): a cancellative commutative monoid embeds into its Grothendieck group, and a
torsion-free abelian group embeds into its divisible hull, which is a `ℚ`-vector space.

This removes the finite-generation hypothesis from `AffineMonoid.to_twoUniqueProds` and
`AffineAddMonoid.to_twoUniqueSums` (`Mathlib.Algebra.AffineMonoid.UniqueSums`). Commutativity and
cancellation are both necessary: non-cancellative monoids fail unique sums directly, and
torsion-free non-abelian groups need not have unique products (Promislow, 1988).
-/

public section

variable {M : Type*}

/-- Every cancellative torsion-free commutative additive monoid has `TwoUniqueSums`, because it
embeds into the divisible hull of its Grothendieck group, which is a `ℚ`-vector space. -/
instance (priority := low) HasUniqueDiv.to_twoUniqueSums [AddCancelCommMonoid M]
    [HasUniqueDiv M] : TwoUniqueSums M :=
  let j : M →+ DivisibleHull (Algebra.GrothendieckAddGroup M) :=
    (DivisibleHull.coeAddMonoidHom _).comp Algebra.GrothendieckAddGroup.of
  .of_injective_addHom j.toAddHom
    (DivisibleHull.coe_injective.comp Algebra.GrothendieckAddGroup.of_injective) inferInstance

/-- Every cancellative torsion-free commutative monoid has `TwoUniqueProds`. -/
@[to_additive existing]
instance (priority := low) HasUniqueRoots.to_twoUniqueProds [CancelCommMonoid M]
    [HasUniqueRoots M] : TwoUniqueProds M :=
  Multiplicative.instTwoUniqueProdsOfTwoUniqueSums (M := Additive M)

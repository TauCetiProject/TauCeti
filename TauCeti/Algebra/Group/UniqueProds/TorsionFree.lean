/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Group.UniqueProds.VectorSpace
import Mathlib.GroupTheory.DivisibleHull
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Torsion-free cancellative commutative monoids have unique products

A torsion-free cancellative commutative monoid has two unique products. Mathlib proves this for
finitely generated monoids, by embedding them into `ℤⁿ` (`AffineMonoid.to_twoUniqueProds`); here no
finiteness is assumed. A torsion-free additive cancellative commutative monoid `M` has unique
division (`IsAddTorsionFree.hasUniqueDiv`), so it embeds into its Grothendieck group, which again
has unique division and therefore embeds into its divisible hull. The divisible hull is a
`ℚ`-vector space, and those have two unique sums.

Through `TauCeti.IsMulTorsionFree.to_twoUniqueProds`,
`TauCeti.Module.IsTorsionFree.to_twoUniqueSums_int`, and Mathlib's instances for monoid algebras,
this makes `R[M]` a domain whenever `R` is one and `M` is a torsion-free cancellative commutative
monoid (`[IsMulTorsionFree M]`) or a torsion-free abelian group (`[Module.IsTorsionFree ℤ M]`,
including free `ℤ`-modules), with no finite generation hypothesis.
-/

public section

namespace TauCeti

variable {M : Type*}

/-- A torsion-free additive cancellative commutative monoid has two unique sums. -/
instance (priority := low) IsAddTorsionFree.to_twoUniqueSums [AddCancelCommMonoid M]
    [IsAddTorsionFree M] : TwoUniqueSums M :=
  have := IsAddTorsionFree.hasUniqueDiv (M := M)
  .of_injective_addHom
    ((DivisibleHull.coeAddMonoidHom _).comp Algebra.GrothendieckAddGroup.of).toAddHom
    (DivisibleHull.coe_injective.comp Algebra.GrothendieckAddGroup.of_injective) inferInstance

/-- A torsion-free cancellative commutative monoid has two unique products. -/
@[to_additive existing TauCeti.IsAddTorsionFree.to_twoUniqueSums]
instance (priority := low) IsMulTorsionFree.to_twoUniqueProds [CancelCommMonoid M]
    [IsMulTorsionFree M] : TwoUniqueProds M :=
  -- As for `AffineMonoid.to_twoUniqueProds`, transfer the additive statement along `Additive M`.
  Multiplicative.instTwoUniqueProdsOfTwoUniqueSums (M := Additive M)

/-- A torsion-free abelian group has two unique sums; unlike
`TauCeti.IsAddTorsionFree.to_twoUniqueSums`, this fires directly for `[Module.Free ℤ G]` via
`Module.Free.instIsTorsionFree`. -/
instance (priority := low) Module.IsTorsionFree.to_twoUniqueSums_int {G : Type*} [AddCommGroup G]
    [Module.IsTorsionFree ℤ G] : TwoUniqueSums G :=
  have : HasUniqueDiv G := .of_isTorsionFree ℤ G
  inferInstance

end TauCeti

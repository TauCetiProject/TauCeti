/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Separability between abstract and canonical fraction fields

If `B` is an `A`-algebra, any two pairs `(K₁, L₁)` and `(K₂, L₂)` of fraction fields of `A` and
`B` sit in a canonical square of `A`- and `B`-algebra isomorphisms (`IsLocalization.algEquiv`),
which commutes by `IsFractionRing.algEquiv_commutes`. Separability of `L₁ / K₁` therefore transfers
to `L₂ / K₂`, and in particular to Mathlib's canonical `FractionRing A` and `FractionRing B`.

## Main results

* `TauCeti.IsFractionRing.isSeparable_of_isFractionRing`: separability transfers between any two
  pairs of fraction fields of `A` and `B`.
* `TauCeti.IsFractionRing.isSeparable_fractionRing`: separability of `L / K` transfers to
  `FractionRing B / FractionRing A`.
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

/-- Separability transfers between any two pairs of fraction fields of `A` and `B`. -/
theorem IsFractionRing.isSeparable_of_isFractionRing
    (A B K₁ L₁ K₂ L₂ : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Field K₁] [Field L₁] [Field K₂] [Field L₂]
    [Algebra A K₁] [Algebra B L₁] [Algebra K₁ L₁] [Algebra A L₁]
    [IsScalarTower A K₁ L₁] [IsScalarTower A B L₁]
    [IsFractionRing A K₁] [IsFractionRing B L₁]
    [Algebra A K₂] [Algebra B L₂] [Algebra K₂ L₂] [Algebra A L₂]
    [IsScalarTower A K₂ L₂] [IsScalarTower A B L₂]
    [IsFractionRing A K₂] [IsFractionRing B L₂]
    [Algebra.IsSeparable K₁ L₁] :
    Algebra.IsSeparable K₂ L₂ :=
  have : NoZeroDivisors A :=
    (IsFractionRing.injective A K₁).noZeroDivisors _ (map_zero _) (map_mul _)
  have : Nontrivial A := (algebraMap A K₁).domain_nontrivial
  have : IsDomain A := NoZeroDivisors.to_isDomain A
  Algebra.IsSeparable.of_equiv_equiv
    (IsLocalization.algEquiv A⁰ K₁ K₂).toRingEquiv
    (IsLocalization.algEquiv B⁰ L₁ L₂).toRingEquiv
    (RingHom.ext fun x ↦ IsFractionRing.algEquiv_commutes
      (IsLocalization.algEquiv A⁰ K₁ K₂) (IsLocalization.algEquiv B⁰ L₁ L₂) x)

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
/-- Separability of `L / K` for fraction fields of `A` and `B` transfers to the canonical fraction
fields `FractionRing A` and `FractionRing B` used by Mathlib's integral-closure and different-ideal
APIs. -/
theorem IsFractionRing.isSeparable_fractionRing
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.IsTorsionFree A B]
    [Field K] [Field L] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [Algebra.IsSeparable K L] :
    Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
  IsFractionRing.isSeparable_of_isFractionRing A B K L (FractionRing A) (FractionRing B)

end TauCeti

end

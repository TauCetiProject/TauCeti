/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Separability for canonical fraction fields

Separability of an extension of fraction fields can be transported to the canonical fraction
rings. This lets results stated for the canonical fraction rings be applied with other models
of the fraction fields.
-/

public section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

/-- If `L / K` is separable for fraction fields `K` of `A` and `L` of `B`, then the extension
of canonical fraction fields is separable. -/
theorem isSeparable_fractionRing_of_isFractionRing (A B K L : Type*)
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra A B] [FaithfulSMul A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L]
    [IsFractionRing A K] [IsFractionRing B L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L] : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
  Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
    (FractionRing.algEquiv B L).symm.toRingEquiv
    (RingHom.ext fun x ↦ IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K).symm
      (FractionRing.algEquiv B L).symm x)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Group actions on integral closures

A faithful group action on a field `L` restricts faithfully to `integralClosure A L` whenever
`L` is a fraction field of `integralClosure A L` (in particular, when `A` embeds into `L` and
`L / A` is algebraic, or when `L / K` is algebraic over a fraction field `K` of `A`). We also
record that restricting scalars of an automorphism along a tower `L / E / K` does not change its
action on `integralClosure A L`.

## Main results

* `AlgEquiv.restrictScalars_smul_integralClosure`: restricting scalars of `σ : L ≃ₐ[E] L` does
  not change its action on `integralClosure A L`.
* `TauCeti.instFaithfulSMulIntegralClosureOfIsFractionRing`: faithful actions on `L` restrict
  faithfully to `integralClosure A L` when `L` is its fraction field.
* `TauCeti.instFaithfulSMulIntegralClosureOfIsAlgebraic`: faithful actions on an algebraic
  extension `L` over an embedded base `A` restrict faithfully to `integralClosure A L`.
* `TauCeti.instFaithfulSMulAlgEquivIntegralClosure`: `L ≃ₐ[K] L` acts faithfully on
  `integralClosure A L` for an algebraic extension `L / K` over a fraction field `K` of `A`.
-/

public section

/-- Restricting the scalars of an automorphism along `L / E / K` does not change its action on
`integralClosure A L`. -/
@[simp] theorem AlgEquiv.restrictScalars_smul_integralClosure {A K E L : Type*} [CommRing A]
    [CommRing K] [CommRing E] [CommRing L] [Algebra A L] [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L] [SMulCommClass (L ≃ₐ[K] L) A L] [SMulCommClass (L ≃ₐ[E] L) A L]
    (σ : L ≃ₐ[E] L) (x : integralClosure A L) :
    σ.restrictScalars K • x = σ • x :=
  Subtype.ext (by simp [AlgEquiv.smul_def])

namespace TauCeti

section FaithfulSMul

variable {G A L : Type*} [CommRing A] [Field L] [Algebra A L] [Group G] [MulSemiringAction G L]
  [SMulCommClass G A L] [FaithfulSMul G L]

/-- A faithful group action on a field `L` restricts faithfully to `integralClosure A L` whenever
`L` is a fraction field of `integralClosure A L`. -/
instance instFaithfulSMulIntegralClosureOfIsFractionRing [IsFractionRing (integralClosure A L) L] :
    FaithfulSMul G (integralClosure A L) :=
  ⟨fun h ↦ eq_of_smul_eq_smul fun y : L ↦ by
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (integralClosure A L) y
    simp only [smul_div₀', ← algebraMap.coe_smul', h]⟩

/-- A faithful group action on an algebraic field extension `L` over an embedded base ring `A`
restricts faithfully to `integralClosure A L`. -/
instance instFaithfulSMulIntegralClosureOfIsAlgebraic [FaithfulSMul A L] [Algebra.IsAlgebraic A L] :
    FaithfulSMul G (integralClosure A L) :=
  letI := IsIntegralClosure.isFractionRing_of_algebraic A (integralClosure A L)
    fun _ ↦ (FaithfulSMul.algebraMap_eq_zero_iff A L).mp
  inferInstance

end FaithfulSMul

/-- For an algebraic extension `L / K` over a fraction field `K` of `A`, `L ≃ₐ[K] L` acts
faithfully on `integralClosure A L`. -/
instance instFaithfulSMulAlgEquivIntegralClosure {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsFractionRing A K]
    [Algebra.IsAlgebraic K L] : FaithfulSMul (L ≃ₐ[K] L) (integralClosure A L) :=
  have : FaithfulSMul A L := .trans A K L
  have : IsDomain A := IsDomain.of_faithfulSMul A L
  have : Algebra.IsAlgebraic A L := IsFractionRing.comap_isAlgebraic_iff.mpr ‹_›
  inferInstance

end TauCeti

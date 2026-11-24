/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.IntegrallyClosed
public import TauCeti.AlgebraicGeometry.MonoidAlgebra.BaseChange
public import TauCeti.AlgebraicGeometry.Scheme.Normal

/-!
# Normality of affine semigroup schemes and their integral models

For an additive submonoid `S` of a torsion-free abelian group `G` and an integral domain `R`,
`AddMonoidAlgebra R S` is a domain, so `Spec (AddMonoidAlgebra R S)` is a normal scheme exactly
when `AddMonoidAlgebra R S` is integrally closed
(`TauCeti.AlgebraicGeometry.isNormalScheme_Spec_iff`). Combining this with
`isIntegrallyClosed_iff_isIntegrallyClosed_and_nsmulSaturation_inf_closure_eq` in
`TauCeti.AddMonoidAlgebra` characterizes normality of affine semigroup schemes and of their
integral models `addMonoidAlgebraIntegralModel S = Spec (AddMonoidAlgebra ℤ S)` in terms of
saturation inside `AddSubgroup.closure S`.

## Main results

* `TauCeti.AlgebraicGeometry.isNormalScheme_addMonoidAlgebraIntegralModel`: the integral model
  `addMonoidAlgebraIntegralModel S` is a normal scheme whenever `AddMonoidAlgebra ℤ S` is an
  integrally closed domain.
* `TauCeti.AlgebraicGeometry.isNormalScheme_Spec_addMonoidAlgebra_iff`: over an integral domain `R`,
  `Spec (AddMonoidAlgebra R S)` is normal iff `R` is integrally closed and `S` is saturated inside
  `AddSubgroup.closure S`.
* `TauCeti.AlgebraicGeometry.isNormalScheme_Spec_addMonoidAlgebra_of_nsmulSaturated`: when `R` is
  an integrally closed domain and `S` is saturated in `G`, `Spec (AddMonoidAlgebra R S)` is normal.
* `TauCeti.AlgebraicGeometry.isNormalScheme_addMonoidAlgebraIntegralModel_iff`: the integral model
  `addMonoidAlgebraIntegralModel S` is normal iff `S` is saturated inside `AddSubgroup.closure S`.
* `TauCeti.AlgebraicGeometry.isNormalScheme_addMonoidAlgebraIntegralModel_of_nsmulSaturated`: when
  `S` is saturated in `G`, `addMonoidAlgebraIntegralModel S` is a normal scheme.
-/

public section

open AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

/-- The integral affine semigroup model `Spec ℤ[S]` of a commutative additive monoid `S` whose
integral monoid algebra `ℤ[S]` is an integrally closed domain is a normal scheme. -/
instance isNormalScheme_addMonoidAlgebraIntegralModel (S : Type*) [AddCommMonoid S]
    [IsDomain (AddMonoidAlgebra ℤ S)] [IsIntegrallyClosed (AddMonoidAlgebra ℤ S)] :
    IsNormalScheme (addMonoidAlgebraIntegralModel S) := by
  rw [addMonoidAlgebraIntegralModel_def]
  exact isNormalScheme_Spec (.of (AddMonoidAlgebra ℤ S))

variable {G : Type*} [AddCommGroup G] [Module.IsTorsionFree ℤ G]

/-- Over an integral domain `R`, the affine semigroup scheme `Spec R[S]` of a submonoid `S` of a
torsion-free abelian group `G` is normal if and only if `R` is integrally closed and `S` is
saturated inside the subgroup `AddSubgroup.closure S` it generates. -/
theorem isNormalScheme_Spec_addMonoidAlgebra_iff (R : Type*) [CommRing R] [IsDomain R]
    (S : AddSubmonoid G) :
    IsNormalScheme (Spec (.of (AddMonoidAlgebra R S))) ↔
      IsIntegrallyClosed R ∧
        S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid = S :=
  (isNormalScheme_Spec_iff (.of (AddMonoidAlgebra R S))).trans
    AddMonoidAlgebra.isIntegrallyClosed_iff_isIntegrallyClosed_and_nsmulSaturation_inf_closure_eq

/-- Over an integrally closed domain `R`, the affine semigroup scheme `Spec R[S]` of a saturated
submonoid `S` of a torsion-free abelian group `G` is normal. -/
theorem isNormalScheme_Spec_addMonoidAlgebra_of_nsmulSaturated (R : Type*) [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] {S : AddSubmonoid G} (hS : S.NSMulSaturated) :
    IsNormalScheme (Spec (.of (AddMonoidAlgebra R S))) :=
  have := hS.isIntegrallyClosed_addMonoidAlgebra (R := R)
  inferInstance

/-- The integral affine semigroup model `Spec ℤ[S]` of a submonoid `S` of a torsion-free abelian
group `G` is normal if and only if `S` is saturated inside `AddSubgroup.closure S`. -/
theorem isNormalScheme_addMonoidAlgebraIntegralModel_iff (S : AddSubmonoid G) :
    IsNormalScheme (addMonoidAlgebraIntegralModel S) ↔
      S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid = S := by
  rw [addMonoidAlgebraIntegralModel_def, isNormalScheme_Spec_iff]
  exact
    AddMonoidAlgebra.isIntegrallyClosed_iff_nsmulSaturation_inf_closure_eq_of_isIntegrallyClosed

/-- The integral affine semigroup model `Spec ℤ[S]` of a saturated submonoid `S` of a torsion-free
abelian group `G` is a normal scheme. -/
theorem isNormalScheme_addMonoidAlgebraIntegralModel_of_nsmulSaturated {S : AddSubmonoid G}
    (hS : S.NSMulSaturated) :
    IsNormalScheme (addMonoidAlgebraIntegralModel S) :=
  have := hS.isIntegrallyClosed_addMonoidAlgebra (R := ℤ)
  inferInstance

end TauCeti.AlgebraicGeometry

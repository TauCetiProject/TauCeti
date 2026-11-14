/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.TensorProduct
public import TauCeti.FieldTheory.Separable.Regular
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Constant field extensions of regular fields

Let `F / k` be a field extension that is geometrically reduced and has exact constants, for
instance one with a separating element and exact constants. Then `F` is a regular extension of `k`
(`TauCeti.isDomain_tensorProduct_of_isGeometricallyReduced`), so `F ⊗[k] k'` is a domain for every
algebraic extension `k' / k`, separable or not. Hence multiplication `F ⊗[k] k' → F · k'` is an
isomorphism onto the constant field extension, discharging the domain hypothesis of
`TauCeti.productMap_bijective_of_constantCompositum_eq_top`. For a function field `F`, this says
that the function field of the curve after an algebraic extension of the constants is
`F ⊗[k] k'`.

Because `F · k'` is therefore the fraction field of `F ⊗[k] k'`, scalar stability of regular
extensions (`TauCeti.isIntegrallyClosedIn_of_isFractionRing_tensorProduct` and
`TauCeti.isGeometricallyReduced_of_isFractionRing_tensorProduct`) implies that `F · k'` is again
geometrically reduced over `k'` with exact constant field `k'`, even when `k' / k` is inseparable.
Compare `IsIntegrallyClosedIn.of_constantCompositum_eq_top`, which drops geometric reducedness of
`F / k` at the cost of requiring `k' / k` to be separable.

## Main results

* `TauCeti.productMap_bijective_of_isGeometricallyReduced`: for `F` geometrically reduced with
  exact constants, multiplication `F ⊗[k] k' → F · k'` is an isomorphism for every algebraic
  extension `k' / k`.
* `TauCeti.productMap_bijective_of_separating`: the same for `F` with a separating element and
  exact constants.
* `TauCeti.isDomain_tensorProduct_of_constantCompositum_eq_top_of_isGeometricallyReduced`: for any
  algebraic `k' / k` and domain `k'`-algebra `A`, `(F · k') ⊗[k'] A` is a domain.
* `TauCeti.isIntegrallyClosedIn_of_constantCompositum_eq_top_of_isGeometricallyReduced` and
  `TauCeti.isGeometricallyReduced_of_constantCompositum_eq_top_of_isGeometricallyReduced`: `k'` is
  exact in `F · k'` and `F · k'` is geometrically reduced over `k'`, whether or not `k' / k` is
  separable.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
* S. Lang, *Introduction to Algebraic Geometry*, Interscience, 1958, Chapter III, Section 1.
-/

public section

open scoped TensorProduct IntermediateField

namespace TauCeti

variable {k F k' F' : Type*} [Field k] [Field F] [Algebra k F] [Field k'] [Field F'] [Algebra k k']
  [Algebra k F'] [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra.IsAlgebraic k k']

/-- **A constant field extension of a regular field is a tensor product.** If `F` is geometrically
reduced with exact constants, then multiplication `F ⊗[k] k' → F · k'` is bijective for every
algebraic extension `k' / k`, separable or not. -/
theorem productMap_bijective_of_isGeometricallyReduced (hex : IsIntegrallyClosedIn k F)
    [Algebra.IsGeometricallyReduced k F] (h : constantCompositum F k' F' = ⊤) :
    Function.Bijective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')) :=
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex k'
  productMap_bijective_of_constantCompositum_eq_top h

/-- **A constant field extension of a separably generated field is a tensor product.** If `F` has
a separating element and exact constants, then multiplication `F ⊗[k] k' → F · k'` is bijective for
every algebraic extension `k' / k`, separable or not. -/
theorem productMap_bijective_of_separating (hex : IsIntegrallyClosedIn k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] (h : constantCompositum F k' F' = ⊤) :
    Function.Bijective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')) :=
  have := isGeometricallyReduced_of_separating hx
  productMap_bijective_of_isGeometricallyReduced hex h

section Stability

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

/-- **An algebraic constant field extension of a regular field stays regular.** If `F / k` is
geometrically reduced with exact constants and `F' = F · k'` for an algebraic extension `k' / k`
(separable or inseparable), then `F' ⊗[k'] A` is a domain for every domain `k'`-algebra `A`. -/
theorem isDomain_tensorProduct_of_constantCompositum_eq_top_of_isGeometricallyReduced
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (h : constantCompositum F k' F' = ⊤) (A : Type*) [CommRing A] [IsDomain A] [Algebra k' A] :
    IsDomain (F' ⊗[k'] A) := by
  have := isDomain_tensorProduct_of_isGeometricallyReduced hex k'
  let _ : Field (F ⊗[k] k') :=
    (Algebra.TensorProduct.isField_of_isAlgebraic k F k' (.inr inferInstance)).toField
  set π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  let _ : Algebra (F ⊗[k] k') F' := π.toRingHom.toAlgebra
  have : IsScalarTower k' (F ⊗[k] k') F' := .of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra, π]
  have hπ := productMap_bijective_of_isGeometricallyReduced (k := k) hex h
  have : IsFractionRing (F ⊗[k] k') F' :=
    .of_algEquiv (AlgEquiv.ofBijective (Algebra.ofId (F ⊗[k] k') F') hπ)
  exact isDomain_tensorProduct_of_isFractionRing_tensorProduct hex (K := k') (Q := F') A

/-- **Exact constants after any algebraic constant extension of a regular field.** If `F / k` is
geometrically reduced with exact constants and `F' = F · k'` for an algebraic extension `k' / k`
(separable or inseparable), then `k'` is the exact constant field of `F'`. -/
theorem isIntegrallyClosedIn_of_constantCompositum_eq_top_of_isGeometricallyReduced
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (h : constantCompositum F k' F' = ⊤) :
    IsIntegrallyClosedIn k' F' := by
  have := isDomain_tensorProduct_of_constantCompositum_eq_top_of_isGeometricallyReduced
    hex h (AlgebraicClosure k')
  exact isIntegrallyClosedIn_of_isDomain_tensorProduct (k := k') (K := F') (AlgebraicClosure k')

/-- **Geometric reducedness after any algebraic constant extension of a regular field.** If `F / k`
is geometrically reduced with exact constants and `F' = F · k'` for an algebraic extension `k' / k`
(separable or inseparable), then `F'` is geometrically reduced over `k'`. -/
theorem isGeometricallyReduced_of_constantCompositum_eq_top_of_isGeometricallyReduced
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (h : constantCompositum F k' F' = ⊤) :
    Algebra.IsGeometricallyReduced k' F' := by
  have := isDomain_tensorProduct_of_constantCompositum_eq_top_of_isGeometricallyReduced
    hex h (AlgebraicClosure k')
  exact isGeometricallyReduced_of_isReduced_tensorProduct (k := k') (AlgebraicClosure k')

end Stability

end TauCeti

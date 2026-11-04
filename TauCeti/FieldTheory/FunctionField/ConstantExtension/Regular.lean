/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.TensorProduct
public import TauCeti.FieldTheory.Separable.Regular

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

## Main results

* `TauCeti.productMap_bijective_of_isGeometricallyReduced`: for `F` geometrically reduced with
  exact constants, multiplication `F ⊗[k] k' → F · k'` is an isomorphism for every algebraic
  extension `k' / k`.
* `TauCeti.productMap_bijective_of_separating`: the same for `F` with a separating element and
  exact constants.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
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

end TauCeti

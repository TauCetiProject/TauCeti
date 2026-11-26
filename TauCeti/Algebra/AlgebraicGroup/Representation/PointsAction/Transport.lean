/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Transport
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Hom

/-!
# Base-point action on transported comodules

Transporting a right comodule structure across a linear equivalence `e : M ≃ₗ[R] N` via
`TauCeti.Comodule.Transport` turns `e` into a comodule isomorphism `transportToHom e`. Consequently,
the base-valued point representation on the transported comodule is conjugate by `e` to the original
representation.

## Main results

* `LinearEquiv.basePointsRepresentation_transport`: transporting a comodule along a linear
  equivalence conjugates its base-point representation.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* J. S. Milne, *Algebraic Groups* (2017), §4.a.
-/

public section

open WithConv
open TauCeti (Comodule)
open TauCeti.Comodule (Transport transportToHom transportToHom_apply basePointsRepresentation)

namespace LinearEquiv

variable {R H M N : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M]
  [AddCommMonoid N] [Module R N]

/-- Transporting a comodule along a linear equivalence conjugates its base-point representation. -/
theorem basePointsRepresentation_transport (e : M ≃ₗ[R] N) (g : WithConv (H →ₐ[R] R)) :
    (letI : Comodule R H N := Transport (R := R) (C := H) e
     basePointsRepresentation (R := R) (H := H) N g) =
      e.toLinearMap ∘ₗ basePointsRepresentation (R := R) (H := H) M g ∘ₗ e.symm.toLinearMap := by
  let _ : Comodule R H N := Transport (R := R) (C := H) e
  ext n
  have h := ((transportToHom (R := R) (C := H) e).map_basePointsRepresentation g (e.symm n)).symm
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, transportToHom_apply,
    LinearEquiv.apply_symm_apply] using h

end LinearEquiv

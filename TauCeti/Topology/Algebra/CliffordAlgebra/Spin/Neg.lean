/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Neg
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic

/-!
# The Spin groups of a quadratic form and of its negative as topological groups

The isomorphism `CliffordAlgebra.spinGroupEquivNeg Q : spinGroup Q ≃* spinGroup (-Q)` restricts
Mathlib's identification `CliffordAlgebra.evenEquivEvenNeg Q` of the even Clifford algebras of `Q`
and `-Q`. Every linear map out of an even Clifford subalgebra is continuous for the subspace
topology of the module topology (`CliffordAlgebra.continuous_even_linearMap`), so this isomorphism
and its inverse are continuous for the subtype topologies of the two Spin groups. It is therefore
an isomorphism of topological groups. No finiteness assumption is needed: the base is any
topological commutative ring in which `2` is invertible.

## Main definitions

* `CliffordAlgebra.spinGroupContinuousMulEquivNeg Q`: the isomorphism `spinGroupEquivNeg Q` of
  topological groups.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §§1–3.
-/

public section

namespace CliffordAlgebra

variable {R V : Type*} [CommRing R] [TopologicalSpace R] [AddCommGroup V] [Module R V]
  [Invertible (2 : R)] (Q : QuadraticForm R V)

/-- The isomorphism `spinGroupEquivNeg Q` between the Spin groups of `Q` and `-Q`, as an
isomorphism of topological groups for the subtype topologies. -/
noncomputable def spinGroupContinuousMulEquivNeg : spinGroup Q ≃ₜ* spinGroup (-Q) where
  toMulEquiv := spinGroupEquivNeg Q
  continuous_toFun := continuous_spinGroup_of_coe_eq
    ((even (-Q)).val.toLinearMap ∘ₗ (evenEquivEvenNeg Q).toLinearMap)
    (coe_spinGroupEquivNeg_apply Q)
  continuous_invFun := continuous_spinGroup_of_coe_eq
    ((even Q).val.toLinearMap ∘ₗ (evenEquivEvenNeg Q).symm.toLinearMap)
    (coe_spinGroupEquivNeg_symm_apply Q)

/-- The topological isomorphism `spinGroupContinuousMulEquivNeg Q` evaluates as
`spinGroupEquivNeg Q`. -/
@[simp]
theorem coe_spinGroupContinuousMulEquivNeg :
    ⇑(spinGroupContinuousMulEquivNeg Q) = spinGroupEquivNeg Q :=
  (rfl)

/-- The inverse of `spinGroupContinuousMulEquivNeg Q` evaluates as the inverse of
`spinGroupEquivNeg Q`. -/
@[simp]
theorem coe_spinGroupContinuousMulEquivNeg_symm :
    ⇑(spinGroupContinuousMulEquivNeg Q).symm = (spinGroupEquivNeg Q).symm :=
  (rfl)

end CliffordAlgebra

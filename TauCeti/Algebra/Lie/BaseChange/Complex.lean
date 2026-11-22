/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Basic
public import TauCeti.LinearAlgebra.Complex.Module

/-!
# The underlying linear equivalence of a scalar-restricted complex Lie algebra

The additive-monoid parent of the restricted Lie ring and that of its restricted additive
group are inherited through different instances. The normalized equivalence uses the latter
parent and the corresponding real module, with the original forward and inverse functions.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer Monographs in
  Mathematics (2012), §15.1, Definition 15.1.1.
-/

public section

namespace LieEquiv

variable {L L' : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRing L'] [LieAlgebra ℝ L']
  (e : RestrictScalars ℝ ℂ L ≃ₗ⁅ℝ⁆ L')

/-- The underlying real-linear equivalence, using the canonical additive-group parent of
scalar restriction. -/
noncomputable def toRealLinearEquiv :
    letI : AddCommMonoid (RestrictScalars ℝ ℂ L) :=
      (instAddCommGroupRestrictScalars ℝ ℂ L).toAddCommMonoid
    letI := RestrictScalars.realModule L
    RestrictScalars ℝ ℂ L ≃ₗ[ℝ] L' := by
  letI : AddCommMonoid (RestrictScalars ℝ ℂ L) :=
      (instAddCommGroupRestrictScalars ℝ ℂ L).toAddCommMonoid
  letI := RestrictScalars.realModule L
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := e.map_smul }

/-- The normalized real-linear comparison has the same forward map as the Lie equivalence. -/
@[simp]
theorem toRealLinearEquiv_apply (x : RestrictScalars ℝ ℂ L) :
    e.toRealLinearEquiv x = e x := by
  rfl

/-- The normalized real-linear comparison has the same inverse as the Lie equivalence. -/
@[simp]
theorem toRealLinearEquiv_symm_apply (x : L') :
    e.toRealLinearEquiv.symm x = e.symm x := by
  rfl

end LieEquiv

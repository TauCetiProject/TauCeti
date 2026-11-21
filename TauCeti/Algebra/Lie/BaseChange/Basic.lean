/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange

/-!
# Lie brackets and scalar restriction for `RestrictScalars`

The additive identification between a scalar-restricted Lie ring and its original carrier
preserves brackets (`RestrictScalars.addEquiv_lie`). Any `A`-linear Lie equivalence between two
`A`-Lie algebras restricts along `Algebra R A` to an `R`-linear Lie equivalence
`LieEquiv.restrictScalars` between their `RestrictScalars R A` type aliases.

## Main definitions and results

* `RestrictScalars.addEquiv_lie`: `RestrictScalars.addEquiv` preserves Lie brackets.
* `LieEquiv.restrictScalars`: scalar restriction of a Lie algebra equivalence across
  `RestrictScalars`, together with `LieEquiv.restrictScalars_apply` and
  `LieEquiv.restrictScalars_symm_apply`.

## References

* `Mathlib.Algebra.Lie.BaseChange`, for the inherited Lie-ring and Lie-algebra structures on
  `RestrictScalars`.
-/

public section

/-- The additive identification for scalar restriction preserves the Lie bracket. -/
@[simp]
theorem RestrictScalars.addEquiv_lie {R A L : Type*} [LieRing L]
    (x y : RestrictScalars R A L) :
    RestrictScalars.addEquiv R A L ⁅x, y⁆ =
      ⁅RestrictScalars.addEquiv R A L x, RestrictScalars.addEquiv R A L y⁆ := rfl

namespace LieEquiv

variable (R : Type*) {A L₁ L₂ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [LieRing L₁] [LieAlgebra A L₁] [LieRing L₂] [LieAlgebra A L₂]

/-- Restrict the scalars of an `A`-linear Lie equivalence along `Algebra R A`, yielding an
`R`-linear Lie equivalence between the `RestrictScalars R A` type aliases. -/
def restrictScalars (e : L₁ ≃ₗ⁅A⁆ L₂) :
    RestrictScalars R A L₁ ≃ₗ⁅R⁆ RestrictScalars R A L₂ where
  toFun x := (RestrictScalars.addEquiv R A L₂).symm (e (RestrictScalars.addEquiv R A L₁ x))
  invFun y := (RestrictScalars.addEquiv R A L₁).symm (e.symm (RestrictScalars.addEquiv R A L₂ y))
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp
  map_smul' r x := by
    rw [RestrictScalars.addEquiv_map_smul, map_smul,
      RestrictScalars.addEquiv_symm_map_algebraMap_smul, RingHom.id_apply]
  map_lie' {x y} := by
    apply (RestrictScalars.addEquiv R A L₂).injective
    rw [RestrictScalars.addEquiv_lie, AddEquiv.apply_symm_apply, RestrictScalars.addEquiv_lie,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, map_lie]

/-- Evaluating a scalar-restricted Lie equivalence transports through `RestrictScalars.addEquiv`. -/
@[simp]
theorem restrictScalars_apply (e : L₁ ≃ₗ⁅A⁆ L₂) (x : RestrictScalars R A L₁) :
    e.restrictScalars R x =
      (RestrictScalars.addEquiv R A L₂).symm (e (RestrictScalars.addEquiv R A L₁ x)) := by
  rfl

/-- Evaluating the inverse of a scalar-restricted Lie equivalence transports `e.symm` through
`RestrictScalars.addEquiv`. -/
@[simp]
theorem restrictScalars_symm_apply (e : L₁ ≃ₗ⁅A⁆ L₂) (y : RestrictScalars R A L₂) :
    (e.restrictScalars R).symm y =
      (RestrictScalars.addEquiv R A L₁).symm (e.symm (RestrictScalars.addEquiv R A L₂ y)) := by
  rfl

end LieEquiv

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.Algebra.Lie.Dual

/-!
# The Killing duality `L ≃ L*`

Let `L` be a finite-dimensional Lie algebra over a field `K` whose Killing form `κ` is
nondegenerate. The Killing form is invariant, `κ ⁅x, y⁆ z = -κ y ⁅x, z⁆`, so `x ↦ κ x` is an
equivalence of Lie modules from the adjoint module `L` to the coadjoint module `L*`. This file
records that equivalence, the case of `LinearMap.BilinForm.lieModuleEquivDual` for the Killing
form, with its evaluation lemmas.

## Main definitions

* `TauCeti.killingDuality`: the Killing form as a Lie module equivalence `L ≃ L*`.

## Main results

* `TauCeti.killingDuality_apply`: the Killing duality sends `x` to `y ↦ κ(x, y)`.
* `TauCeti.killingForm_killingDuality_symm_apply`: its inverse sends `f` to the `x` with
  `κ(x, -) = f`.
* `TauCeti.toLinearMap_killingDuality`: its underlying linear map is the Killing form.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §5.1 for the
  Killing form and §23.1 for its use to identify `L` with `L*`.
-/

public section

namespace TauCeti

open LieAlgebra Module

variable (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [IsKilling K L]

/-- The **Killing duality** of a Lie algebra with nondegenerate Killing form `κ`: the equivalence
`x ↦ κ x` of the adjoint module `L` with the coadjoint module `L*`. -/
noncomputable def killingDuality : L ≃ₗ⁅K,L⁆ Dual K L :=
  (killingForm K L).lieModuleEquivDual (IsKilling.killingForm_nondegenerate K L)
    (LieModule.traceForm_lieInvariant K L L)

/-- The Killing duality sends `x` to the linear form `y ↦ κ(x, y)`. -/
@[simp]
theorem killingDuality_apply (x y : L) : killingDuality K L x y = killingForm K L x y :=
  LinearMap.BilinForm.lieModuleEquivDual_apply _ _ _ x y

/-- The inverse of the Killing duality sends a linear form `f` to the element `x` with
`κ(x, y) = f y` for all `y`. -/
@[simp]
theorem killingForm_killingDuality_symm_apply (f : Dual K L) (y : L) :
    killingForm K L ((killingDuality K L).symm f) y = f y :=
  LinearMap.BilinForm.apply_lieModuleEquivDual_symm_apply _ _ _ f y

/-- The linear map underlying the Killing duality is the Killing form, read as a linear map
`L → L*`. -/
theorem toLinearMap_killingDuality :
    ((killingDuality K L : L ≃ₗ[K] Dual K L) : L →ₗ[K] Dual K L) = killingForm K L :=
  LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ killingDuality_apply K L x y

end TauCeti

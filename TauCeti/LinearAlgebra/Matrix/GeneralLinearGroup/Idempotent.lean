/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Cutting general linear groups along idempotents

For an idempotent `e` in a commutative ring `A`, the map `g ↦ e • g + (1 - e) • 1` is a monoid
endomorphism of `Matrix n n A`, hence induces a group endomorphism `IsIdempotentElem.cutGL` of
`GL n A`. Given `c, d : GL n A`, the product `c * he.cutGL (c⁻¹ * d)` patches `c` and `d` along
`e` into the invertible matrix `e • d + (1 - e) • c` (`IsIdempotentElem.val_mul_cutGL_inv_mul`).

## Main definitions and results

* `IsIdempotentElem.cutGL`: the endomorphism `g ↦ e • g + (1 - e) • 1` of `GL n A`.
* `IsIdempotentElem.val_cutGL`: characterizing formula for the underlying matrix of `he.cutGL g`.
* `IsIdempotentElem.val_mul_cutGL_inv_mul`: patching `c` and `d` along `e` gives
  `e • d + (1 - e) • c`.

## References

* L. Alpöge and L. Sernau, Lean formalization of the generalized Riemann hypothesis for Dirichlet
  `L`-functions (`Lib/General/LinearAlgebra/IntegralLattices.lean`, `New.cutGL`),
  <https://github.com/lsernau/grh-lean> (Apache 2.0).
-/

public section

open Matrix

namespace IsIdempotentElem

variable {A n : Type*} [CommRing A] [Fintype n] [DecidableEq n] {e : A}

/-- For an idempotent `e` of a commutative ring `A`, the endomorphism `g ↦ e • g + (1 - e) • 1`
of `GL n A`. -/
def cutGL (he : IsIdempotentElem e) : GL n A →* GL n A :=
  Units.map
    { toFun g := e • g + (1 - e) • 1
      map_one' := by simp
      map_mul' := by simp [he.eq, mul_add, add_mul, smul_smul, mul_sub, sub_mul] }

/-- Characterizing formula for the underlying matrix of `he.cutGL g`. -/
@[simp]
theorem val_cutGL (he : IsIdempotentElem e) (g : GL n A) :
    (he.cutGL g).val = e • g.val + (1 - e) • 1 := by
  rfl

/-- Patching two invertible matrices `c` and `d` along an idempotent `e` gives
`e • d + (1 - e) • c`. -/
theorem val_mul_cutGL_inv_mul (he : IsIdempotentElem e) (c d : GL n A) :
    (c * he.cutGL (c⁻¹ * d)).val = e • d.val + (1 - e) • c.val := by
  rw [Units.val_mul, val_cutGL]
  simp [mul_add, -Matrix.coe_units_inv]

end IsIdempotentElem

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Ring.Idempotent

/-!
# Inverting one component of a unit

An idempotent `e` of a commutative ring `R` splits it as `R ≅ e R × (1 - e) R`, and so splits
each unit `u` into its `e`-component `e u` and its `(1 - e)`-component `(1 - e) u`. Inverting the
first component and keeping the second is the automorphism

`u ↦ e u⁻¹ + (1 - e) u`

of the unit group `Rˣ`, written here without reference to the product decomposition: since
`e² = e` and `e (1 - e) = 0`, products of elements of the form `e x + (1 - e) y` are computed
componentwise (`IsIdempotentElem.mul_add_one_sub_mul`).

The automorphism is an involution. At `e = 0` it is the identity and at `e = 1` it is inversion.
For the idempotent of `ZMod N` attached to an exact divisor `Q` of `N` it is the automorphism of
`(ZMod N)ˣ` inverting the residue modulo `Q` and fixing the residue modulo `N / Q`, through which
the Atkin–Lehner operator `W_Q` shifts the nebentypus of a modular form.

## Main definitions

* `IsIdempotentElem.unitsInvPart`: the automorphism `u ↦ e u⁻¹ + (1 - e) u` of `Rˣ`.

## Main results

* `IsIdempotentElem.mul_unitsInvPart`, `IsIdempotentElem.one_sub_mul_unitsInvPart`: the two
  components of `unitsInvPart u` are `e u⁻¹` and `(1 - e) u`.
* `IsIdempotentElem.unitsInvPart_symm`: `unitsInvPart` is an involution.
* `IsIdempotentElem.unitsInvPart_zero`, `IsIdempotentElem.unitsInvPart_one`: at `e = 0` and
  `e = 1` it is the identity and inversion.
-/

public section

namespace IsIdempotentElem

variable {R : Type*} [CommRing R] {e : R}

/-- **Inverting the `e`-component of a unit**: for an idempotent `e` of a commutative ring `R`,
the automorphism `u ↦ e u⁻¹ + (1 - e) u` of `Rˣ`. Under `R ≅ e R × (1 - e) R` it inverts the first
component and fixes the second. It is its own inverse (`unitsInvPart_symm`). -/
def unitsInvPart (he : IsIdempotentElem e) : Rˣ ≃* Rˣ :=
  .mk' (Function.Involutive.toPerm
    (fun u ↦ ⟨e * ↑u⁻¹ + (1 - e) * u, e * u + (1 - e) * ↑u⁻¹,
      by rw [he.mul_add_one_sub_mul]; simp, by rw [he.mul_add_one_sub_mul]; simp⟩)
    fun u ↦ Units.ext <| by
      simp only [Units.inv_mk]
      linear_combination 2 * (↑u - ↑u⁻¹ : R) * he.eq)
    fun u v ↦ Units.ext <| by
      simp only [Function.Involutive.toPerm, Equiv.coe_fn_mk, Units.val_mul, mul_inv_rev,
        he.mul_add_one_sub_mul]
      ring

/-- The value of `unitsInvPart` at a unit `u` is `e u⁻¹ + (1 - e) u`. -/
theorem val_unitsInvPart (he : IsIdempotentElem e) (u : Rˣ) :
    (he.unitsInvPart u : R) = e * ↑u⁻¹ + (1 - e) * u := (rfl)

/-- **`unitsInvPart` is an involution**: it is its own inverse. -/
@[simp]
theorem unitsInvPart_symm (he : IsIdempotentElem e) : he.unitsInvPart.symm = he.unitsInvPart :=
  (rfl)

/-- **`unitsInvPart` is an involution**, applied twice to a unit. -/
@[simp]
theorem unitsInvPart_unitsInvPart (he : IsIdempotentElem e) (u : Rˣ) :
    he.unitsInvPart (he.unitsInvPart u) = u :=
  he.unitsInvPart.apply_symm_apply u

/-- **The `e`-component of `unitsInvPart u`** is the `e`-component of `u⁻¹`. -/
@[simp]
theorem mul_unitsInvPart (he : IsIdempotentElem e) (u : Rˣ) :
    e * (he.unitsInvPart u : R) = e * ↑u⁻¹ := by
  rw [val_unitsInvPart]
  linear_combination (↑u⁻¹ - ↑u : R) * he.eq

/-- **The `(1 - e)`-component of `unitsInvPart u`** is the `(1 - e)`-component of `u`. -/
@[simp]
theorem one_sub_mul_unitsInvPart (he : IsIdempotentElem e) (u : Rˣ) :
    (1 - e) * (he.unitsInvPart u : R) = (1 - e) * u := by
  rw [val_unitsInvPart]
  linear_combination (↑u - ↑u⁻¹ : R) * he.eq

/-- At the idempotent `0` nothing is inverted: `unitsInvPart` is the identity. -/
@[simp]
theorem unitsInvPart_zero : (IsIdempotentElem.zero : IsIdempotentElem (0 : R)).unitsInvPart =
    MulEquiv.refl Rˣ :=
  MulEquiv.ext fun u ↦ Units.ext <| by simp [val_unitsInvPart]

/-- At the idempotent `1` everything is inverted: `unitsInvPart` is inversion. -/
@[simp]
theorem unitsInvPart_one : (IsIdempotentElem.one : IsIdempotentElem (1 : R)).unitsInvPart =
    MulEquiv.inv Rˣ :=
  MulEquiv.ext fun u ↦ Units.ext <| by simp [val_unitsInvPart]

end IsIdempotentElem

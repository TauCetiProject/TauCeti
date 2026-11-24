/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Ring.Idempotent.Basic

/-!
# Units associated to idempotents

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

For elements satisfying `e * p = p` and `p * e = e`, `TauCeti.idempotentConjUnit` is the
unit `1 + e - p` conjugating `e` to `p`. Both elements are automatically idempotent.
This is the algebraic similarity used in Blackadar, *K-Theory for Operator Algebras*,
second edition, Proposition 4.6.2.

## Main definitions

* `TauCeti.idempotentConjUnit`: the explicit similarity between such idempotents.
* `IsIdempotentElem.unitsInvPart`: the automorphism `u ↦ e u⁻¹ + (1 - e) u` of `Rˣ`.

## Main results

* `TauCeti.isConj_of_mul_eq`: if `e * p = p` and `p * e = e`, then `p` and `e` are conjugate.
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
  have hinv : Function.Involutive fun u : Rˣ ↦ (⟨e * ↑u⁻¹ + (1 - e) * u, e * u + (1 - e) * ↑u⁻¹,
      by rw [he.mul_add_one_sub_mul]; simp, by rw [he.mul_add_one_sub_mul]; simp⟩ : Rˣ) :=
    fun u ↦ Units.ext <| by
      simp only [Units.inv_mk]
      linear_combination 2 * (↑u - ↑u⁻¹ : R) * he.eq
  .mk' (hinv.toPerm _) fun u v ↦ Units.ext <| by
    simp only [Function.Involutive.coe_toPerm, Units.val_mul, mul_inv_rev, he.mul_add_one_sub_mul]
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

namespace TauCeti

variable {R : Type*} [Ring R]

/-- The unit `1 + e - p`, with inverse `1 - e + p`, conjugating `e` to `p` when
`e * p = p` and `p * e = e`. These identities already imply idempotence. -/
def idempotentConjUnit (e p : R) (hep : e * p = p) (hpe : p * e = e) : Rˣ := by
  have hee : e * e = e := by
    calc
      e * e = e * (p * e) := by rw [hpe]
      _ = e := by rw [← mul_assoc, hep, hpe]
  have hpp : p * p = p := by
    calc
      p * p = p * (e * p) := by rw [hep]
      _ = p := by rw [← mul_assoc, hpe, hep]
  exact
    { val := 1 + e - p
      inv := 1 - e + p
      val_inv := by noncomm_ring [hee, hpp, hep, hpe]
      inv_val := by noncomm_ring [hee, hpp, hep, hpe] }

/-- The value of the canonical similarity unit. -/
@[simp]
theorem coe_idempotentConjUnit (e p : R) (hep : e * p = p) (hpe : p * e = e) :
    (idempotentConjUnit e p hep hpe : R) = 1 + e - p := (rfl)

/-- The value of the inverse of the canonical similarity unit. -/
@[simp]
theorem coe_inv_idempotentConjUnit (e p : R) (hep : e * p = p) (hpe : p * e = e) :
    (↑(idempotentConjUnit e p hep hpe)⁻¹ : R) = 1 - e + p := (rfl)

/-- The canonical similarity unit conjugates `e` to `p`. -/
theorem idempotentConjUnit_mul_mul_inv (e p : R) (hep : e * p = p) (hpe : p * e = e) :
    (idempotentConjUnit e p hep hpe : R) * e * ↑(idempotentConjUnit e p hep hpe)⁻¹ = p := by
  have hee : e * e = e := by
    calc
      e * e = e * (p * e) := by rw [hpe]
      _ = e := by rw [← mul_assoc, hep, hpe]
  rw [coe_idempotentConjUnit, coe_inv_idempotentConjUnit]
  noncomm_ring [hee, hep, hpe]

/-- **Similar idempotents**: elements `p` and `e` of a ring with `e * p = p` and `p * e = e` are
conjugate, by the inverse of `TauCeti.idempotentConjUnit e p`. -/
theorem isConj_of_mul_eq {p e : R} (hep : e * p = p) (hpe : p * e = e) : IsConj p e := by
  obtain ⟨u, hu⟩ : ∃ u : Rˣ, (u : R) * e * ↑u⁻¹ = p :=
    ⟨_, idempotentConjUnit_mul_mul_inv e p hep hpe⟩
  refine ⟨u⁻¹, ?_⟩
  rw [SemiconjBy, ← hu]
  simp only [mul_assoc, Units.inv_mul_cancel_left]

end TauCeti

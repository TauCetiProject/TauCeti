/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Prod
public import Mathlib.Algebra.Star.Unitary

/-!
# Unitary elements

The unitary elements of a product of star monoids are the pairs of unitary elements. This file
packages that identification as a multiplicative equivalence. It also records that a unit is
unitary exactly when its adjoint is its inverse.

## Main definitions and results

* `Unitary.prodEquiv`: `unitary (A × B)` is multiplicatively equivalent to
  `unitary A × unitary B`.
* `Units.mem_unitary_iff_star_eq_inv`: a unit `u` is unitary if and only if `star u = u⁻¹`
  in `R`.
-/

public section

namespace Unitary

variable (A B : Type*) [Monoid A] [Monoid B] [StarMul A] [StarMul B]

/-- Unitary elements in a product are pairs of unitary elements. -/
def prodEquiv :
    unitary (A × B) ≃* unitary A × unitary B :=
  (MulEquiv.submonoidCongr (Prod.unitary_eq A B)).trans
    (Submonoid.prodEquiv (unitary A) (unitary B))

/-- The product underlying the forward unitary-product equivalence is unchanged. -/
@[simp]
theorem coe_prodEquiv_apply (u : unitary (A × B)) :
    (((prodEquiv A B u).1 : A), ((prodEquiv A B u).2 : B)) = (u : A × B) :=
  (rfl)

/-- The product underlying the inverse unitary-product equivalence is the pair of underlying
unitary elements. -/
@[simp]
theorem coe_prodEquiv_symm_apply (u : unitary A × unitary B) :
    ((prodEquiv A B).symm u : A × B) = ((u.1 : A), (u.2 : B)) :=
  (rfl)

end Unitary

namespace Units

section Monoid

variable {R : Type*} [Monoid R] [StarMul R] {u : Rˣ}

/-- A unit is unitary exactly when its adjoint is its inverse. -/
theorem mem_unitary_iff_star_eq_inv : (u : R) ∈ unitary R ↔ star (u : R) = ↑u⁻¹ :=
  ⟨fun h ↦ (u.inv_eq_of_mul_eq_one_left (Unitary.star_mul_self_of_mem h)).symm,
    fun h ↦ u.isUnit.mem_unitary_of_star_mul_self (h ▸ u.inv_mul)⟩

/-- The adjoint of the inverse of a unit whose underlying element is unitary is the unit. -/
theorem star_inv_eq_of_mem_unitary (h : (u : R) ∈ unitary R) : star (↑u⁻¹ : R) = u := by
  rw [← mem_unitary_iff_star_eq_inv.1 h, star_star]

end Monoid

/-- For a unit `u` whose underlying element is unitary, `u - u⁻¹` is skew-adjoint. -/
theorem star_sub_inv_of_mem_unitary {R : Type*} [Ring R] [StarRing R] {u : Rˣ}
    (h : (u : R) ∈ unitary R) : star ((u : R) - ↑u⁻¹) = ↑u⁻¹ - u := by
  rw [star_sub, mem_unitary_iff_star_eq_inv.1 h, star_inv_eq_of_mem_unitary h]

end Units

end

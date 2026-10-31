/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Unit reflection and kernels of ring homomorphisms

A surjective map of commutative rings whose kernel consists of nilpotent elements reflects
units. The kernel of any unit-reflecting map is contained in the Jacobson radical.
Here unit reflection is Mathlib's `IsLocalHom`; neither ring is required to be local.

These facts allow unit reflection to propagate through inverse systems with locally nilpotent
transition kernels. Elementwise nilpotence suffices, without a uniform exponent.
-/

public section

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A surjective ring homomorphism with elementwise nilpotent kernel reflects units.
No uniform nilpotence exponent is required. -/
theorem isLocalHom_of_surjective_of_isNilpotent_ker (f : R →+* S)
    (hf : Function.Surjective f) (hnil : ∀ x, f x = 0 → IsNilpotent x) :
    IsLocalHom f := by
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨y, hy⟩ := hf (↑hx.unit⁻¹)
  have hxy : IsNilpotent (x * y - 1) := hnil _ (by simp [hy, hx.mul_val_inv])
  exact isUnit_of_mul_isUnit_left (by simpa using hxy.isUnit_add_one)

/-- The kernel of a unit-reflecting ring map is contained in the Jacobson radical. -/
theorem ker_le_jacobson (f : R →+* S) [IsLocalHom f] :
    ker f ≤ Ideal.jacobson (⊥ : Ideal R) := by
  intro x hx
  refine Ideal.mem_jacobson_bot.mpr fun y ↦ isUnit_of_map_unit f _ ?_
  simp only [mem_ker] at hx
  simp [hx]

end RingHom

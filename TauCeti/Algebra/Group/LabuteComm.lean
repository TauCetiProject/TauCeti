/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Labute's commutator

Labute's commutator `(x, y) = x⁻¹y⁻¹xy` is the commutator convention in which the relators of the
Demushkin normal forms are written; Mathlib's `⁅x, y⁆ = xyx⁻¹y⁻¹` is the other convention.

## Main declarations

* `TauCeti.labuteComm`: Labute's commutator.
* `TauCeti.labuteComm_eq_commutatorElement_inv_inv`: its relation to Mathlib's commutator.
* `TauCeti.map_labuteComm`: monoid homomorphisms preserve it.
* `TauCeti.labuteComm_eq_one_iff_commute`: it is trivial exactly for commuting elements.
-/

public section

namespace TauCeti

open scoped commutatorElement

variable {H : Type*} [Group H]

/-- **Labute's commutator** `(x, y) = x⁻¹y⁻¹xy`, the convention in which the Demushkin
normal-form relators are written. Mathlib's `⁅x, y⁆ = xyx⁻¹y⁻¹` is the other convention; the two
are related by `TauCeti.labuteComm_eq_commutatorElement_inv_inv`, and generate the same
subgroups. -/
def labuteComm (x y : H) : H := x⁻¹ * y⁻¹ * x * y

/-- The defining equation of `TauCeti.labuteComm`. -/
theorem labuteComm_def (x y : H) : labuteComm x y = x⁻¹ * y⁻¹ * x * y := (rfl)

/-- Labute's commutator is Mathlib's commutator of the inverses: `(x, y) = ⁅x⁻¹, y⁻¹⁆`. -/
theorem labuteComm_eq_commutatorElement_inv_inv (x y : H) : labuteComm x y = ⁅x⁻¹, y⁻¹⁆ := by
  rw [labuteComm_def, commutatorElement_def, inv_inv, inv_inv]

/-- A monoid homomorphism carries Labute's commutator to Labute's commutator. -/
@[simp]
theorem map_labuteComm {K F : Type*} [Group K] [FunLike F H K] [MonoidHomClass F H K] (f : F)
    (x y : H) : f (labuteComm x y) = labuteComm (f x) (f y) := by
  simp only [labuteComm_def, map_mul, map_inv]

/-- Labute's commutator is trivial exactly when the two elements commute. -/
theorem labuteComm_eq_one_iff_commute (x y : H) : labuteComm x y = 1 ↔ Commute x y := by
  rw [labuteComm_eq_commutatorElement_inv_inv, commutatorElement_eq_one_iff_commute,
    Commute.inv_inv_iff]

/-- Labute's commutator of two commuting elements is trivial. -/
theorem _root_.Commute.labuteComm_eq_one {x y : H} (h : Commute x y) : labuteComm x y = 1 :=
  (labuteComm_eq_one_iff_commute x y).mpr h

/-- Labute's commutator is trivial in a commutative group. -/
@[simp]
theorem labuteComm_eq_one {A : Type*} [CommGroup A] (x y : A) : labuteComm x y = 1 :=
  (Commute.all x y).labuteComm_eq_one

end TauCeti

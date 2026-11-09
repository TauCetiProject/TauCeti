/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.BigOperators
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
* `TauCeti.labuteComm_mem_commutator`, `TauCeti.labuteComm_mem_of_mem_left`,
  `TauCeti.labuteComm_mem_commutator_of_mem` and
  `TauCeti.list_prod_map_labuteComm_range_mem_commutator`: it, and products of such, lie in the
  commutator subgroup or in `⁅N, N⁆`.
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

/-- Labute's commutator lies in the commutator subgroup. -/
theorem labuteComm_mem_commutator (x y : H) : labuteComm x y ∈ commutator H := by
  rw [labuteComm_eq_commutatorElement_inv_inv]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- Labute's commutator `(x, y) = x⁻¹ (y⁻¹ x y)` of an element `x` of a normal subgroup `N` with
any `y` lies in `N`. -/
theorem labuteComm_mem_of_mem_left {N : Subgroup H} [N.Normal] {x : H} (hx : x ∈ N) (y : H) :
    labuteComm x y ∈ N := by
  rw [labuteComm_def, mul_assoc, mul_assoc]
  exact N.mul_mem (N.inv_mem hx) (by simpa only [mul_assoc] using ‹N.Normal›.conj_mem' _ hx y)

/-- Labute's commutator of two elements of a subgroup `N` lies in `⁅N, N⁆`. -/
theorem labuteComm_mem_commutator_of_mem {N : Subgroup H} {x y : H} (hx : x ∈ N) (hy : y ∈ N) :
    labuteComm x y ∈ ⁅N, N⁆ := by
  rw [labuteComm_eq_commutatorElement_inv_inv]
  exact Subgroup.commutator_mem_commutator (N.inv_mem hx) (N.inv_mem hy)

/-- A product of Labute's commutators of elements of a subgroup `N` lies in `⁅N, N⁆`. -/
theorem list_prod_map_labuteComm_range_mem_commutator {N : Subgroup H} (m : ℕ) {a b : ℕ → H}
    (ha : ∀ i < m, a i ∈ N) (hb : ∀ i < m, b i ∈ N) :
    ((List.range m).map fun i ↦ labuteComm (a i) (b i)).prod ∈ ⁅N, N⁆ := by
  refine list_prod_mem ?_
  simpa only [List.forall_mem_map, List.mem_range] using
    fun i hi ↦ labuteComm_mem_commutator_of_mem (ha i hi) (hb i hi)

end TauCeti

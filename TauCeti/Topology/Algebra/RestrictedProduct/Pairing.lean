/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Pairings on restricted products

A family of biadditive pairings which vanishes on the reference subgroups induces a
pairing of restricted products by summing its local values. Restrictedness makes this an
honest finite sum, even when neither argument has finite support.

Testing against elements supported at one index recovers the local pairing. Consequently
local nondegeneracy implies nondegeneracy of the sum pairing, and the annihilator of the
product of reference subgroups is described coordinatewise. These constructions apply to
sums of local duality pairings with orthogonal local conditions.
-/

public noncomputable section

namespace RestrictedProduct

open scoped RestrictedProduct

variable {ι : Type*} {A B : ι → Type*} {C : Type*}
  [∀ i, AddGroup (A i)] [∀ i, AddGroup (B i)] [AddCommMonoid C]
  (U : ∀ i, AddSubgroup (A i)) (V : ∀ i, AddSubgroup (B i))
  (p : ∀ i, A i →+ B i →+ C)
  (hp : ∀ i, ∀ a ∈ U i, ∀ b ∈ V i, p i a b = 0)

include hp

/-- Local values of an orthogonal family of pairings have finite support on restricted
products. -/
theorem hasFiniteSupport_pairing (x : Πʳ i, [A i, U i]) (y : Πʳ i, [B i, V i]) :
    (fun i ↦ p i (x i) (y i)).HasFiniteSupport := by
  apply Filter.eventually_cofinite.mp
  filter_upwards [x.eventually, y.eventually] with i hx hy
  simpa only [not_not] using hp i (x i) hx (y i) hy

/-- Sum of local pairings on restricted products with orthogonal reference subgroups. -/
def sumPairing : (Πʳ i, [A i, U i]) →+ (Πʳ i, [B i, V i]) →+ C where
  toFun x :=
    { toFun := fun y ↦ ∑ᶠ i, p i (x i) (y i)
      map_zero' := by simp
      map_add' := fun y z ↦ by
        simp only [add_apply, map_add]
        exact finsum_add_distrib (hasFiniteSupport_pairing U V p hp x y)
          (hasFiniteSupport_pairing U V p hp x z) }
  map_zero' := by ext y; simp
  map_add' x z := by
    ext y
    simp only [add_apply, map_add, AddMonoidHom.add_apply]
    exact finsum_add_distrib (hasFiniteSupport_pairing U V p hp x y)
      (hasFiniteSupport_pairing U V p hp z y)

/-- The restricted-product pairing is the finite sum of the local values. -/
theorem sumPairing_apply (x : Πʳ i, [A i, U i]) (y : Πʳ i, [B i, V i]) :
    sumPairing U V p hp x y = ∑ᶠ i, p i (x i) (y i) := (rfl)

/-- The sum pairing can be evaluated on any finite set outside which both coordinates
belong to the reference subgroups. -/
theorem sumPairing_eq_sum (x : Πʳ i, [A i, U i]) (y : Πʳ i, [B i, V i])
    (S : Finset ι) (hS : ∀ i ∉ S, x i ∈ U i ∧ y i ∈ V i) :
    sumPairing U V p hp x y = ∑ i ∈ S, p i (x i) (y i) := by
  rw [sumPairing_apply]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra h
  exact hi (hp i _ (hS i h).1 _ (hS i h).2)

section Single

variable [DecidableEq ι]

/-- Testing a sum pairing against a single supported coordinate recovers its local value. -/
@[simp]
theorem sumPairing_single_right (x : Πʳ i, [A i, U i]) (i : ι) (b : B i) :
    sumPairing U V p hp x (single V i b) = p i (x i) b := by
  rw [sumPairing_apply, finsum_eq_single _ i]
  · rw [single_eq_same]
  · intro j hj
    rw [single_eq_of_ne _ _ hj, map_zero]

/-- A single supported first argument recovers the local value as well. -/
@[simp]
theorem sumPairing_single_left (i : ι) (a : A i) (y : Πʳ i, [B i, V i]) :
    sumPairing U V p hp (single U i a) y = p i a (y i) := by
  rw [sumPairing_apply, finsum_eq_single _ i]
  · rw [single_eq_same]
  · intro j hj
    rw [single_eq_of_ne _ _ hj, map_zero, AddMonoidHom.zero_apply]

end Single

/-- Nondegeneracy in the first argument is preserved by the restricted-product sum. -/
theorem sumPairing_injective (hinj : ∀ i, Function.Injective (p i)) :
    Function.Injective (sumPairing U V p hp) := by
  classical
  intro x y h
  ext i
  apply hinj i
  ext b
  simpa only [sumPairing_single_right] using DFunLike.congr_fun h (single V i b)

/-- Nondegeneracy in the second argument is also preserved by the sum. -/
theorem sumPairing_flip_injective (hinj : ∀ i, Function.Injective (p i).flip) :
    Function.Injective (sumPairing U V p hp).flip := by
  classical
  intro x y h
  ext i
  apply hinj i
  ext a
  simpa only [AddMonoidHom.flip_apply, sumPairing_single_left] using
    DFunLike.congr_fun h (single U i a)

/-- Orthogonality to the full product of the reference subgroups is equivalent to local
orthogonality at every index. No perfection assumption is needed. -/
theorem sumPairing_structureMap_eq_zero_iff (x : Πʳ i, [A i, U i]) :
    (∀ y : ∀ i, V i, sumPairing U V p hp x
      (structureMap B (fun i ↦ (V i : Set (B i))) Filter.cofinite y) = 0) ↔
      ∀ i, ∀ b ∈ V i, p i (x i) b = 0 := by
  classical
  constructor
  · intro h i b hb
    let y : ∀ j, V j := Pi.single i ⟨b, hb⟩
    have hy : structureMap B (fun i ↦ (V i : Set (B i))) Filter.cofinite y =
        single V i b := by
      ext j
      by_cases hj : j = i
      · subst j; simp [y]
      · simp [y, Pi.single_eq_of_ne hj, single_eq_of_ne V b hj]
    simpa only [hy, sumPairing_single_right] using h y
  · intro h y
    rw [sumPairing_apply]
    exact finsum_eq_zero_of_forall_eq_zero fun i ↦ h i _ (y i).property

end RestrictedProduct

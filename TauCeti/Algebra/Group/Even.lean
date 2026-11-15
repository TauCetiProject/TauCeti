/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

/-!
# Squares and finite products

A unit square factor does not change whether an element is a square
(`IsUnit.isSquare_sq_mul_iff`).

If all but the last entries of two finite families agree modulo squares, agreement of their
products modulo squares determines the last entry. This is useful when prescribing the last
coefficient of a diagonal quadratic form from its determinant.
-/

public section

namespace TauCeti

/-- Agreement modulo squares of two products over `s`, and of all their factors except the one
at `j ∈ s`, forces agreement of the factors at `j`. -/
theorem isSquare_div_of_isSquare_prod_div_prod
    {G ι : Type*} [CommGroup G] {s : Finset ι} {a b : ι → G} {j : ι} (hj : j ∈ s)
    (h : ∀ i ∈ s, i ≠ j → IsSquare (a i / b i))
    (hp : IsSquare ((∏ i ∈ s, a i) / ∏ i ∈ s, b i)) :
    IsSquare (a j / b j) := by
  classical
  rw [← s.mul_prod_erase a hj, ← s.mul_prod_erase b hj, mul_div_mul_comm,
    ← Finset.prod_div_distrib] at hp
  simpa using hp.div (Finset.isSquare_prod _ fun i hi ↦
    h i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))

end TauCeti

/-- Multiplying by the square of a unit does not change whether an element is a square. -/
@[simp]
theorem IsUnit.isSquare_sq_mul_iff {M : Type*} [CommMonoid M] {u x : M} (hu : IsUnit u) :
    IsSquare (u ^ 2 * x) ↔ IsSquare x := by
  refine ⟨fun h ↦ ?_, fun ⟨r, hr⟩ ↦ ⟨u * r, by rw [hr, mul_mul_mul_comm, sq]⟩⟩
  have := (IsSquare.sq (↑hu.unit⁻¹ : M)).mul h
  rwa [← mul_assoc, ← mul_pow, hu.val_inv_mul, one_pow, one_mul] at this

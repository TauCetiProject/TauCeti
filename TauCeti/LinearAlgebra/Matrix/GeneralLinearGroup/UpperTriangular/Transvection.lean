/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# Upper transvections

This file records that an upper transvection belongs to the upper-triangular subgroup, and, over
any ring, to the upper-unitriangular subgroup. This lets upper transvections be used as elements
of the Borel subgroup `B` in the construction of the standard Tits system of `GLₙ₊₁`: they appear
when an element of `B` is factored as a product with a transvection at a simple root, and,
together with their conjugates by permutation matrices, in the proof that `B` and the permutation
matrices generate `GLₙ(k)`. As elements of the upper-unitriangular group they detect its centre.
-/

public section

open Matrix

namespace TauCeti

universe u v

variable {m : Type v} [Fintype m] [LinearOrder m] {R : Type u}

/-- A transvection `x_{ij}(c)` with `i < j` is upper triangular. -/
theorem transvectionUnit_mem_upperTriangularGroup [CommRing R] {i j : m} (hij : i < j) (c : R) :
    transvectionUnit hij.ne c ∈ upperTriangularGroup m R := by
  rw [UpperTriangularGroup.mem_iff, coe_transvectionUnit]
  exact Matrix.blockTriangular_transvection (le_of_lt hij) c

/-- A transvection `e_ij(c) = 1 + c Eᵢⱼ` with `i < j` is upper unitriangular. -/
theorem transvectionUnit_mem_upperUnitriangularGroup [Ring R] {i j : m} (hij : i < j) (c : R) :
    transvectionUnit hij.ne c ∈ upperUnitriangularGroup m R := by
  rw [UpperUnitriangularGroup.mem_iff, coe_transvectionUnit_eq_one_add_single,
    isUpperUnitriangular_iff]
  refine ⟨fun a b hba ↦ ?_, fun k ↦ ?_⟩
  · have hab : ¬ (i = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hij hba
    rw [Matrix.add_apply, Matrix.one_apply_ne hba.ne', Matrix.single_apply_of_ne (h := hab),
      add_zero]
  · rw [Matrix.add_apply, Matrix.one_apply_eq,
      Matrix.single_apply_of_ne
        (h := fun h : i = k ∧ j = k ↦ hij.ne (h.1.trans h.2.symm)), add_zero]

end TauCeti

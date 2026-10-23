/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.LowRank.One
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Generators

/-!
# The Spin group in dimension one

In dimension one the even Clifford algebra has dimension one over the base field. Thus every
even Clifford unit is a scalar unit. When the form represents a unit, scalar units belong to
Mathlib's Lipschitz group, so the even unitary carrier and the Spin carrier coincide in this
dimension.

The rank-one equality identifies `spinGroup` with the unitary group of the even Clifford algebra
inside Clifford units. The zero-dimensional case is different: its Lipschitz group is trivial.

The scalar description follows the standard Clifford algebra calculation; see H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

namespace CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- For a one-dimensional quadratic space representing a unit, every even Clifford unit lies in
Mathlib's Lipschitz group. -/
theorem mem_lipschitzGroup_of_mem_even_of_finrank_eq_one (Q : QuadraticForm K V)
    (hQ : ∃ v, IsUnit (Q v)) (hV : Module.finrank K V = 1) (x : (CliffordAlgebra Q)ˣ)
    (hx : (x : CliffordAlgebra Q) ∈ even Q) : x ∈ lipschitzGroup Q := by
  obtain ⟨a, rfl⟩ := exists_eq_unitsMap_algebraMap_of_mem_even_of_finrank_eq_one Q hV x hx
  exact unitsMap_algebraMap_mem_lipschitzGroup hQ a

/-- For a one-dimensional quadratic space representing a unit, the even unitary carrier lies in
the Lipschitz group. -/
theorem evenUnitaryGroup_le_lipschitzGroup_of_finrank_eq_one (Q : QuadraticForm K V)
    (hQ : ∃ v, IsUnit (Q v)) (hV : Module.finrank K V = 1) :
    evenUnitaryGroup Q ≤ lipschitzGroup Q := by
  intro x hx
  exact mem_lipschitzGroup_of_mem_even_of_finrank_eq_one Q hQ hV x
    (evenUnitaryGroup.mem_even Q hx)

/-- For a one-dimensional quadratic space representing a unit, the Spin group fills the even
unitary carrier inside Clifford units. -/
-- Not `@[simp]`: `range_spinGroup_toUnits` already simplifies the left-hand side.
theorem range_spinGroup_toUnits_eq_evenUnitaryGroup_of_finrank_eq_one
    (Q : QuadraticForm K V) (hQ : ∃ v, IsUnit (Q v))
    (hV : Module.finrank K V = 1) :
    (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range = evenUnitaryGroup Q := by
  rw [range_spinGroup_toUnits]
  exact inf_eq_right.mpr (evenUnitaryGroup_le_lipschitzGroup_of_finrank_eq_one Q hQ hV)

end CliffordAlgebra

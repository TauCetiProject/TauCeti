/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Generators

/-!
# The Spin group in dimension one

In dimension one the even Clifford algebra has dimension one over the base field. Thus every
even Clifford unit is a scalar unit. When the form represents a unit, scalar units belong to
Mathlib's Lipschitz group, so the even unitary carrier and the Spin carrier coincide in this
dimension.

This is the first low-rank case of the comparison between `spinGroup` and the unitary group of
the even Clifford algebra. The zero-dimensional case is different: its Lipschitz group is trivial.

The scalar description follows the standard Clifford algebra calculation; see H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

namespace CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]

/-- In dimension one, every even Clifford unit is a scalar unit of the Clifford algebra. -/
theorem exists_scalar_unit_of_mem_even_of_finrank_eq_one (Q : QuadraticForm K V)
    (hV : Module.finrank K V = 1) (x : (CliffordAlgebra Q)ˣ)
    (hx : (x : CliffordAlgebra Q) ∈ even Q) :
    ∃ a : Kˣ, x = Units.map (algebraMap K (CliffordAlgebra Q)) a := by
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; decide)
  have hdim : Module.finrank K (even Q) = 1 := by
    rw [finrank_even Q, hV]
    norm_num
  obtain ⟨a, ha⟩ :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdim).2
      (⟨(x : CliffordAlgebra Q), hx⟩ : even Q)
  have hcoe : algebraMap K (CliffordAlgebra Q) a = (x : CliffordAlgebra Q) :=
    congrArg (fun y : even Q => (y : CliffordAlgebra Q)) ha
  have ha0 : a ≠ 0 := by
    intro hzero
    apply x.ne_zero
    simpa [hzero] using hcoe.symm
  let au : Kˣ := (Ne.isUnit ha0).unit
  refine ⟨au, Units.ext ?_⟩
  simpa [au] using hcoe.symm

/-- For a one-dimensional quadratic space representing a unit, every even Clifford unit lies in
Mathlib's Lipschitz group. -/
theorem even_units_le_lipschitzGroup_of_finrank_eq_one (Q : QuadraticForm K V)
    (hQ : ∃ v, IsUnit (Q v)) (hV : Module.finrank K V = 1) (x : (CliffordAlgebra Q)ˣ)
    (hx : (x : CliffordAlgebra Q) ∈ even Q) : x ∈ lipschitzGroup Q := by
  obtain ⟨a, rfl⟩ := exists_scalar_unit_of_mem_even_of_finrank_eq_one Q hV x hx
  exact unitsMap_algebraMap_mem_lipschitzGroup hQ a

/-- In dimension one, the even unitary carrier lies in the Lipschitz group. -/
theorem evenUnitaryGroup_le_lipschitzGroup_of_finrank_eq_one (Q : QuadraticForm K V)
    (hQ : ∃ v, IsUnit (Q v)) (hV : Module.finrank K V = 1) :
    evenUnitaryGroup Q ≤ lipschitzGroup Q := by
  intro x hx
  exact even_units_le_lipschitzGroup_of_finrank_eq_one Q hQ hV x
    (evenUnitaryGroup.mem_even Q hx)

/-- In dimension one, the Spin group fills the even unitary carrier inside Clifford units. -/
theorem range_spinGroup_toUnits_eq_evenUnitaryGroup_of_finrank_eq_one
    (Q : QuadraticForm K V) (hQ : ∃ v, IsUnit (Q v))
    (hV : Module.finrank K V = 1) :
    (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range = evenUnitaryGroup Q := by
  rw [range_spinGroup_toUnits]
  exact inf_eq_right.mpr (evenUnitaryGroup_le_lipschitzGroup_of_finrank_eq_one Q hQ hV)

end CliffordAlgebra

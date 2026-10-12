/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Generators
import TauCeti.LinearAlgebra.CliffordAlgebra.LowRank.Two

/-!
# The Spin group in dimension two

In dimension two the odd part of a Clifford algebra is exactly the image of its generating space.
If the quadratic form represents a unit, multiply an even Clifford unit by the corresponding
invertible vector. The product is odd, hence is another vector; solving for the original unit
expresses it as a product of two Lipschitz generators. Consequently every even unitary Clifford
unit belongs to the Lipschitz group, and the even unitary carrier is exactly the Spin carrier.

The argument is the standard low-dimensional Clifford calculation; see H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.

## Main results

* `CliffordAlgebra.mem_lipschitzGroup_of_mem_even_of_finrank_eq_two`: every even Clifford unit is
  Lipschitz when the form represents a unit.
* `CliffordAlgebra.range_spinGroup_toUnits_eq_evenUnitaryGroup_of_finrank_eq_two`: the Spin image
  and even unitary carrier coincide.
-/

public section

open Module

namespace CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

/-- For a two-dimensional quadratic space representing a unit, every even Clifford unit lies in
Mathlib's Lipschitz group. -/
theorem mem_lipschitzGroup_of_mem_even_of_finrank_eq_two (Q : QuadraticForm K V)
    (hQ : ∃ v, IsUnit (Q v)) (hV : finrank K V = 2) (x : (CliffordAlgebra Q)ˣ)
    (hx : (x : CliffordAlgebra Q) ∈ even Q) : x ∈ lipschitzGroup Q := by
  obtain ⟨v, hv⟩ := hQ
  let _ : Invertible (Q v) := hv.invertible
  have hodd : ((x * unitι Q v : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 1 := by
    -- Expose the degree-zero characterization of `even` so graded multiplication sees the two
    -- factors, then normalize the unit coercions.
    change (x : CliffordAlgebra Q) ∈ evenOdd Q 0 at hx
    have hprod : (x : CliffordAlgebra Q) * ι Q v ∈ evenOdd Q 1 :=
      zero_add (1 : ZMod 2) ▸ SetLike.mul_mem_graded hx (ι_mem_evenOdd_one Q v)
    simpa only [Units.val_mul, coe_unitι] using hprod
  rw [← range_ι_eq_evenOdd_one_of_finrank_eq_two Q hV] at hodd
  obtain ⟨w, hw⟩ := hodd
  have hwQ : IsUnit (Q w) :=
    isUnit_of_isUnit_ι Q (hw ▸ (x * unitι Q v).isUnit)
  let _ : Invertible (Q w) := hwQ.invertible
  have hxw : x * unitι Q v = unitι Q w := by
    apply Units.ext
    simpa only [Units.val_mul, coe_unitι] using hw.symm
  have hx_eq : x = unitι Q w * (unitι Q v)⁻¹ :=
    eq_mul_inv_iff_mul_eq.mpr hxw
  rw [hx_eq]
  exact mul_mem (unitι_mem_lipschitzGroup w) (inv_mem (unitι_mem_lipschitzGroup v))

/-- For a two-dimensional quadratic space representing a unit, the even unitary carrier lies in
the Lipschitz group. -/
theorem evenUnitaryGroup_le_lipschitzGroup_of_finrank_eq_two (Q : QuadraticForm K V)
    (hQ : ∃ v, IsUnit (Q v)) (hV : finrank K V = 2) :
    evenUnitaryGroup Q ≤ lipschitzGroup Q := by
  intro x hx
  exact mem_lipschitzGroup_of_mem_even_of_finrank_eq_two Q hQ hV x
    (evenUnitaryGroup.mem_even Q hx)

/-- For a two-dimensional quadratic space representing a unit, the Spin group fills the even
unitary carrier inside Clifford units. -/
-- Not `@[simp]`: `range_spinGroup_toUnits` already simplifies the left-hand side.
theorem range_spinGroup_toUnits_eq_evenUnitaryGroup_of_finrank_eq_two
    (Q : QuadraticForm K V) (hQ : ∃ v, IsUnit (Q v)) (hV : finrank K V = 2) :
    (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range = evenUnitaryGroup Q := by
  rw [range_spinGroup_toUnits]
  exact inf_eq_right.mpr (evenUnitaryGroup_le_lipschitzGroup_of_finrank_eq_two Q hQ hV)

end CliffordAlgebra

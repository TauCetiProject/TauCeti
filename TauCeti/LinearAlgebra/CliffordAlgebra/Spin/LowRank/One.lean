/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.LowRank.One
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.LowRank
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Generators

/-!
# The Spin group in dimension one

In dimension one the even Clifford algebra has dimension one over the base field. Thus every
even Clifford unit is a scalar unit. When the form represents a unit, scalar units belong to
Mathlib's Lipschitz group, so the even unitary carrier and the Spin carrier coincide in this
dimension.

The rank-one equality identifies `spinGroup` with the unitary group of the even Clifford algebra
inside Clifford units. The zero-dimensional case is different: its Lipschitz group is trivial.

For a nondegenerate form, the special orthogonal group of a line is trivial, so the Spin action is
trivial and the Spin group is the kernel `{1, -1}` of its double cover. Thus `Spin(Q) = {±1}` is
cyclic of order two, and the double cover `Spin(Q) → SO(Q)` is the trivial two-sheeted cover of a
point.

## Main results

* `CliffordAlgebra.range_spinGroup_toUnits_eq_evenUnitaryGroup_of_finrank_eq_one`: Spin fills the
  even unitary carrier when the form represents a unit.
* `CliffordAlgebra.ker_spinToSpecialOrthogonal_eq_top_of_finrank_eq_one`: the Spin action on a
  line is trivial.
* `CliffordAlgebra.mem_spinGroup_iff_of_finrank_eq_one`: for a nondegenerate form, the Spin group
  consists of `1` and `-1`.
* `CliffordAlgebra.zmodTwoMulEquivSpinGroupOfFinrankEqOne`: for a nondegenerate form, the Spin
  group is `Multiplicative (ZMod 2)`, with the generator sent to `-1`.

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

section Kernel

variable [Invertible (2 : K)] (Q : QuadraticForm K V)

/-- In dimension one the Spin action is trivial: the special orthogonal group of a line is
trivial, so the whole Spin group is the kernel of its action. -/
theorem ker_spinToSpecialOrthogonal_eq_top_of_finrank_eq_one (hV : Module.finrank K V = 1) :
    MonoidHom.ker (spinToSpecialOrthogonal Q) = ⊤ := by
  have : Module.Finite K V := Module.finite_of_finrank_eq_succ hV
  have : Subsingleton (TauCeti.QuadraticMap.specialOrthogonalGroup Q) := by
    rw [QuadraticMap.specialOrthogonalGroup_eq_bot_of_finrank_le_one Q hV.le]
    infer_instance
  exact MonoidHom.ker_eq_top_iff.mpr (MonoidHom.ext fun _ ↦ Subsingleton.elim _ _)

/-- In dimension one the Spin group of a nondegenerate form is `{1, -1}`. -/
theorem spinGroup.eq_one_or_eq_negOne_of_finrank_eq_one [Nontrivial V] (hQ : Q.Nondegenerate)
    (hV : Module.finrank K V = 1) (x : spinGroup Q) :
    x = 1 ∨ x = spinGroup.negOne Q hQ.ne_zero := by
  have : Module.Finite K V := Module.finite_of_finrank_eq_succ hV
  refine (mem_ker_spinToSpecialOrthogonal_iff Q hQ x).mp ?_
  rw [ker_spinToSpecialOrthogonal_eq_top_of_finrank_eq_one Q hV]
  exact Subgroup.mem_top x

/-- In dimension one the Spin group of a nondegenerate form consists of exactly the Clifford
elements `1` and `-1`. -/
theorem mem_spinGroup_iff_of_finrank_eq_one (hQ : Q.Nondegenerate)
    (hV : Module.finrank K V = 1) {x : CliffordAlgebra Q} :
    x ∈ spinGroup Q ↔ x = 1 ∨ x = -1 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [hV]; exact one_pos)
  constructor
  · intro hx
    rcases spinGroup.eq_one_or_eq_negOne_of_finrank_eq_one Q hQ hV ⟨x, hx⟩ with h | h
    · exact .inl (congrArg Subtype.val h)
    · exact .inr (by simpa using congrArg Subtype.val h)
  · rintro (rfl | rfl)
    · exact (spinGroup Q).one_mem
    · exact neg_one_mem_spinGroup Q hQ.ne_zero

/-- In dimension one the Spin group of a nondegenerate form is cyclic of order two, generated by
`-1`: the inclusion of the Spin double cover is an isomorphism, since its projection lands in the
trivial special orthogonal group. -/
noncomputable def zmodTwoMulEquivSpinGroupOfFinrankEqOne (hQ : Q.Nondegenerate)
    (hV : Module.finrank K V = 1) :
    Multiplicative (ZMod 2) ≃* spinGroup Q :=
  have : Module.Finite K V := Module.finite_of_finrank_eq_succ hV
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [hV]; exact one_pos)
  (zmodTwoMulEquivKerSpinToSpecialOrthogonal Q hQ).trans <|
    (MulEquiv.subgroupCongr (ker_spinToSpecialOrthogonal_eq_top_of_finrank_eq_one Q hV)).trans
      Subgroup.topEquiv

/-- The rank-one cyclic equivalence sends the generator of `Multiplicative (ZMod 2)` to `-1`. -/
@[simp]
theorem zmodTwoMulEquivSpinGroupOfFinrankEqOne_apply_ofAdd_one [Nontrivial V]
    (hQ : Q.Nondegenerate)
    (hV : Module.finrank K V = 1) :
    zmodTwoMulEquivSpinGroupOfFinrankEqOne Q hQ hV (Multiplicative.ofAdd 1) =
      spinGroup.negOne Q hQ.ne_zero := by
  simp [zmodTwoMulEquivSpinGroupOfFinrankEqOne]

end Kernel

end CliffordAlgebra

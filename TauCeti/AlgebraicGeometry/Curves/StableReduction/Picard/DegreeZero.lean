/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.Rank
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-!
# The degree-zero numerical Picard group

The weighted Picard group of a numerical type is a finitely generated abelian group of rank one.
Its total-degree map is nonzero, so its kernel has rank zero and is finite. Thus the numerical
degree-zero classes are precisely the torsion classes. This is the finite group to which the
degree-zero part of the Picard group of a special fibre is compared in stable reduction.

The rank-one input is `NumericalType.finrank_pic`; the degree map and its value on a unit
multidegree are in `Picard.Basic`.
-/

public section

namespace TauCeti

namespace NumericalType

universe u

variable (T : NumericalType.{u})

/-- The numerical Picard classes of total degree zero. -/
abbrev degreeZero : Submodule ℤ T.Pic := LinearMap.ker T.degree

/-- A numerical Picard class has degree zero exactly when it belongs to the degree-zero
submodule. -/
@[simp]
lemma mem_degreeZero_iff (x : T.Pic) : x ∈ T.degreeZero ↔ T.degree x = 0 :=
  LinearMap.mem_ker

/-- The total-degree map of a numerical type has rank one: the class supported at any
component has nonzero degree. -/
theorem finrank_range_degree : Module.finrank ℤ (LinearMap.range T.degree) = 1 := by
  let i := Classical.choice T.componentNonempty
  let x : T.Pic := Submodule.Quotient.mk (Pi.single i 1)
  have hx : T.degree x ≠ 0 := by
    dsimp only [x]
    rw [T.degree_mk, T.totalDegree_apply]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.single_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, one_mul]
    exact mul_ne_zero (Int.natCast_pos.mpr (T.multiplicity i).pos).ne'
      (Int.natCast_pos.mpr (T.weight i).pos).ne'
  have hpos : 0 < Module.finrank ℤ (LinearMap.range T.degree) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨T.degree x, ⟨x, rfl⟩⟩, ?_⟩
    intro h
    exact hx (congrArg Subtype.val h)
  have hle : Module.finrank ℤ (LinearMap.range T.degree) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range T.degree)
  omega

/-- The kernel of total degree has rank zero. -/
theorem finrank_degreeZero : Module.finrank ℤ T.degreeZero = 0 := by
  have h := (LinearMap.ker T.degree).finrank_quotient_add_finrank
  rw [LinearEquiv.finrank_eq T.degree.quotKerEquivRange, T.finrank_range_degree,
    T.finrank_pic] at h
  simpa only [degreeZero] using (by omega : Module.finrank ℤ (LinearMap.ker T.degree) = 0)

/-- The degree-zero subgroup of the numerical Picard group is finite. -/
theorem finite_degreeZero : Finite T.degreeZero := by
  have htor : Module.IsTorsion ℤ T.degreeZero :=
    Module.finrank_eq_zero_iff_isTorsion.mp T.finrank_degreeZero
  exact Module.finite_of_fg_torsion T.degreeZero htor

/-- A numerical Picard class has degree zero if and only if it is torsion. In particular,
the degree-zero condition can be checked by an integral multiple of the class. -/
theorem degree_eq_zero_iff_exists_smul_eq_zero (x : T.Pic) :
    T.degree x = 0 ↔ ∃ n : ℤ, n ≠ 0 ∧ n • x = 0 := by
  constructor
  · intro hx
    have htor : Module.IsTorsion ℤ T.degreeZero :=
      Module.finrank_eq_zero_iff_isTorsion.mp T.finrank_degreeZero
    obtain ⟨n, hn⟩ := htor (x := ⟨x, hx⟩)
    exact ⟨n, nonZeroDivisors.coe_ne_zero n, congrArg Subtype.val hn⟩
  · rintro ⟨n, hn, hx⟩
    have h := congrArg T.degree hx
    simp only [map_smul, map_zero, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hn

end NumericalType

end TauCeti

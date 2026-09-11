/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Generation
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.ReflectionPair
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Rotation

/-!
# Path-connectedness of compact real Spin groups

For the positive-definite real Clifford form in dimension at least two, the identity path
component contains the scalar `-1` and every normalized reflection-pair lift. Every anisotropic
vector can be normalized without changing its reflection, so reflection-pair generation forces
the identity path component to be the whole Spin group.

## Main result

* `CliffordAlgebra.pathConnectedSpace_realCliffordSpinGroupZero_add_two` proves that every
  compact real Spin group of dimension at least two is path-connected.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Sections 2 and 6.
-/

public section

namespace CliffordAlgebra

open TauCeti

private theorem sqrt_norm_ne_zero_realCliffordForm_zero {n : ℕ} (v : Fin n → ℝ)
    [Invertible (realCliffordForm n 0 v)] :
    Real.sqrt (realCliffordForm n 0 v) ≠ 0 := by
  have hv0 : v ≠ 0 := by
    intro hv
    subst v
    exact (isUnit_of_invertible
      (realCliffordForm n 0 (0 : Fin n → ℝ))).ne_zero (by simp)
  have hvpos : 0 < realCliffordForm n 0 v :=
    posDef_realCliffordForm_zero n v hv0
  exact ne_of_gt (Real.sqrt_pos.2 hvpos)

private theorem normalized_norm_realCliffordForm_zero {n : ℕ} (v : Fin n → ℝ)
    [Invertible (realCliffordForm n 0 v)] :
    realCliffordForm n 0
        ((Real.sqrt (realCliffordForm n 0 v))⁻¹ • v) = 1 := by
  have hvpos : 0 < realCliffordForm n 0 v :=
    Real.sqrt_pos.mp <| lt_of_le_of_ne (Real.sqrt_nonneg _)
      (sqrt_norm_ne_zero_realCliffordForm_zero v).symm
  have hsqrt := sqrt_norm_ne_zero_realCliffordForm_zero v
  calc
    realCliffordForm n 0 ((Real.sqrt (realCliffordForm n 0 v))⁻¹ • v) =
        (Real.sqrt (realCliffordForm n 0 v))⁻¹ *
          (Real.sqrt (realCliffordForm n 0 v))⁻¹ * realCliffordForm n 0 v := by
      rw [QuadraticMap.map_smul]
      rfl
    _ = 1 := by
      field_simp
      simpa [pow_two] using (Real.sq_sqrt hvpos.le).symm

/-- The compact real Spin group is path-connected in every dimension at least two. -/
theorem pathConnectedSpace_realCliffordSpinGroupZero_add_two (n : ℕ) :
    PathConnectedSpace (realCliffordSpinGroupZero (n + 2)) := by
  let Q := realCliffordForm (n + 2) 0
  let H := Subgroup.pathComponentOne (spinGroup Q)
  have hH : H = ⊤ := by
    apply subgroup_eq_top_of_negOne_mem_of_reflection_pair_lift_mem Q
      (posDef_realCliffordForm_zero (n + 2)).anisotropic.nondegenerate H
    · exact mem_pathComponent_iff.mpr
        (joined_one_negOne_realCliffordSpinGroupZero_add_two n)
    · intro v w _ _
      let a := (Real.sqrt (Q v))⁻¹
      let b := (Real.sqrt (Q w))⁻¹
      have hva : a ≠ 0 :=
        inv_ne_zero (sqrt_norm_ne_zero_realCliffordForm_zero v)
      have hwb : b ≠ 0 :=
        inv_ne_zero (sqrt_norm_ne_zero_realCliffordForm_zero w)
      let _ : Invertible a := (isUnit_iff_ne_zero.mpr hva).invertible
      let _ : Invertible b := (isUnit_iff_ne_zero.mpr hwb).invertible
      have hv : Q (a • v) = 1 := normalized_norm_realCliffordForm_zero v
      have hw : Q (b • w) = 1 := normalized_norm_realCliffordForm_zero w
      let _ : Invertible (Q (a • v)) := hv.symm ▸ invertibleOne
      let _ : Invertible (Q (b • w)) := hw.symm ▸ invertibleOne
      let x := spinReflectionPair Q (a • v) (b • w) hv hw
      refine ⟨x, ?_, ?_⟩
      · exact mem_pathComponent_iff.mpr
          (joined_one_spinReflectionPair_realCliffordForm_zero
            (by omega) (a • v) (b • w) hv hw)
      · rw [coe_spinToSpecialOrthogonal_spinReflectionPair]
        simp only [Subgroup.coe_mul, QuadraticMap.coe_reflectionOrthogonal]
        have hvref : QuadraticMap.reflection Q (a • v) =
            QuadraticMap.reflection Q v := by
          convert QuadraticMap.reflection_smul_eq Q v a using 1
          congr 1
          exact Subsingleton.elim _ _
        have hwref : QuadraticMap.reflection Q (b • w) =
            QuadraticMap.reflection Q w := by
          convert QuadraticMap.reflection_smul_eq Q w b using 1
          congr 1
          exact Subsingleton.elim _ _
        rw [hvref, hwref]
  apply pathConnectedSpace_iff_eq.mpr
  refine ⟨1, ?_⟩
  simpa only [H, Subgroup.coe_pathComponentOne] using
    (Subgroup.coe_eq_univ.mpr hH)

end CliffordAlgebra

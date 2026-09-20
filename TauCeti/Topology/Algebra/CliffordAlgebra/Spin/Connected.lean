/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Generation
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.ReflectionPair
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Rotation
import TauCeti.LinearAlgebra.QuadraticForm.Real

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
      have hv0 : v ≠ 0 := (posDef_realCliffordForm_zero (n + 2)).anisotropic.eq_zero_iff.not.mp
        (isUnit_of_invertible (Q v)).ne_zero
      have hw0 : w ≠ 0 := (posDef_realCliffordForm_zero (n + 2)).anisotropic.eq_zero_iff.not.mp
        (isUnit_of_invertible (Q w)).ne_zero
      have hvpos : 0 < Q v := by
        simpa only [Q] using posDef_realCliffordForm_zero (n + 2) v hv0
      have hwpos : 0 < Q w := by
        simpa only [Q] using posDef_realCliffordForm_zero (n + 2) w hw0
      let a := (Real.sqrt (Q v))⁻¹
      let b := (Real.sqrt (Q w))⁻¹
      have hva : a ≠ 0 := by
        simpa only [a] using QuadraticMap.inv_sqrt_apply_ne_zero hvpos
      have hwb : b ≠ 0 := by
        simpa only [b] using QuadraticMap.inv_sqrt_apply_ne_zero hwpos
      let _ : Invertible a := (isUnit_iff_ne_zero.mpr hva).invertible
      let _ : Invertible b := (isUnit_iff_ne_zero.mpr hwb).invertible
      have hv : Q (a • v) = 1 := by
        simpa only [Q, a] using QuadraticMap.map_inv_sqrt_smul_eq_one hvpos
      have hw : Q (b • w) = 1 := by
        simpa only [Q, b] using QuadraticMap.map_inv_sqrt_smul_eq_one hwpos
      let _ : Invertible (Q (a • v)) := hv.symm ▸ invertibleOne
      let _ : Invertible (Q (b • w)) := hw.symm ▸ invertibleOne
      have reflection_smul_eq' (u : Fin (n + 2) → ℝ) (c : ℝ)
          [Invertible (Q u)] [Invertible c] [Invertible (Q (c • u))] :
          QuadraticMap.reflection Q (c • u) = QuadraticMap.reflection Q u := by
        -- `reflection_smul_eq` creates its own norm instance; these `Invertible` instances
        -- are propositionally equal, so align them through the subsingleton instance proof.
        convert QuadraticMap.reflection_smul_eq Q u c using 1
        congr 1
        exact Subsingleton.elim _ _
      let x := spinReflectionPair Q (a • v) (b • w) hv hw
      refine ⟨x, ?_, ?_⟩
      · exact mem_pathComponent_iff.mpr
          (joined_one_spinReflectionPair_realCliffordForm_zero
            (by omega) (a • v) (b • w) hv hw)
      · rw [coe_spinToSpecialOrthogonal_spinReflectionPair]
        simp only [Subgroup.coe_mul, QuadraticMap.coe_reflectionOrthogonal]
        have hvref := reflection_smul_eq' v a
        have hwref := reflection_smul_eq' w b
        rw [hvref, hwref]
  apply pathConnectedSpace_iff_eq.mpr
  refine ⟨1, ?_⟩
  simpa only [H, Subgroup.coe_pathComponentOne] using
    (Subgroup.coe_eq_univ.mpr hH)

end CliffordAlgebra

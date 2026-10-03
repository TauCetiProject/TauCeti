/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Closed
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Projection
public import TauCeti.Topology.Algebra.QuadraticForm.RealSpecialOrthogonal

/-!
# The real Spin projection on closed unit-group carriers

The compact real Spin group and its special-orthogonal target enter the closed-subgroup theorem as
subgroups of ambient unit groups. This module transports the usual Spin projection to exactly
those two range carriers and bundles it as a continuous homomorphism.

The source range is topologically isomorphic to the usual Spin group. Indeed, the inclusion into
the Clifford units is injective and continuous, and its inverse on the range is continuous because
the Spin group is compact and the unit group is Hausdorff. Composing that inverse with the Spin
action and the faithful special-orthogonal matrix representation gives the required carrier map.

The resulting homomorphism is onto in every dimension: the standard real Clifford form is positive
definite, so its Spin action surjects onto the special orthogonal group. Consequently, after the
closed carriers are given their Lie-group structures, automatic smoothness makes this map available
to the Lie functor without changing either carrier.

## Main results

* `TauCeti.CliffordAlgebra.realCliffordSpinContinuousMulEquivUnitsRange` identifies the usual
  compact real Spin group with the source range carrier as a topological group.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRange` is the continuous
  homomorphism between the closed real Spin and special-orthogonal carriers.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRange_apply_toUnits` computes it on
  the canonical representative of every Spin element.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRange_surjective` proves that the
  carrier homomorphism is onto.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

namespace TauCeti

namespace CliffordAlgebra

open _root_.CliffordAlgebra

noncomputable section

/-- The canonical inclusion of the real Spin group into the Clifford units is a topological
embedding. -/
theorem isEmbedding_realCliffordSpinToUnits (n : ℕ) :
    Topology.IsEmbedding
      (spinGroup.toUnits (Q := realCliffordForm n 0)) := by
  have hcontinuous : Continuous
      (spinGroup.toUnits (Q := realCliffordForm n 0)) := by
    apply Units.continuous_iff.mpr
    exact ⟨continuous_subtype_val, continuous_subtype_val.star⟩
  exact (hcontinuous.isClosedEmbedding
    (spinGroup.toUnits_injective (Q := realCliffordForm n 0))).isEmbedding

/-- The compact real Spin group is topologically isomorphic to its range in the Clifford units. -/
noncomputable def realCliffordSpinContinuousMulEquivUnitsRange (n : ℕ) :
    spinGroup (realCliffordForm n 0) ≃ₜ*
      MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0)) :=
  ContinuousMulEquiv.mk'
    ((isEmbedding_realCliffordSpinToUnits n).toHomeomorph)
    fun x y ↦ Subtype.ext (map_mul (spinGroup.toUnits (Q := realCliffordForm n 0)) x y)

/-- The topological equivalence with the range sends a Spin element to its canonical unit. -/
@[simp]
theorem realCliffordSpinContinuousMulEquivUnitsRange_apply
    (n : ℕ) (x : spinGroup (realCliffordForm n 0)) :
    realCliffordSpinContinuousMulEquivUnitsRange n x =
      ⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩ := by
  simp only [realCliffordSpinContinuousMulEquivUnitsRange]
  rfl

/-- The compact real Spin projection as a continuous homomorphism between the two closed range
carriers in the Clifford and matrix unit groups. -/
noncomputable def realCliffordSpinToSpecialOrthogonalRange (n : ℕ) :
    MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0)) →ₜ*
      MonoidHom.range
        (QuadraticMap.specialOrthogonalToGeneralLinear
          (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)) where
  toMonoidHom :=
    (QuadraticMap.specialOrthogonalToGeneralLinear
      (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)).rangeRestrict.comp
      ((spinToSpecialOrthogonal (realCliffordForm n 0)).comp
        (realCliffordSpinContinuousMulEquivUnitsRange n).symm.toMonoidHom)
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    have hprojection : Continuous
        ((QuadraticMap.specialOrthogonalToGeneralLinear
          (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)).comp
            (spinToSpecialOrthogonal (realCliffordForm n 0))) := by
      apply Continuous.of_coeHom_comp
      apply continuous_matrix
      intro i j
      simpa only [MonoidHom.comp_apply, Units.coeHom_apply,
        QuadraticMap.specialOrthogonalToGeneralLinear_apply,
        coe_spinToSpecialOrthogonal_apply, Function.comp_def] using
        (continuous_apply i).comp
          (continuous_spinVectorAction_apply
            (realCliffordForm n 0) (Pi.single j 1))
    exact hprojection.comp
      (realCliffordSpinContinuousMulEquivUnitsRange n).symm.continuous

/-- On the canonical range representative of a Spin element, the carrier homomorphism is the
usual Spin projection followed by the special-orthogonal matrix inclusion. -/
@[simp]
theorem realCliffordSpinToSpecialOrthogonalRange_apply_toUnits
    (n : ℕ) (x : spinGroup (realCliffordForm n 0)) :
    realCliffordSpinToSpecialOrthogonalRange n
        ⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩ =
      ⟨QuadraticMap.specialOrthogonalToGeneralLinear
          (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)
          (spinToSpecialOrthogonal (realCliffordForm n 0) x),
        ⟨spinToSpecialOrthogonal (realCliffordForm n 0) x, rfl⟩⟩ := by
  apply Subtype.ext
  change QuadraticMap.specialOrthogonalToGeneralLinear
      (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)
      (spinToSpecialOrthogonal (realCliffordForm n 0)
        ((realCliffordSpinContinuousMulEquivUnitsRange n).symm
          ⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩)) = _
  rw [show (⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩ :
      MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) =
        realCliffordSpinContinuousMulEquivUnitsRange n x by rfl]
  rw [(realCliffordSpinContinuousMulEquivUnitsRange n).symm_apply_apply]

/-- The continuous homomorphism between the closed real Spin and special-orthogonal carriers is
surjective. -/
theorem realCliffordSpinToSpecialOrthogonalRange_surjective (n : ℕ) :
    Function.Surjective (realCliffordSpinToSpecialOrthogonalRange n) := by
  rintro ⟨g, y, rfl⟩
  obtain ⟨x, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm n 0) (posDef_realCliffordForm_zero n) y
  exact ⟨⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩,
    realCliffordSpinToSpecialOrthogonalRange_apply_toUnits n x⟩

end

end CliffordAlgebra

end TauCeti

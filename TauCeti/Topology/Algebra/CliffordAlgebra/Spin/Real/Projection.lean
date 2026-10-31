/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Closed
public import Mathlib.Topology.Covering.Basic
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
import Mathlib.Topology.Covering.Quotient

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

In positive dimension the carrier homomorphism is again the Spin double cover: its kernel consists
of the units `1` and `-1`, and it is a covering map. The source carrier is compact and the target
is Hausdorff, so the surjection is a quotient map with finite kernel. This transports the compact
real Spin covering to the unit-group carriers that serve as frame structure groups.

## Main results

* `TauCeti.CliffordAlgebra.realCliffordSpinContinuousMulEquivUnitsRange` identifies the usual
  compact real Spin group with the source range carrier as a topological group.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRange` is the continuous
  homomorphism between the closed real Spin and special-orthogonal carriers.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRange_apply` computes it on an
  arbitrary source carrier, and `realCliffordSpinToSpecialOrthogonalRange_apply_toUnits`
  specializes the formula to the canonical representative of a Spin element.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRange_surjective` proves that the
  carrier homomorphism is onto.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRange_eq_one_iff` identifies its
  kernel with the units `1` and `-1`.
* `TauCeti.CliffordAlgebra.isCoveringMap_realCliffordSpinToSpecialOrthogonalRange` proves that it
  is a covering map in positive dimension.

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

private def realCliffordSpinToUnitsContinuousMonoidHom (n : ℕ) :
    spinGroup (realCliffordForm n 0) →ₜ* (CliffordAlgebra (realCliffordForm n 0))ˣ :=
  ⟨spinGroup.toUnits, (isEmbedding_realCliffordSpinToUnits n).continuous⟩

private theorem isEmbedding_realCliffordSpinToUnitsContinuousMonoidHom (n : ℕ) :
    Topology.IsEmbedding (realCliffordSpinToUnitsContinuousMonoidHom n) := by
  -- The bundled homomorphism has `spinGroup.toUnits` as its forward map definitionally.
  change Topology.IsEmbedding (spinGroup.toUnits (Q := realCliffordForm n 0))
  exact isEmbedding_realCliffordSpinToUnits n

/-- The compact real Spin group is topologically isomorphic to its range in the Clifford units. -/
noncomputable def realCliffordSpinContinuousMulEquivUnitsRange (n : ℕ) :
    spinGroup (realCliffordForm n 0) ≃ₜ*
      MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0)) :=
  (realCliffordSpinToUnitsContinuousMonoidHom n).equivRangeOfIsEmbedding
    (isEmbedding_realCliffordSpinToUnitsContinuousMonoidHom n)

/-- The topological equivalence with the range sends a Spin element to its canonical unit. -/
@[simp]
theorem realCliffordSpinContinuousMulEquivUnitsRange_apply
    (n : ℕ) (x : spinGroup (realCliffordForm n 0)) :
    realCliffordSpinContinuousMulEquivUnitsRange n x =
      ⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩ := by
  -- Expose the specialized range equivalence so its generic forward-map theorem applies.
  change (realCliffordSpinToUnitsContinuousMonoidHom n).equivRangeOfIsEmbedding
    (isEmbedding_realCliffordSpinToUnitsContinuousMonoidHom n) x = _
  exact (realCliffordSpinToUnitsContinuousMonoidHom n).equivRangeOfIsEmbedding_apply
    (isEmbedding_realCliffordSpinToUnitsContinuousMonoidHom n) x

/-- The inverse topological equivalence sends a canonical range representative back to its Spin
element. -/
@[simp]
theorem realCliffordSpinContinuousMulEquivUnitsRange_symm_apply
    (n : ℕ) (x : spinGroup (realCliffordForm n 0)) :
    (realCliffordSpinContinuousMulEquivUnitsRange n).symm
        ⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩ = x := by
  rw [← realCliffordSpinContinuousMulEquivUnitsRange_apply]
  exact (realCliffordSpinContinuousMulEquivUnitsRange n).symm_apply_apply x

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
      classical
      have h := (QuadraticMap.isEmbedding_specialOrthogonalToGeneralLinear
          (realCliffordForm n 0)).continuous.comp
        (continuous_spinToSpecialOrthogonal_pi (realCliffordForm n 0))
      -- The continuity theorem is elaborated with `Classical.decEq`, whereas this concrete
      -- `Fin`-indexed target uses its canonical decidable-equality instance. The two resulting
      -- coordinate inclusions are propositionally equal because decidable equality is subsingleton.
      have hdec : Classical.decEq (Fin n) = instDecidableEqFin n := Subsingleton.elim _ _
      change Continuous (fun x ↦
        @QuadraticMap.specialOrthogonalToGeneralLinear ℝ inferInstance (Fin n) inferInstance
          (Classical.decEq (Fin n)) ℝ inferInstance inferInstance (realCliffordForm n 0)
          (spinToSpecialOrthogonal (realCliffordForm n 0) x)) at h
      rw [hdec] at h
      change Continuous (fun x ↦
        @QuadraticMap.specialOrthogonalToGeneralLinear ℝ inferInstance (Fin n) inferInstance
          (instDecidableEqFin n) ℝ inferInstance inferInstance (realCliffordForm n 0)
          (spinToSpecialOrthogonal (realCliffordForm n 0) x))
      exact h
    exact hprojection.comp
      (realCliffordSpinContinuousMulEquivUnitsRange n).symm.continuous

/-- The carrier homomorphism applies the usual Spin projection to the source representative
selected by the inverse range equivalence. -/
@[simp]
theorem realCliffordSpinToSpecialOrthogonalRange_apply
    (n : ℕ) (x : MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) :
    realCliffordSpinToSpecialOrthogonalRange n x =
      ⟨QuadraticMap.specialOrthogonalToGeneralLinear
          (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)
          (spinToSpecialOrthogonal (realCliffordForm n 0)
            ((realCliffordSpinContinuousMulEquivUnitsRange n).symm x)),
        ⟨spinToSpecialOrthogonal (realCliffordForm n 0)
            ((realCliffordSpinContinuousMulEquivUnitsRange n).symm x), rfl⟩⟩ := by
  apply Subtype.ext
  rfl

/-- On the canonical range representative of a Spin element, the carrier homomorphism is the
usual Spin projection followed by the special-orthogonal matrix inclusion. -/
theorem realCliffordSpinToSpecialOrthogonalRange_apply_toUnits
    (n : ℕ) (x : spinGroup (realCliffordForm n 0)) :
    realCliffordSpinToSpecialOrthogonalRange n
        ⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩ =
      ⟨QuadraticMap.specialOrthogonalToGeneralLinear
          (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)
          (spinToSpecialOrthogonal (realCliffordForm n 0) x),
        ⟨spinToSpecialOrthogonal (realCliffordForm n 0) x, rfl⟩⟩ := by
  rw [realCliffordSpinToSpecialOrthogonalRange_apply,
    realCliffordSpinContinuousMulEquivUnitsRange_symm_apply]

/-- The continuous homomorphism between the closed real Spin and special-orthogonal carriers is
surjective. -/
theorem realCliffordSpinToSpecialOrthogonalRange_surjective (n : ℕ) :
    Function.Surjective (realCliffordSpinToSpecialOrthogonalRange n) := by
  rintro ⟨g, y, rfl⟩
  obtain ⟨x, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm n 0) (posDef_realCliffordForm_zero n) y
  exact ⟨⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩,
    realCliffordSpinToSpecialOrthogonalRange_apply_toUnits n x⟩

/-- In positive dimension, a point of the Spin carrier lies over the identity exactly when it is
the unit `1` or the unit `-1`. -/
theorem realCliffordSpinToSpecialOrthogonalRange_eq_one_iff (n : ℕ) [NeZero n]
    (x : MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) :
    realCliffordSpinToSpecialOrthogonalRange n x = 1 ↔
      (x : (CliffordAlgebra (realCliffordForm n 0))ˣ) = 1 ∨
        (x : (CliffordAlgebra (realCliffordForm n 0))ˣ) = -1 := by
  obtain ⟨_, y, rfl⟩ := x
  have : Nontrivial (Fin (n + 0) → ℝ) := inferInstanceAs (Nontrivial (Fin n → ℝ))
  rw [realCliffordSpinToSpecialOrthogonalRange_apply_toUnits, Subtype.ext_iff,
    OneMemClass.coe_one,
    map_eq_one_iff _ (QuadraticMap.specialOrthogonalToGeneralLinear_injective _),
    ← MonoidHom.mem_ker,
    mem_ker_spinToSpecialOrthogonal_iff _ (nondegenerate_realCliffordForm n 0)]
  refine or_congr ?_ ?_
  · rw [← map_one spinGroup.toUnits, spinGroup.toUnits_injective.eq_iff]
  · rw [Subtype.ext_iff, spinGroup.coe_negOne, Units.ext_iff, spinGroup.val_toUnits_apply,
      Units.val_neg, Units.val_one]

/-- In positive dimension, the projection between the closed real Spin and special-orthogonal
carriers is a covering map. -/
theorem isCoveringMap_realCliffordSpinToSpecialOrthogonalRange (n : ℕ) [NeZero n] :
    IsCoveringMap (realCliffordSpinToSpecialOrthogonalRange n) := by
  let f := realCliffordSpinToSpecialOrthogonalRange n
  have : CompactSpace (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) :=
    (realCliffordSpinContinuousMulEquivUnitsRange n).toHomeomorph.compactSpace
  have hquot : Topology.IsQuotientMap f :=
    .of_surjective_continuous (realCliffordSpinToSpecialOrthogonalRange_surjective n) f.continuous
  have hfin : (SetLike.coe f.toMonoidHom.ker).Finite := by
    refine (Set.Finite.preimage Subtype.val_injective.injOn (Set.toFinite {1, -1})).subset ?_
    intro x hx
    simpa using (realCliffordSpinToSpecialOrthogonalRange_eq_one_iff n x).mp hx
  exact (hquot.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
    (f := f.toMonoidHom) hfin.isDiscrete).isCoveringMap

end

end CliffordAlgebra

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Closed
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.UnitsRange
public import Mathlib.Topology.Covering.Basic
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Covering

/-!
# The real Spin projection on closed unit-group carriers

The compact real Spin group and its special-orthogonal target enter the closed-subgroup theorem as
subgroups of ambient unit groups. This module specializes the general unit-range constructions from
`TauCeti.Topology.Algebra.CliffordAlgebra.Spin.UnitsRange` to the positive-definite real Clifford
form `realCliffordForm n 0` and records surjectivity and the covering-map property on those range
carriers.

The resulting homomorphism is onto in every dimension: the standard real Clifford form is positive
definite, so its Spin action surjects onto the special orthogonal group. Consequently, after the
closed carriers are given their Lie-group structures, automatic smoothness makes this map available
to the Lie functor without changing either carrier.

The carrier homomorphism is a covering map in every dimension. In dimension zero both carriers
are points and the covering is trivial (one sheet); its kernel consists of the unit `1` only. In
positive dimension it is again the Spin double cover: its kernel consists of the units `1` and
`-1`, and the covering is the compact real Spin covering
`CliffordAlgebra.isCoveringMap_realCliffordSpinProjectionZero`, transported along the
homeomorphisms of `Spin(n)` and `SO(n)` with the unit-group carriers that serve as frame structure
groups.

## Main results

* `TauCeti.CliffordAlgebra.realCliffordSpinContinuousMulEquivUnitsRange` specializes
  `CliffordAlgebra.spinGroupContinuousMulEquivUnitsRange` to identify the compact real Spin group
  with its unit-range carrier as a topological group.
* `TauCeti.CliffordAlgebra.realCliffordSpecialOrthogonalContinuousMulEquivRange` specializes
  `QuadraticMap.specialOrthogonalContinuousMulEquivRange` to identify the compact special
  orthogonal group `SO(n)` with its matrix-range carrier in `GL(n, ℝ)`.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRange` specializes
  `CliffordAlgebra.spinToSpecialOrthogonalUnitsRange` to the closed real Spin and
  special-orthogonal carriers.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRange_apply` computes it on an
  arbitrary source carrier, and `realCliffordSpinToSpecialOrthogonalRange_apply_toUnits`
  specializes the formula to the canonical representative of a Spin element.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRange_surjective` proves that the
  carrier homomorphism is onto.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRange_eq_one_iff` characterizes the
  kernel as the Spin-carrier points equal to the unit `1` or `-1` (`{1, -1}` in positive dimension,
  `{1}` in dimension zero).
* `TauCeti.CliffordAlgebra.isCoveringMap_realCliffordSpinToSpecialOrthogonalRange` proves that it
  is a covering map.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

namespace TauCeti

namespace CliffordAlgebra

open _root_.CliffordAlgebra

noncomputable section

/-- The compact real Spin group is topologically isomorphic to its range in the Clifford units. -/
noncomputable def realCliffordSpinContinuousMulEquivUnitsRange (n : ℕ) :
    spinGroup (realCliffordForm n 0) ≃ₜ*
      MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0)) :=
  spinGroupContinuousMulEquivUnitsRange (realCliffordForm n 0)

/-- The topological equivalence with the range sends a Spin element to its canonical unit. -/
@[simp]
theorem realCliffordSpinContinuousMulEquivUnitsRange_apply
    (n : ℕ) (x : spinGroup (realCliffordForm n 0)) :
    realCliffordSpinContinuousMulEquivUnitsRange n x =
      ⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩ :=
  spinGroupContinuousMulEquivUnitsRange_apply (realCliffordForm n 0) x

/-- The inverse topological equivalence sends a canonical range representative back to its Spin
element. -/
@[simp]
theorem realCliffordSpinContinuousMulEquivUnitsRange_symm_apply
    (n : ℕ) (x : spinGroup (realCliffordForm n 0)) :
    (realCliffordSpinContinuousMulEquivUnitsRange n).symm
        ⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩ = x :=
  spinGroupContinuousMulEquivUnitsRange_symm_apply (realCliffordForm n 0) x

/-- The coordinate special orthogonal group `SO(n)` is topologically isomorphic to its range in
`GL(n, ℝ)`. -/
def realCliffordSpecialOrthogonalContinuousMulEquivRange (n : ℕ) :
    QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0) ≃ₜ*
      MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)) :=
  (show QuadraticForm ℝ (Fin n → ℝ) from
    realCliffordForm n 0).specialOrthogonalContinuousMulEquivRange

/-- The topological equivalence with the range sends an element of `SO(n)` to its matrix. -/
@[simp]
theorem realCliffordSpecialOrthogonalContinuousMulEquivRange_apply (n : ℕ)
    (g : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) :
    realCliffordSpecialOrthogonalContinuousMulEquivRange n g =
      ⟨QuadraticMap.specialOrthogonalToGeneralLinear
        (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0) g, ⟨g, rfl⟩⟩ :=
  QuadraticMap.specialOrthogonalContinuousMulEquivRange_apply
    (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0) g

/-- The inverse topological equivalence sends the matrix of an element of `SO(n)` back to it. -/
@[simp]
theorem realCliffordSpecialOrthogonalContinuousMulEquivRange_symm_apply (n : ℕ)
    (g : QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) :
    (realCliffordSpecialOrthogonalContinuousMulEquivRange n).symm
        ⟨QuadraticMap.specialOrthogonalToGeneralLinear
          (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0) g, ⟨g, rfl⟩⟩ = g :=
  QuadraticMap.specialOrthogonalContinuousMulEquivRange_symm_apply
    (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0) g

/-- The compact real Spin projection as a continuous homomorphism between the two closed range
carriers in the Clifford and matrix unit groups. -/
noncomputable def realCliffordSpinToSpecialOrthogonalRange (n : ℕ) :
    MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0)) →ₜ*
      MonoidHom.range
        (QuadraticMap.specialOrthogonalToGeneralLinear
          (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)) :=
  spinToSpecialOrthogonalUnitsRange (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)

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
  rw [realCliffordSpinToSpecialOrthogonalRange, spinToSpecialOrthogonalUnitsRange_apply,
    QuadraticMap.specialOrthogonalContinuousMulEquivRange_apply]
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

/-- A point of the Spin carrier lies over the identity exactly when it is the unit `1` or the
unit `-1`. -/
theorem realCliffordSpinToSpecialOrthogonalRange_eq_one_iff (n : ℕ)
    (x : MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) :
    realCliffordSpinToSpecialOrthogonalRange n x = 1 ↔
      (x : (CliffordAlgebra (realCliffordForm n 0))ˣ) = 1 ∨
        (x : (CliffordAlgebra (realCliffordForm n 0))ˣ) = -1 :=
  spinToSpecialOrthogonalUnitsRange_eq_one_iff
    (show QuadraticForm ℝ (Fin n → ℝ) from realCliffordForm n 0)
    (nondegenerate_realCliffordForm n 0) x

/-- The projection between the closed real Spin and special-orthogonal carriers is a covering
map. -/
theorem isCoveringMap_realCliffordSpinToSpecialOrthogonalRange (n : ℕ) :
    IsCoveringMap (realCliffordSpinToSpecialOrthogonalRange n) := by
  obtain rfl | hn := n.eq_zero_or_pos
  · -- In dimension zero both carriers are points.
    -- `realCliffordForm 0 0` lives on `Fin (0 + 0) → ℝ`, which is `Fin 0 → ℝ` by definition.
    have : Subsingleton (Fin (0 + 0) → ℝ) := inferInstanceAs (Subsingleton (Fin 0 → ℝ))
    have hX : Subsingleton (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm 0 0))) :=
      (Set.subsingleton_coe _).mpr (MonoidHom.subsingleton_coe_range _)
    have : Subsingleton (MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (realCliffordForm 0 0))) :=
      (realCliffordSpinToSpecialOrthogonalRange_surjective 0).subsingleton
    exact .of_discreteTopology _
  have : NeZero n := ⟨hn.ne'⟩
  have h : ⇑(realCliffordSpinToSpecialOrthogonalRange n) =
      realCliffordSpecialOrthogonalContinuousMulEquivRange n ∘
        realCliffordSpinProjectionZero n ∘
        (realCliffordSpinContinuousMulEquivUnitsRange n).symm := by
    funext x
    simp [realCliffordSpinProjectionZero_apply]
  rw [h]
  exact ((isCoveringMap_realCliffordSpinProjectionZero n).homeomorph_comp
    (realCliffordSpecialOrthogonalContinuousMulEquivRange n).toHomeomorph).comp_homeomorph
      (realCliffordSpinContinuousMulEquivUnitsRange n).symm.toHomeomorph

end

end CliffordAlgebra

end TauCeti

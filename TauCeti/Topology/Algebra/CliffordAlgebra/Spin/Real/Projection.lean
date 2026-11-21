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
# Surjectivity and covering property of the real Spin projection on unit-group carriers

The compact real Spin group and its special-orthogonal target enter the closed-subgroup theorem as
subgroups of ambient unit groups, connected by the general range-carrier projection
`CliffordAlgebra.spinToSpecialOrthogonalUnitsRange` from
`TauCeti.Topology.Algebra.CliffordAlgebra.Spin.UnitsRange`. For the positive-definite real Clifford
form `realCliffordForm n 0`, this module records surjectivity and the covering-map property on those
range carriers.

The resulting homomorphism is onto in every dimension: the standard real Clifford form is positive
definite, so its Spin action surjects onto the special orthogonal group. Consequently, after the
closed carriers are given their Lie-group structures, automatic smoothness makes this map available
to the Lie functor without changing either carrier.

The carrier homomorphism is a covering map in every dimension. In dimension zero both carriers
are points and the covering is trivial (one sheet); its kernel consists of the unit `1` only. In
positive dimension it is again the Spin double cover: its kernel consists of the units `1` and
`-1` (by `CliffordAlgebra.spinToSpecialOrthogonalUnitsRange_eq_one_iff`), and the covering is the
compact real Spin covering `CliffordAlgebra.isCoveringMap_realCliffordSpinProjectionZero`,
transported along the homeomorphisms `CliffordAlgebra.spinGroupContinuousMulEquivUnitsRange` and
`QuadraticMap.specialOrthogonalContinuousMulEquivRange` of `Spin(n)` and `SO(n)` with the
unit-group carriers that serve as frame structure groups.

## Main results

* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRange_surjective` proves that the
  carrier homomorphism is onto.
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

/-- The continuous homomorphism between the closed real Spin and special-orthogonal carriers is
surjective. -/
theorem realCliffordSpinToSpecialOrthogonalRange_surjective (n : ℕ) :
    Function.Surjective (spinToSpecialOrthogonalUnitsRange (realCliffordFormZero n)) := by
  rintro ⟨g, y, rfl⟩
  obtain ⟨x, rfl⟩ := spinToSpecialOrthogonal_surjective_of_posDef
    (realCliffordForm n 0) (posDef_realCliffordForm_zero n) y
  exact ⟨⟨spinGroup.toUnits x, ⟨x, rfl⟩⟩, by
    rw [spinToSpecialOrthogonalUnitsRange_apply_toUnits,
      QuadraticMap.specialOrthogonalContinuousMulEquivRange_apply]⟩

/-- The projection between the closed real Spin and special-orthogonal carriers is a covering
map. -/
theorem isCoveringMap_realCliffordSpinToSpecialOrthogonalRange (n : ℕ) :
    IsCoveringMap (spinToSpecialOrthogonalUnitsRange (realCliffordFormZero n)) := by
  obtain rfl | hn := n.eq_zero_or_pos
  · -- In dimension zero both carriers are points.
    -- `realCliffordForm 0 0` lives on `Fin (0 + 0) → ℝ`, which is `Fin 0 → ℝ` by definition.
    have : Subsingleton (Fin (0 + 0) → ℝ) := inferInstanceAs (Subsingleton (Fin 0 → ℝ))
    have hX : Subsingleton (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm 0 0))) :=
      (Set.subsingleton_coe _).mpr (MonoidHom.subsingleton_coe_range _)
    have : Subsingleton (MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (realCliffordFormZero 0))) :=
      (realCliffordSpinToSpecialOrthogonalRange_surjective 0).subsingleton
    exact .of_discreteTopology _
  have : NeZero n := ⟨hn.ne'⟩
  have h : ⇑(spinToSpecialOrthogonalUnitsRange (realCliffordFormZero n)) =
      (realCliffordFormZero n).specialOrthogonalContinuousMulEquivRange ∘
        realCliffordSpinProjectionZero n ∘
        (spinGroupContinuousMulEquivUnitsRange (realCliffordForm n 0)).symm := by
    funext x
    simp [realCliffordSpinProjectionZero_apply]
  rw [h]
  exact ((isCoveringMap_realCliffordSpinProjectionZero n).homeomorph_comp
    (realCliffordFormZero n).specialOrthogonalContinuousMulEquivRange.toHomeomorph).comp_homeomorph
      (spinGroupContinuousMulEquivUnitsRange (realCliffordForm n 0)).symm.toHomeomorph

end

end CliffordAlgebra

end TauCeti

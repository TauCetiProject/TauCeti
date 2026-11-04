/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Covering

/-!
# Smooth evenly covered neighborhoods for the compact Spin projection

The compact real Spin projection on the closed units-range Lie-group carriers is a smooth
covering in positive dimension. Each rotation has a single evenly covered neighborhood on
which every sheet is a smooth local section. The sheets are labeled by the actual fiber over
the chosen rotation, and each section passes through its labeling point. These are the local
lifts used for smooth transitions of spin bundles.

The topological covering is
`TauCeti.CliffordAlgebra.isCoveringMap_realCliffordSpinToSpecialOrthogonalRange`;
local smooth invertibility is
`TauCeti.CliffordAlgebra.isLocalDiffeomorph_realCliffordSpinToSpecialOrthogonalSmoothRange`.
We keep their native units-range carriers and select the matrix operator topology explicitly.
At this Mathlib pin, `PiLp.pseudoMetricSpaceToPi` preserves the product uniformity, so the
operator-induced matrix topology and the entrywise topology are definitionally equal.
Consequently their identity homeomorphism, also on units and the SO range, is
`Homeomorph.refl`; no new topology or smooth structure is introduced.

The positive-dimensional statement includes rank one. Native Spin in rank zero is trivial;
the geometric two-element rank-zero group is a separate construction.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

open Manifold
open scoped ContDiff Manifold Matrix.Norms.Operator

noncomputable section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace

local notation "SpinUnitsRange(" n ")" =>
  MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))

local notation "SpecialOrthogonalUnitsRange(" n ")" =>
  MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
    (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ)))

local notation "SpinLieModel(" n ")" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0))) (SpinUnitsRange(n)))

local notation "SpecialOrthogonalLieModel(" n ")" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) (SpecialOrthogonalUnitsRange(n)))

/-- Every rotation has an evenly covered neighborhood whose sections are all smooth. Labeling
by the actual fiber makes each section pass through its prescribed Spin lift at the center. -/
theorem exists_realCliffordSpinSmoothCoveringTrivialization (n : ℕ) [NeZero n]
    (y : SpecialOrthogonalUnitsRange(n)) :
    ∃ t : Bundle.Trivialization
        ((realCliffordSpinToSpecialOrthogonalSmoothRange n) ⁻¹' {y})
        (realCliffordSpinToSpecialOrthogonalSmoothRange n),
      y ∈ t.baseSet ∧
      (∀ a : (realCliffordSpinToSpecialOrthogonalSmoothRange n) ⁻¹' {y},
        t.toOpenPartialHomeomorph.symm (y, a) = a) ∧
      ∀ a : (realCliffordSpinToSpecialOrthogonalSmoothRange n) ⁻¹' {y},
        ContMDiffOn 𝓘(ℝ, SpecialOrthogonalLieModel(n)) 𝓘(ℝ, SpinLieModel(n)) ∞
          (fun z ↦ t.toOpenPartialHomeomorph.symm (z, a)) t.baseSet := by
  have hmap : ⇑(realCliffordSpinToSpecialOrthogonalSmoothRange n) =
      ⇑(realCliffordSpinToSpecialOrthogonalRange n) := by
    funext x
    exact realCliffordSpinToSpecialOrthogonalSmoothRange_apply n x
  have hcover : IsCoveringMap (realCliffordSpinToSpecialOrthogonalSmoothRange n) := by
    rw [hmap]
    -- The operator norm preserves the product topology, including on units and subgroups.
    exact isCoveringMap_realCliffordSpinToSpecialOrthogonalRange n
  have hsurj : Function.Surjective (realCliffordSpinToSpecialOrthogonalSmoothRange n) := by
    rw [hmap]
    exact realCliffordSpinToSpecialOrthogonalRange_surjective n
  exact hcover.exists_trivialization_contMDiffOn_symm
    (isLocalDiffeomorph_realCliffordSpinToSpecialOrthogonalSmoothRange n) (hsurj y)

end TauCeti.CliffordAlgebra

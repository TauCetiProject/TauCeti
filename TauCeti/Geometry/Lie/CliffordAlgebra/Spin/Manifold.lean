/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Differential
public import TauCeti.Geometry.Manifold.Instances.Comap

/-!
# The native compact Spin group as a Lie group

The compact Spin group already has an embedded Lie-group realization in Clifford units.
Here its charts are pulled back to the original Clifford subtype along
`realCliffordSpinContinuousMulEquivUnitsRange`. This keeps the original topology and group
operations and lets constructions on native Spin quotients use the embedded smooth structure.

The comparison is a diffeomorphism, not just an abstract group isomorphism; multiplication
and inversion on the native carrier are smooth.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

noncomputable section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra Manifold
open scoped Manifold ContDiff

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace

/-- The model space of compact Spin, given by the Lie algebra of its embedded units range. -/
abbrev realSpinLieModel (n : ℕ) :=
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0)))
    (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))))

/-- The charts on native compact Spin pulled back from its embedded units range. -/
instance instChartedSpaceRealSpin (n : ℕ) :
    ChartedSpace (realSpinLieModel n) (spinGroup (realCliffordForm n 0)) :=
  (realCliffordSpinContinuousMulEquivUnitsRange n).toHomeomorph.isLocalHomeomorph.chartedSpaceComap

/-- The native compact Spin carrier is smooth for the pulled-back charts. -/
instance instIsManifoldRealSpin (n : ℕ) :
    IsManifold 𝓘(ℝ, realSpinLieModel n) ∞ (spinGroup (realCliffordForm n 0)) :=
  IsLocalHomeomorph.isManifold_chartedSpaceComap
    (realCliffordSpinContinuousMulEquivUnitsRange n).toHomeomorph.isLocalHomeomorph

/-- The comparison from native Spin to its embedded units range is a smooth diffeomorphism. -/
def realSpinDiffeomorphUnitsRange (n : ℕ) :
    Diffeomorph 𝓘(ℝ, realSpinLieModel n) 𝓘(ℝ, realSpinLieModel n)
      (spinGroup (realCliffordForm n 0))
      (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) ∞ where
  toEquiv := (realCliffordSpinContinuousMulEquivUnitsRange n).toEquiv
  contMDiff_toFun := IsLocalHomeomorph.contMDiff_chartedSpaceComap
    (realCliffordSpinContinuousMulEquivUnitsRange n).toHomeomorph.isLocalHomeomorph
  contMDiff_invFun := by
    apply (IsLocalHomeomorph.contMDiff_chartedSpaceComap_iff
      (realCliffordSpinContinuousMulEquivUnitsRange n).toHomeomorph.isLocalHomeomorph).mpr
    refine ⟨(realCliffordSpinContinuousMulEquivUnitsRange n).symm.continuous, ?_⟩
    convert contMDiff_id using 1
    funext s
    exact (realCliffordSpinContinuousMulEquivUnitsRange n).apply_symm_apply s

/-- The smooth comparison is the existing continuous group equivalence. -/
@[simp]
theorem realSpinDiffeomorphUnitsRange_apply (n : ℕ) (s : spinGroup (realCliffordForm n 0)) :
    realSpinDiffeomorphUnitsRange n s = realCliffordSpinContinuousMulEquivUnitsRange n s :=
  (rfl)

/-- The original multiplication and inversion make native compact Spin a Lie group. -/
instance instLieGroupRealSpin (n : ℕ) :
    LieGroup 𝓘(ℝ, realSpinLieModel n) ∞ (spinGroup (realCliffordForm n 0)) where
  contMDiff_mul := by
    apply (IsLocalHomeomorph.contMDiff_chartedSpaceComap_iff
      (realCliffordSpinContinuousMulEquivUnitsRange n).toHomeomorph.isLocalHomeomorph).mpr
    refine ⟨continuous_mul, ?_⟩
    convert ((realSpinDiffeomorphUnitsRange n).contMDiff.comp contMDiff_fst).mul
      ((realSpinDiffeomorphUnitsRange n).contMDiff.comp contMDiff_snd) using 1
    funext p
    exact map_mul (realCliffordSpinContinuousMulEquivUnitsRange n) p.1 p.2
  contMDiff_inv := by
    apply (IsLocalHomeomorph.contMDiff_chartedSpaceComap_iff
      (realCliffordSpinContinuousMulEquivUnitsRange n).toHomeomorph.isLocalHomeomorph).mpr
    refine ⟨continuous_inv, ?_⟩
    convert (realSpinDiffeomorphUnitsRange n).contMDiff.inv using 1
    funext s
    exact map_inv (realCliffordSpinContinuousMulEquivUnitsRange n) s

end TauCeti.CliffordAlgebra

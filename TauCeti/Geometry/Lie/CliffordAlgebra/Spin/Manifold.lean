/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Projection
public import TauCeti.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.Instances.Comap

/-!
# The native compact Spin group as a Lie group

The compact Spin group already has an embedded Lie-group realization in Clifford units.
Here its charts are pulled back to the original Clifford subtype along
`realCliffordSpinContinuousMulEquivUnitsRange`. This keeps the original topology and group
operations and lets constructions on native Spin quotients use the embedded smooth structure.

The comparison is a diffeomorphism, not just an abstract group isomorphism; multiplication
and inversion on the native carrier are smooth, and `realSpinLieEquivUnitsRange` and
`realSpinLieEquivQuadratic` identify its Lie algebra with that of the embedded units range and with
`quadraticLieSubalgebra (realCliffordForm n 0)`.

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
      (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) ∞ :=
  ((realCliffordSpinContinuousMulEquivUnitsRange n).toHomeomorph.isLocalHomeomorph
    |>.isLocalDiffeomorph_chartedSpaceComap (n := ∞)).diffeomorphOfBijective
      (realCliffordSpinContinuousMulEquivUnitsRange n).bijective

/-- The smooth comparison is the existing continuous group equivalence. -/
@[simp]
theorem realSpinDiffeomorphUnitsRange_apply (n : ℕ) (s : spinGroup (realCliffordForm n 0)) :
    realSpinDiffeomorphUnitsRange n s = realCliffordSpinContinuousMulEquivUnitsRange n s :=
  congrFun (IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _) s

/-- The inverse smooth comparison is the inverse continuous group equivalence. -/
@[simp]
theorem realSpinDiffeomorphUnitsRange_symm_apply (n : ℕ)
    (g : MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) :
    (realSpinDiffeomorphUnitsRange n).symm g =
      (realCliffordSpinContinuousMulEquivUnitsRange n).symm g := by
  apply (realCliffordSpinContinuousMulEquivUnitsRange n).injective
  rw [← realSpinDiffeomorphUnitsRange_apply, Diffeomorph.apply_symm_apply,
    ContinuousMulEquiv.apply_symm_apply]

/-- The original multiplication and inversion make native compact Spin a Lie group. -/
instance instLieGroupRealSpin (n : ℕ) :
    LieGroup 𝓘(ℝ, realSpinLieModel n) ∞ (spinGroup (realCliffordForm n 0)) :=
  IsLocalDiffeomorph.lieGroup (I := 𝓘(ℝ, realSpinLieModel n))
    (realCliffordSpinContinuousMulEquivUnitsRange n).symm.toMulEquiv.toMonoidHom
    (by
      convert (realSpinDiffeomorphUnitsRange n).symm.isLocalDiffeomorph using 1
      funext g
      exact (realSpinDiffeomorphUnitsRange_symm_apply n g).symm)
    (realCliffordSpinContinuousMulEquivUnitsRange n).symm.surjective

/-- The Lie-algebra equivalence between native compact Spin and its embedded units range,
induced by the topological group isomorphism `realCliffordSpinContinuousMulEquivUnitsRange`. -/
def realSpinLieEquivUnitsRange (n : ℕ) :
    LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0)) ≃ₗ⁅ℝ⁆
      LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n)
        (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) :=
  (realCliffordSpinContinuousMulEquivUnitsRange n).lieEquiv

/-- The forward Lie-algebra comparison is the Lie map of the units-range group isomorphism. -/
@[simp]
theorem realSpinLieEquivUnitsRange_apply (n : ℕ)
    (X : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0))) :
    realSpinLieEquivUnitsRange n X =
      ContinuousMonoidHom.lieMap
        (I := 𝓘(ℝ, realSpinLieModel n)) (I' := 𝓘(ℝ, realSpinLieModel n))
        (realCliffordSpinContinuousMulEquivUnitsRange n :
          spinGroup (realCliffordForm n 0) →ₜ*
            MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) X :=
  ContinuousMulEquiv.lieEquiv_apply _ X

/-- The inverse Lie-algebra comparison is the Lie map of the inverse units-range group
isomorphism. -/
@[simp]
theorem realSpinLieEquivUnitsRange_symm_apply (n : ℕ)
    (Y : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n)
      (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0)))) :
    (realSpinLieEquivUnitsRange n).symm Y =
      ContinuousMonoidHom.lieMap
        (I := 𝓘(ℝ, realSpinLieModel n)) (I' := 𝓘(ℝ, realSpinLieModel n))
        ((realCliffordSpinContinuousMulEquivUnitsRange n).symm :
          MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0)) →ₜ*
            spinGroup (realCliffordForm n 0)) Y :=
  ContinuousMulEquiv.lieEquiv_symm_apply _ Y

/-- The Lie algebra of native compact Spin identified directly with the quadratic Clifford Lie
subalgebra. -/
def realSpinLieEquivQuadratic (n : ℕ) :
    LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0)) ≃ₗ⁅ℝ⁆
      quadraticLieSubalgebra (realCliffordForm n 0) :=
  (realSpinLieEquivUnitsRange n).trans (realCliffordSpinLieEquivQuadratic n)

/-- Evaluation of the quadratic Clifford coordinate equivalence on native compact Spin. -/
@[simp]
theorem realSpinLieEquivQuadratic_apply (n : ℕ)
    (X : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0))) :
    realSpinLieEquivQuadratic n X =
      realCliffordSpinLieEquivQuadratic n (realSpinLieEquivUnitsRange n X) :=
  (rfl)

/-- Inverse evaluation of the quadratic Clifford coordinate equivalence on native compact Spin. -/
@[simp]
theorem realSpinLieEquivQuadratic_symm_apply (n : ℕ)
    (x : quadraticLieSubalgebra (realCliffordForm n 0)) :
    (realSpinLieEquivQuadratic n).symm x =
      (realSpinLieEquivUnitsRange n).symm ((realCliffordSpinLieEquivQuadratic n).symm x) :=
  (rfl)

end TauCeti.CliffordAlgebra

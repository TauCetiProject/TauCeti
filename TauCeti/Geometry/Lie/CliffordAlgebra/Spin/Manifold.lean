/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.Instances.Comap

/-!
# The native compact Spin group as a Lie group

The compact Spin group already has an embedded Lie-group realization in Clifford units.
Here its charts are pulled back to the original Clifford subtype along
`realCliffordSpinContinuousMulEquivUnitsRange`. This keeps the original topology and group
operations and lets constructions on native Spin quotients use the embedded smooth structure.

The comparison is a diffeomorphism, not just an abstract group isomorphism; multiplication
and inversion on the native carrier are smooth. Composing this comparison with the smooth
projection on the embedded units range gives the smooth projection from native compact Spin to
the embedded special-orthogonal carrier, together with its invertible Lie differential and
local-diffeomorphism property.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

noncomputable section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra Manifold
open scoped Manifold ContDiff Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace

/-- The model space of compact Spin, given by the Lie algebra of its embedded units range. -/
abbrev realSpinLieModel (n : ℕ) :=
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0)))
    (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))))

/-- The model space of the embedded compact special-orthogonal carrier in matrix units. -/
abbrev realSpecialOrthogonalLieModel (n : ℕ) :=
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
    (MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
      (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ)))))

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

/-- The smooth Lie-group isomorphism from native compact Spin to its embedded units range. -/
def realSpinSmoothEquivUnitsRange (n : ℕ) :
    ContMDiffMonoidMorphism 𝓘(ℝ, realSpinLieModel n) 𝓘(ℝ, realSpinLieModel n) ∞
      (spinGroup (realCliffordForm n 0))
      (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) where
  toMonoidHom := (realCliffordSpinContinuousMulEquivUnitsRange n).toMulEquiv.toMonoidHom
  contMDiff_toFun :=
    (realSpinDiffeomorphUnitsRange n).contMDiff.congr fun s ↦
      (realSpinDiffeomorphUnitsRange_apply n s).symm

/-- The bundled smooth comparison acts by `realCliffordSpinContinuousMulEquivUnitsRange`. -/
@[simp]
theorem realSpinSmoothEquivUnitsRange_apply (n : ℕ) (s : spinGroup (realCliffordForm n 0)) :
    realSpinSmoothEquivUnitsRange n s = realCliffordSpinContinuousMulEquivUnitsRange n s :=
  (rfl)

/-- The smooth comparison from native Spin to its embedded units range is a local diffeomorphism. -/
theorem isLocalDiffeomorph_realSpinSmoothEquivUnitsRange (n : ℕ) :
    IsLocalDiffeomorph 𝓘(ℝ, realSpinLieModel n) 𝓘(ℝ, realSpinLieModel n) ∞
      (realSpinSmoothEquivUnitsRange n) := by
  convert (realSpinDiffeomorphUnitsRange n).isLocalDiffeomorph using 1
  funext s
  exact (realSpinDiffeomorphUnitsRange_apply n s).symm

/-- The Lie-algebra equivalence between native compact Spin and its embedded units range. -/
def realSpinLieEquivUnitsRange (n : ℕ) :
    LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0)) ≃ₗ⁅ℝ⁆
      LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n)
        (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) :=
  TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt (realSpinSmoothEquivUnitsRange n)
    (isLocalDiffeomorph_realSpinSmoothEquivUnitsRange n 1)

/-- The Lie equivalence to the embedded units range acts by the Lie map of the comparison. -/
@[simp]
theorem realSpinLieEquivUnitsRange_apply (n : ℕ)
    (X : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0))) :
    realSpinLieEquivUnitsRange n X = lieMap (realSpinSmoothEquivUnitsRange n) X :=
  TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt_apply _ _ X

/-- The Lie homomorphism underlying `realSpinLieEquivUnitsRange` is `lieMap`. -/
@[simp]
theorem realSpinLieEquivUnitsRange_toLieHom (n : ℕ) :
    (realSpinLieEquivUnitsRange n).toLieHom = lieMap (realSpinSmoothEquivUnitsRange n) :=
  TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt_toLieHom _ _

/-- The smooth projection from native compact Spin to the embedded special-orthogonal carrier. -/
def realSpinToSpecialOrthogonalSmoothRange (n : ℕ) :
    ContMDiffMonoidMorphism 𝓘(ℝ, realSpinLieModel n) 𝓘(ℝ, realSpecialOrthogonalLieModel n) ∞
      (spinGroup (realCliffordForm n 0))
      (MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ)))) :=
  (realCliffordSpinToSpecialOrthogonalSmoothRange n).comp (realSpinSmoothEquivUnitsRange n)

/-- The smooth projection from native Spin sends `s` to `spinToSpecialOrthogonal` embedded in the
matrix units range. -/
@[simp]
theorem realSpinToSpecialOrthogonalSmoothRange_apply (n : ℕ)
    (s : spinGroup (realCliffordForm n 0)) :
    realSpinToSpecialOrthogonalSmoothRange n s =
      realCliffordSpecialOrthogonalContinuousMulEquivRange n
        (spinToSpecialOrthogonal (realCliffordForm n 0) s) := by
  simp only [realSpinToSpecialOrthogonalSmoothRange, ContMDiffMonoidMorphism.coe_comp,
    Function.comp_apply, realSpinSmoothEquivUnitsRange_apply,
    realCliffordSpinToSpecialOrthogonalSmoothRange_apply,
    realCliffordSpinContinuousMulEquivUnitsRange_apply,
    realCliffordSpinToSpecialOrthogonalRange_apply_toUnits,
    realCliffordSpecialOrthogonalContinuousMulEquivRange_apply]

/-- The Lie-algebra equivalence from native compact Spin to the embedded special-orthogonal
carrier, given by the differential of the smooth Spin projection. -/
def realSpinToSpecialOrthogonalRangeLieEquiv (n : ℕ) :
    LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0)) ≃ₗ⁅ℝ⁆
      LeftInvariantDerivation 𝓘(ℝ, realSpecialOrthogonalLieModel n)
        (MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
          (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ)))) :=
  (realSpinLieEquivUnitsRange n).trans (realCliffordSpinToSpecialOrthogonalRangeLieEquiv n)

/-- The native Spin projection Lie equivalence acts by `lieMap` of the smooth projection. -/
@[simp]
theorem realSpinToSpecialOrthogonalRangeLieEquiv_apply (n : ℕ)
    (X : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0))) :
    realSpinToSpecialOrthogonalRangeLieEquiv n X =
      lieMap (realSpinToSpecialOrthogonalSmoothRange n) X := by
  -- Congruence avoids costly dependent rewriting through the Clifford and matrix Lie models.
  calc
    realSpinToSpecialOrthogonalRangeLieEquiv n X =
        realCliffordSpinToSpecialOrthogonalRangeLieEquiv n (realSpinLieEquivUnitsRange n X) :=
      rfl
    _ = realCliffordSpinToSpecialOrthogonalRangeLieMap n
          (lieMap (realSpinSmoothEquivUnitsRange n) X) :=
      (realCliffordSpinToSpecialOrthogonalRangeLieEquiv_apply n _).trans
        (congrArg (realCliffordSpinToSpecialOrthogonalRangeLieMap n)
          (realSpinLieEquivUnitsRange_apply n X))
    _ = lieMap (realCliffordSpinToSpecialOrthogonalSmoothRange n)
          (lieMap (realSpinSmoothEquivUnitsRange n) X) :=
      DFunLike.congr_fun (realCliffordSpinToSpecialOrthogonalRangeLieMap_eq_lieMap n) _
    _ = lieMap (realSpinToSpecialOrthogonalSmoothRange n) X :=
      (DFunLike.congr_fun
        (lieMap_comp (realSpinSmoothEquivUnitsRange n)
          (realCliffordSpinToSpecialOrthogonalSmoothRange n)) X).symm

/-- The Lie homomorphism underlying `realSpinToSpecialOrthogonalRangeLieEquiv` is `lieMap`. -/
@[simp]
theorem realSpinToSpecialOrthogonalRangeLieEquiv_toLieHom (n : ℕ) :
    (realSpinToSpecialOrthogonalRangeLieEquiv n).toLieHom =
      lieMap (realSpinToSpecialOrthogonalSmoothRange n) := by
  apply LieHom.ext
  intro X
  exact realSpinToSpecialOrthogonalRangeLieEquiv_apply n X

/-- The smooth projection from native compact Spin to the embedded special-orthogonal carrier is a
local diffeomorphism in every dimension. -/
theorem isLocalDiffeomorph_realSpinToSpecialOrthogonalSmoothRange (n : ℕ) :
    IsLocalDiffeomorph 𝓘(ℝ, realSpinLieModel n) 𝓘(ℝ, realSpecialOrthogonalLieModel n) ∞
      (realSpinToSpecialOrthogonalSmoothRange n) := by
  apply (realSpinToSpecialOrthogonalSmoothRange n).isLocalDiffeomorph_of_lieMap_bijective
  refine ⟨fun X Y h ↦ (realSpinToSpecialOrthogonalRangeLieEquiv n).injective
    ((realSpinToSpecialOrthogonalRangeLieEquiv_apply n X).trans
      (h.trans (realSpinToSpecialOrthogonalRangeLieEquiv_apply n Y).symm)),
    fun Z ↦ ⟨(realSpinToSpecialOrthogonalRangeLieEquiv n).symm Z,
      (realSpinToSpecialOrthogonalRangeLieEquiv_apply n _).symm.trans
        ((realSpinToSpecialOrthogonalRangeLieEquiv n).apply_symm_apply Z)⟩⟩

end TauCeti.CliffordAlgebra

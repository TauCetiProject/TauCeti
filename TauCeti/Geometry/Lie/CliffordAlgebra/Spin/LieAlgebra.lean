/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.LocalDiffeomorph
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Manifold

/-!
# The Lie algebra of compact Spin is `so(n)`

The native compact Spin group `Spin(n)`, with the Lie-group structure pulled back from its
embedded range in the Clifford units (`TauCeti.CliffordAlgebra.instLieGroupRealSpin`), has Lie
algebra `so(n)`, the real skew-symmetric `n × n` matrices
(`TauCeti.CliffordAlgebra.realSpinLieEquivSo`). The equivalence is the differential of the
projection `Spin(n) → SO(n)`, read in skew-matrix coordinates: it is the composite of

* the Lie map of the isomorphism of `Spin(n)` with its range in the Clifford units, bijective
  because this isomorphism is the diffeomorphism
  `TauCeti.CliffordAlgebra.realSpinDiffeomorphUnitsRange`;
* the differential of the projection of that range onto the range of `SO(n)` in the matrix
  units, bijective by `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalRangeLieEquiv`;
* the skew-matrix coordinates of the Lie algebra of that range,
  `TauCeti.CliffordAlgebra.realCliffordSpecialOrthogonalLieEquivSo`.

Since `Spin(3)` is simply connected, Lie-algebra homomorphisms out of `so(3)` integrate along
this equivalence to smooth homomorphisms out of `Spin(3)`.

## Main definitions

* `TauCeti.CliffordAlgebra.realSpinContMDiffMonoidMorphismUnitsRange` and
  `TauCeti.CliffordAlgebra.realSpinLieEquivUnitsRange`: the smooth homomorphism and Lie-algebra
  equivalence identifying compact `Spin(n)` with its range in the Clifford units.
* `TauCeti.CliffordAlgebra.realSpinToSpecialOrthogonalSmoothRange` and
  `TauCeti.CliffordAlgebra.realSpinToSpecialOrthogonalRangeLieEquiv`: the smooth projection onto
  the embedded `SO(n)` carrier and its Lie-algebra equivalence.
* `TauCeti.CliffordAlgebra.realSpinLieEquivSo`: the Lie algebra of compact `Spin(n)` is `so(n)`.

## Main results

* `TauCeti.CliffordAlgebra.isLocalDiffeomorph_realSpinToSpecialOrthogonalSmoothRange`: the smooth
  projection from native compact `Spin(n)` to the embedded `SO(n)` carrier is a local
  diffeomorphism.
* `TauCeti.CliffordAlgebra.realSpinLieEquivSo_apply`: it is the differential of the projection
  `Spin(n) → SO(n)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

open Manifold
open scoped ContDiff Manifold Matrix.Norms.Operator

noncomputable section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra TauCeti.Lie

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace

/-- The model space of the embedded compact special-orthogonal carrier in matrix units. -/
abbrev realSpecialOrthogonalLieModel (n : ℕ) :=
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
    (MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
      (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ)))))

/-- The isomorphism `TauCeti.CliffordAlgebra.realCliffordSpinContinuousMulEquivUnitsRange` of
compact `Spin(n)` with its range in the Clifford units, as a smooth homomorphism: it is the
diffeomorphism `TauCeti.CliffordAlgebra.realSpinDiffeomorphUnitsRange`. -/
def realSpinContMDiffMonoidMorphismUnitsRange (n : ℕ) :
    ContMDiffMonoidMorphism 𝓘(ℝ, realSpinLieModel n) 𝓘(ℝ, realSpinLieModel n) ∞
      (spinGroup (realCliffordForm n 0))
      (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) where
  toMonoidHom := (realCliffordSpinContinuousMulEquivUnitsRange n).toMonoidHom
  contMDiff_toFun := by
    convert (realSpinDiffeomorphUnitsRange n).contMDiff using 1
    funext s
    exact (realSpinDiffeomorphUnitsRange_apply n s).symm

@[simp]
theorem coe_realSpinContMDiffMonoidMorphismUnitsRange (n : ℕ) :
    ⇑(realSpinContMDiffMonoidMorphismUnitsRange n) =
      realCliffordSpinContinuousMulEquivUnitsRange n :=
  (rfl)

/-- The isomorphism of compact `Spin(n)` with its range in the Clifford units is a local
diffeomorphism. -/
theorem isLocalDiffeomorph_realSpinContMDiffMonoidMorphismUnitsRange (n : ℕ) :
    IsLocalDiffeomorph 𝓘(ℝ, realSpinLieModel n) 𝓘(ℝ, realSpinLieModel n) ∞
      (realSpinContMDiffMonoidMorphismUnitsRange n) := by
  convert (realSpinDiffeomorphUnitsRange n).isLocalDiffeomorph using 1
  funext s
  exact (realSpinDiffeomorphUnitsRange_apply n s).symm

/-- The Lie-algebra equivalence between native compact Spin and its embedded units range. -/
def realSpinLieEquivUnitsRange (n : ℕ) :
    LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0)) ≃ₗ⁅ℝ⁆
      LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n)
        (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))) :=
  lieEquivOfIsLocalDiffeomorphAt (realSpinContMDiffMonoidMorphismUnitsRange n)
    (isLocalDiffeomorph_realSpinContMDiffMonoidMorphismUnitsRange n 1)

/-- The Lie equivalence to the embedded units range acts by the Lie map of the comparison. -/
@[simp]
theorem realSpinLieEquivUnitsRange_apply (n : ℕ)
    (X : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0))) :
    realSpinLieEquivUnitsRange n X = lieMap (realSpinContMDiffMonoidMorphismUnitsRange n) X :=
  lieEquivOfIsLocalDiffeomorphAt_apply _ _ X

/-- The Lie homomorphism underlying `realSpinLieEquivUnitsRange` is `lieMap`. -/
@[simp]
theorem realSpinLieEquivUnitsRange_toLieHom (n : ℕ) :
    (realSpinLieEquivUnitsRange n).toLieHom =
      lieMap (realSpinContMDiffMonoidMorphismUnitsRange n) :=
  lieEquivOfIsLocalDiffeomorphAt_toLieHom _ _

/-- The inverse of `realSpinLieEquivUnitsRange` cancels `lieMap` of the smooth comparison. -/
@[simp]
theorem realSpinLieEquivUnitsRange_symm_apply_lieMap (n : ℕ)
    (X : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0))) :
    (realSpinLieEquivUnitsRange n).symm
      (lieMap (realSpinContMDiffMonoidMorphismUnitsRange n) X) = X :=
  lieEquivOfIsLocalDiffeomorphAt_symm_apply_lieMap _ _ X

/-- Applying `lieMap` of the smooth comparison cancels `(realSpinLieEquivUnitsRange n).symm`. -/
@[simp]
theorem lieMap_realSpinLieEquivUnitsRange_symm_apply (n : ℕ)
    (Y : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n)
      (MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0)))) :
    lieMap (realSpinContMDiffMonoidMorphismUnitsRange n)
      ((realSpinLieEquivUnitsRange n).symm Y) = Y :=
  lieMap_lieEquivOfIsLocalDiffeomorphAt_symm_apply _ _ Y

/-- The smooth projection from native compact Spin to the embedded special-orthogonal carrier. -/
def realSpinToSpecialOrthogonalSmoothRange (n : ℕ) :
    ContMDiffMonoidMorphism 𝓘(ℝ, realSpinLieModel n) 𝓘(ℝ, realSpecialOrthogonalLieModel n) ∞
      (spinGroup (realCliffordForm n 0))
      (MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ)))) :=
  (realCliffordSpinToSpecialOrthogonalSmoothRange n).comp
    (realSpinContMDiffMonoidMorphismUnitsRange n)

/-- The smooth projection from native Spin sends `s` to `spinToSpecialOrthogonal` embedded in the
matrix units range. -/
@[simp]
theorem realSpinToSpecialOrthogonalSmoothRange_apply (n : ℕ)
    (s : spinGroup (realCliffordForm n 0)) :
    realSpinToSpecialOrthogonalSmoothRange n s =
      realCliffordSpecialOrthogonalContinuousMulEquivRange n
        (spinToSpecialOrthogonal (realCliffordForm n 0) s) := by
  simp only [realSpinToSpecialOrthogonalSmoothRange, ContMDiffMonoidMorphism.coe_comp,
    Function.comp_apply, coe_realSpinContMDiffMonoidMorphismUnitsRange,
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
  simp [realSpinToSpecialOrthogonalRangeLieEquiv, realSpinToSpecialOrthogonalSmoothRange,
    realCliffordSpinToSpecialOrthogonalRangeLieMap_eq_lieMap]

/-- The inverse of `realSpinToSpecialOrthogonalRangeLieEquiv` cancels `lieMap` of the smooth Spin
projection. -/
@[simp]
theorem realSpinToSpecialOrthogonalRangeLieEquiv_symm_apply_lieMap (n : ℕ)
    (X : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0))) :
    (realSpinToSpecialOrthogonalRangeLieEquiv n).symm
      (lieMap (realSpinToSpecialOrthogonalSmoothRange n) X) = X := by
  -- Congruence avoids costly `isDefEq` unfolding across the Spin/SO Lie-subalgebra models.
  calc
    (realSpinToSpecialOrthogonalRangeLieEquiv n).symm
        (lieMap (realSpinToSpecialOrthogonalSmoothRange n) X)
      = (realSpinToSpecialOrthogonalRangeLieEquiv n).symm
          (realSpinToSpecialOrthogonalRangeLieEquiv n X) :=
      congrArg (realSpinToSpecialOrthogonalRangeLieEquiv n).symm
        (realSpinToSpecialOrthogonalRangeLieEquiv_apply n X).symm
    _ = X := (realSpinToSpecialOrthogonalRangeLieEquiv n).symm_apply_apply X

/-- Applying `lieMap` of the smooth Spin projection cancels
`(realSpinToSpecialOrthogonalRangeLieEquiv n).symm`. -/
@[simp]
theorem lieMap_realSpinToSpecialOrthogonalRangeLieEquiv_symm_apply (n : ℕ)
    (Ω : LeftInvariantDerivation 𝓘(ℝ, realSpecialOrthogonalLieModel n)
      (MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ))))) :
    lieMap (realSpinToSpecialOrthogonalSmoothRange n)
      ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω) = Ω := by
  calc
    lieMap (realSpinToSpecialOrthogonalSmoothRange n)
        ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω)
      = realSpinToSpecialOrthogonalRangeLieEquiv n
          ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω) :=
      (realSpinToSpecialOrthogonalRangeLieEquiv_apply n _).symm
    _ = Ω := (realSpinToSpecialOrthogonalRangeLieEquiv n).apply_symm_apply Ω

/-- Pushing forward the native Spin inverse lift to the units range recovers the units-range
inverse lift. -/
theorem realSpinLieEquivUnitsRange_realSpinToSpecialOrthogonalRangeLieEquiv_symm (n : ℕ)
    (Ω : LeftInvariantDerivation 𝓘(ℝ, realSpecialOrthogonalLieModel n)
      (MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
        (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ))))) :
    realSpinLieEquivUnitsRange n ((realSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω) =
      (realCliffordSpinToSpecialOrthogonalRangeLieEquiv n).symm Ω := by
  simp [realSpinToSpecialOrthogonalRangeLieEquiv]

/-- The Lie homomorphism underlying `realSpinToSpecialOrthogonalRangeLieEquiv` is `lieMap`. -/
@[simp]
theorem realSpinToSpecialOrthogonalRangeLieEquiv_toLieHom (n : ℕ) :
    (realSpinToSpecialOrthogonalRangeLieEquiv n).toLieHom =
      lieMap (realSpinToSpecialOrthogonalSmoothRange n) :=
  LieHom.ext <| realSpinToSpecialOrthogonalRangeLieEquiv_apply n

/-- The smooth projection from native compact Spin to the embedded special-orthogonal carrier is a
local diffeomorphism in every dimension. -/
theorem isLocalDiffeomorph_realSpinToSpecialOrthogonalSmoothRange (n : ℕ) :
    IsLocalDiffeomorph 𝓘(ℝ, realSpinLieModel n) 𝓘(ℝ, realSpecialOrthogonalLieModel n) ∞
      (realSpinToSpecialOrthogonalSmoothRange n) := by
  rw [realSpinToSpecialOrthogonalSmoothRange, ContMDiffMonoidMorphism.coe_comp]
  exact fun s ↦ IsLocalDiffeomorphAt.comp
    (hf := isLocalDiffeomorph_realSpinContMDiffMonoidMorphismUnitsRange n s)
    (hg := isLocalDiffeomorph_realCliffordSpinToSpecialOrthogonalSmoothRange n _)

/-- **The Lie algebra of compact `Spin(n)` is `so(n)`.** The differential of the projection
`Spin(n) → SO(n)`, in skew-symmetric-matrix coordinates
(`TauCeti.CliffordAlgebra.realSpinLieEquivSo_apply`). -/
def realSpinLieEquivSo (n : ℕ) :
    LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0)) ≃ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so (Fin n) ℝ :=
  (realSpinToSpecialOrthogonalRangeLieEquiv n).trans (realCliffordSpecialOrthogonalLieEquivSo n)

/-- `TauCeti.CliffordAlgebra.realSpinLieEquivSo` is the Lie map of the projection of compact
`Spin(n)` onto the range of `SO(n)` in the matrix units, read in skew-symmetric-matrix
coordinates. -/
theorem realSpinLieEquivSo_apply (n : ℕ)
    (X : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0))) :
    realSpinLieEquivSo n X = realCliffordSpecialOrthogonalLieEquivSo n
      (lieMap ((realCliffordSpinToSpecialOrthogonalSmoothRange n).comp
        (realSpinContMDiffMonoidMorphismUnitsRange n)) X) := by
  simp [realSpinLieEquivSo, realSpinToSpecialOrthogonalSmoothRange]

end TauCeti.CliffordAlgebra

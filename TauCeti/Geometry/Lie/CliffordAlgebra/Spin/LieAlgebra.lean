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

* `TauCeti.CliffordAlgebra.realSpinContMDiffMonoidMorphismUnitsRange`: the isomorphism of compact
  `Spin(n)` with its range in the Clifford units, as a smooth homomorphism.
* `TauCeti.CliffordAlgebra.realSpinLieEquivSo`: the Lie algebra of compact `Spin(n)` is `so(n)`.

## Main results

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

/-- **The Lie algebra of compact `Spin(n)` is `so(n)`.** The differential of the projection
`Spin(n) → SO(n)`, in skew-symmetric-matrix coordinates
(`TauCeti.CliffordAlgebra.realSpinLieEquivSo_apply`). -/
def realSpinLieEquivSo (n : ℕ) :
    LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0)) ≃ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so (Fin n) ℝ :=
  ((lieEquivOfIsLocalDiffeomorphAt (realSpinContMDiffMonoidMorphismUnitsRange n)
      (isLocalDiffeomorph_realSpinContMDiffMonoidMorphismUnitsRange n 1)).trans
    (realCliffordSpinToSpecialOrthogonalRangeLieEquiv n)).trans
    (realCliffordSpecialOrthogonalLieEquivSo n)

/-- `TauCeti.CliffordAlgebra.realSpinLieEquivSo` is the Lie map of the projection of compact
`Spin(n)` onto the range of `SO(n)` in the matrix units, read in skew-symmetric-matrix
coordinates. -/
theorem realSpinLieEquivSo_apply (n : ℕ)
    (X : LeftInvariantDerivation 𝓘(ℝ, realSpinLieModel n) (spinGroup (realCliffordForm n 0))) :
    realSpinLieEquivSo n X = realCliffordSpecialOrthogonalLieEquivSo n
      (lieMap ((realCliffordSpinToSpecialOrthogonalSmoothRange n).comp
        (realSpinContMDiffMonoidMorphismUnitsRange n)) X) := by
  simp [realSpinLieEquivSo, lieMap_comp, realCliffordSpinToSpecialOrthogonalRangeLieMap_eq_lieMap]

end TauCeti.CliffordAlgebra

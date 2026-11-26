/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.RepresentationTheory.SU2.StandardBasis
public import TauCeti.Topology.Algebra.Quaternion.Unitary
public import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# `SU(2)` as a compact simply connected Lie group

The special unitary subgroup `TauCeti.GLSpecialUnitary (Fin 2) ℂ` of the real Lie group
`GL(2, ℂ)` is closed, so the closed-subgroup theorem makes it a Lie group modelled on its Lie
algebra `𝔰𝔲(2)` (`TauCeti.SU2.lieAlgebra`), with smooth inclusion into `GL(2, ℂ)`
(`TauCeti.SU2.embeddedLieSubgroupData`). This file records the facts about this Lie group that
are needed to integrate Lie-algebra homomorphisms out of `𝔰𝔲(2)` and to read the result as a map
out of the three-sphere.

As a topological group the subgroup of `GL(2, ℂ)` is the matrix special unitary group
(`TauCeti.GLSpecialUnitary.continuousMulEquiv`), which is compact and is the group of unit
quaternions. So `SU(2)` is homeomorphic to the unit sphere of `ℝ⁴`
(`TauCeti.SU2.homeomorphSphere`), and it is simply connected
(`TauCeti.SU2.instSimplyConnectedSpace`). Its native Lie algebra, made of its own left-invariant
derivations, is identified with `𝔰𝔲(2)` by the differential of the inclusion
(`TauCeti.SU2.nativeLieEquiv`), and `𝔰𝔲(2)` is three-dimensional.

The Lie group `GL(2, ℂ)` and its Lie algebra use the topology of the operator norm on matrices,
`Matrix.linftyOpTopologicalSpace`, as in `TauCeti.RepresentationTheory.SU2.StandardBasis`. It is
the entrywise topology by definition, but not syntactically, so the topological facts are proved
for the entrywise topology first and then used under the operator-norm instances.

## Main definitions

* `TauCeti.SU2.homeomorphSphere`: `SU(2)` is homeomorphic to the unit sphere of `ℝ⁴`, with
  `coe_homeomorphSphere_apply` and `coe_homeomorphSphere_symm_apply` giving its coordinates.
* `TauCeti.SU2.embeddedLieSubgroupData`: the Lie group structure of `SU(2)`, modelled on `𝔰𝔲(2)`.
* `TauCeti.SU2.nativeLieEquiv`: the native Lie algebra of `SU(2)` is `𝔰𝔲(2)`.

## Main results

* `TauCeti.SU2.instSimplyConnectedSpace`: `SU(2)` is simply connected.
* `TauCeti.SU2.not_isLieAbelian_leftInvariantDerivation`: the native Lie algebra of `SU(2)` is not
  abelian.
-/

public section

noncomputable section

open Metric
open scoped ContDiff Manifold

namespace TauCeti

namespace SU2

/-- **`SU(2)` is the three-sphere.** The special unitary subgroup of `GL(2, ℂ)` is homeomorphic to
the unit sphere of `ℝ⁴`, through the matrix special unitary group, the unit quaternions and the
standard coordinates of the quaternions. -/
def homeomorphSphere :
    GLSpecialUnitary (Fin 2) ℂ ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  (GLSpecialUnitary.continuousMulEquiv (Fin 2) ℂ).toHomeomorph.trans <|
    Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup.symm.toHomeomorph.trans <|
      Quaternion.unitaryHomeomorphSphere.trans <|
        Quaternion.linearIsometryEquivTuple.toHomeomorph.subtype fun q ↦ by
          simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph,
            LinearIsometryEquiv.norm_map]

/-- `TauCeti.SU2.homeomorphSphere` sends `g` to the coordinates of the unit quaternion with matrix
`g`, which are the real and imaginary parts of the first row of `g`. -/
@[simp]
theorem coe_homeomorphSphere_apply (g : GLSpecialUnitary (Fin 2) ℂ) :
    (homeomorphSphere g : EuclideanSpace ℝ (Fin 4)) =
      !₂[(((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re,
        (((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im,
        (((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re,
        (((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im] := by
  have hg := Quaternion.coe_unitaryEquivSpecialUnitaryGroup_symm_apply
    (GLSpecialUnitary.continuousMulEquiv (Fin 2) ℂ g)
  rw [GLSpecialUnitary.coe_continuousMulEquiv_apply, Quaternion.toComplexMatrix_apply] at hg
  rw [← hg]
  simp [homeomorphSphere]

/-- The inverse of `TauCeti.SU2.homeomorphSphere` sends a point of the sphere to the matrix of the
quaternion with those coordinates. -/
@[simp]
theorem coe_homeomorphSphere_symm_apply (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    ((homeomorphSphere.symm x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      Quaternion.toComplexMatrix (Quaternion.linearIsometryEquivTuple.symm x) := by
  simp [homeomorphSphere, ContinuousMulEquiv.toHomeomorph_eq_coe,
    Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup_apply,
    Quaternion.coe_unitaryEquivSpecialUnitaryGroup_apply]

/-- `SU(2)` is simply connected, as the group of unit quaternions. -/
instance instSimplyConnectedSpace : SimplyConnectedSpace (GLSpecialUnitary (Fin 2) ℂ) :=
  (GLSpecialUnitary.continuousMulEquiv (Fin 2) ℂ).toHomeomorph.toHomotopyEquiv.simplyConnectedSpace

-- Use the operator-norm topology under which `GL(2, ℂ)` is a Lie group, as in
-- `TauCeti.RepresentationTheory.SU2.StandardBasis`.
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
  TauCeti.normedAlgebraRatOfReal

open scoped Matrix.Norms.Operator

/-- **`SU(2)` is a Lie group.** The structure of embedded Lie subgroup of `GL(2, ℂ)` that the
closed-subgroup theorem gives the closed subgroup `SU(2)`, with model space its Lie algebra
`𝔰𝔲(2)`. -/
def embeddedLieSubgroupData :
    Lie.EmbeddedLieSubgroupData 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ) (GLSpecialUnitary (Fin 2) ℂ)
      lieAlgebra.toSubmodule :=
  Lie.EmbeddedLieSubgroupData.ofIsClosed (isClosed_GLSpecialUnitary (Fin 2) ℂ)

instance : ChartedSpace lieAlgebra.toSubmodule (GLSpecialUnitary (Fin 2) ℂ) :=
  embeddedLieSubgroupData.chartedSpace

instance : LieGroup 𝓘(ℝ, lieAlgebra.toSubmodule) ∞ (GLSpecialUnitary (Fin 2) ℂ) :=
  embeddedLieSubgroupData.lieGroup

/-! The instances above for the entrywise topology of matrices, restated for the operator-norm
topology. The two topologies agree by definition (`Matrix.linftyOpTopologicalSpace_eq`), but not
up to instance reducibility, so instance search does not transfer them. -/

/-- `SU(2)` is compact, for the operator-norm topology. -/
instance instCompactSpaceOperatorNorm : CompactSpace (GLSpecialUnitary (Fin 2) ℂ) :=
  GLSpecialUnitary.instCompactSpace

/-- `SU(2)` is simply connected, for the operator-norm topology. -/
instance instSimplyConnectedSpaceOperatorNorm : SimplyConnectedSpace (GLSpecialUnitary (Fin 2) ℂ) :=
  instSimplyConnectedSpace

/-- `SU(2)` is second countable, for the operator-norm topology. -/
instance instSecondCountableTopologyOperatorNorm :
    SecondCountableTopology (GLSpecialUnitary (Fin 2) ℂ) :=
  GLSpecialUnitary.instSecondCountableTopology

/-- **The native Lie algebra of `SU(2)` is `𝔰𝔲(2)`.** The differential of the inclusion of
`SU(2)` into `GL(2, ℂ)` identifies the left-invariant derivations of the Lie group `SU(2)` with
`𝔰𝔲(2)`. -/
def nativeLieEquiv :
    LeftInvariantDerivation 𝓘(ℝ, lieAlgebra.toSubmodule) (GLSpecialUnitary (Fin 2) ℂ) ≃ₗ⁅ℝ⁆
      lieAlgebra :=
  embeddedLieSubgroupData.lieEquivLieSubalgebraOfSubgroup

/-- The identification `TauCeti.SU2.nativeLieEquiv` is the differential of the inclusion of
`SU(2)` into `GL(2, ℂ)`. -/
@[simp]
theorem coe_nativeLieEquiv_apply
    (X : LeftInvariantDerivation 𝓘(ℝ, lieAlgebra.toSubmodule) (GLSpecialUnitary (Fin 2) ℂ)) :
    (nativeLieEquiv X : LeftInvariantDerivation 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ)
        (Matrix (Fin 2) (Fin 2) ℂ)ˣ) =
      embeddedLieSubgroupData.lieMapSubtypeVal X :=
  embeddedLieSubgroupData.lieEquivLieSubalgebraOfSubgroup_apply X

/-- **The native Lie algebra of `SU(2)` is not abelian**, since it is `𝔰𝔲(2)`
(`TauCeti.SU2.nativeLieEquiv`, `TauCeti.SU2.not_isLieAbelian_lieAlgebra`). -/
theorem not_isLieAbelian_leftInvariantDerivation :
    ¬IsLieAbelian
      (LeftInvariantDerivation 𝓘(ℝ, lieAlgebra.toSubmodule) (GLSpecialUnitary (Fin 2) ℂ)) :=
  fun h ↦ not_isLieAbelian_lieAlgebra (nativeLieEquiv.symm.injective.isLieAbelian h)

end SU2

end TauCeti

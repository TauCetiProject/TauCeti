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
import TauCeti.RepresentationTheory.SU2.NormalSubgroup

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

The element `diag(i, -i)` of the native Lie algebra (`TauCeti.SU2.torusGenerator`) generates the
diagonal torus `diag(e^{is}, e^{-is})` of `SU(2)`. So a smooth homomorphism `φ` out of `SU(2)`
sends the diagonal torus to the one-parameter subgroup of `dφ(diag(i, -i))`, which has period
`2π`. If `dφ(diag(i, -i)) ≠ 0`, then `φ` is not trivial, so its kernel lies in the center
`{1, -1}` of `SU(2)` (`TauCeti.SU2.ker_le_center`).

The Lie group `GL(2, ℂ)` and its Lie algebra use the topology of the operator norm on matrices,
`Matrix.linftyOpTopologicalSpace`, as in `TauCeti.RepresentationTheory.SU2.StandardBasis`. It is
the entrywise topology by definition, but not syntactically, so the topological facts are proved
for the entrywise topology first and then used under the operator-norm instances.

## Main definitions

* `TauCeti.SU2.homeomorphSphere`: `SU(2)` is homeomorphic to the unit sphere of `ℝ⁴`, with
  `coe_homeomorphSphere_apply` and `coe_homeomorphSphere_symm_apply` giving its coordinates.
* `TauCeti.SU2.embeddedLieSubgroupData`: the Lie group structure of `SU(2)`, modelled on `𝔰𝔲(2)`.
* `TauCeti.SU2.nativeLieEquiv`: the native Lie algebra of `SU(2)` is `𝔰𝔲(2)`.
* `TauCeti.SU2.torusGenerator`: the element `diag(i, -i)` of the native Lie algebra of `SU(2)`.

## Main results

* `TauCeti.SU2.instSimplyConnectedSpace`: `SU(2)` is simply connected.
* `TauCeti.SU2.lieExp_smul_torusGenerator`: `exp(s diag(i, -i)) = diag(e^{is}, e^{-is})`.
* `ContMDiffMonoidMorphism.map_torusExp`: a smooth homomorphism `φ` out of `SU(2)` sends the
  diagonal torus to the one-parameter subgroup of `dφ(diag(i, -i))`.
* `ContMDiffMonoidMorphism.lieExp_two_pi_smul_lieMap_torusGenerator`: that one-parameter subgroup
  has period `2π`, so `exp(2π dφ(diag(i, -i))) = 1`.
* `ContMDiffMonoidMorphism.ker_le_center_of_lieMap_ne_zero`: if `dφ(diag(i, -i)) ≠ 0`, the kernel
  of `φ` lies in the center `{1, -1}` of `SU(2)`.
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

/-! ### The generator of the diagonal torus -/

section TorusGenerator

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- The element `diag(i, -i)` of the native Lie algebra of the Lie group `SU(2)`: the coroot of the
positive root of the diagonal torus. It is `-2` times the basis element `-iσ₃/2` of `𝔰𝔲(2)`. -/
def torusGenerator :
    LeftInvariantDerivation 𝓘(ℝ, lieAlgebra.toSubmodule) (GLSpecialUnitary (Fin 2) ℂ) :=
  nativeLieEquiv.symm ((-2 : ℝ) • suTwoEquiv (Pi.single 2 1))

/-- The identification `TauCeti.SU2.nativeLieEquiv` sends `TauCeti.SU2.torusGenerator` to `-2`
times the basis element `-iσ₃/2` of `𝔰𝔲(2)`. -/
@[simp]
theorem nativeLieEquiv_torusGenerator :
    nativeLieEquiv torusGenerator = (-2 : ℝ) • suTwoEquiv (Pi.single 2 1) :=
  LieEquiv.apply_symm_apply _ _

/-- The matrix of `TauCeti.SU2.torusGenerator` is `diag(i, -i)`. -/
theorem toMatrix_nativeLieEquiv_torusGenerator :
    toMatrix (nativeLieEquiv torusGenerator) = Matrix.diagonal ![Complex.I, -Complex.I] := by
  rw [nativeLieEquiv_torusGenerator, map_smul, toMatrix_suTwoEquiv_single_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **The one-parameter subgroup of `diag(i, -i)` is the diagonal torus of `SU(2)`**:
`exp(s diag(i, -i)) = diag(e^{is}, e^{-is})`. -/
theorem lieExp_smul_torusGenerator (s : ℝ) :
    lieExp (s • torusGenerator) =
      (GLSpecialUnitary.continuousMulEquiv (Fin 2) ℂ).symm (torusExp s) := by
  apply Subtype.ext
  apply Units.ext
  have hmap := map_lieExp embeddedLieSubgroupData.subtypeVal (s • torusGenerator)
  dsimp only at hmap
  have hsub : (embeddedLieSubgroupData.subtypeVal (lieExp (s • torusGenerator)) :
      (Matrix (Fin 2) (Fin 2) ℂ)ˣ) =
      ((lieExp (s • torusGenerator) : GLSpecialUnitary (Fin 2) ℂ) : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) :=
    embeddedLieSubgroupData.subtypeVal_apply _
  have hY : (lieMap embeddedLieSubgroupData.subtypeVal (s • torusGenerator) :
      LeftInvariantDerivation 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ) (Matrix (Fin 2) (Fin 2) ℂ)ˣ) =
      (((s * -2) • suTwoEquiv (Pi.single 2 1) : lieAlgebra) :
        LeftInvariantDerivation 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ) (Matrix (Fin 2) (Fin 2) ℂ)ˣ) := by
    rw [← Lie.EmbeddedLieSubgroupData.lieMapSubtypeVal_apply, ← coe_nativeLieEquiv_apply,
      map_smul, nativeLieEquiv_torusGenerator, smul_smul]
  rw [← hsub, hmap, hY, coe_lieExp_smul_suTwoEquiv_single_two,
    GLSpecialUnitary.coe_continuousMulEquiv_symm_apply]
  congr 2
  ring

end TorusGenerator

end SU2

end TauCeti

open TauCeti

namespace ContMDiffMonoidMorphism

-- Use the operator-norm topology under which `GL(2, ℂ)` is a Lie group, as above.
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
  TauCeti.normedAlgebraRatOfReal
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

open scoped Matrix.Norms.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-- **A smooth homomorphism out of `SU(2)` on the diagonal torus.** For a smooth homomorphism
`φ : SU(2) → G` with `v = dφ(diag(i, -i))`, `φ(diag(e^{is}, e^{-is})) = exp_G(s v)`. -/
theorem map_torusExp
    (φ : ContMDiffMonoidMorphism 𝓘(ℝ, SU2.lieAlgebra.toSubmodule) I ∞
      (GLSpecialUnitary (Fin 2) ℂ) G) (s : ℝ) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    φ ((GLSpecialUnitary.continuousMulEquiv (Fin 2) ℂ).symm (SU2.torusExp s)) =
      lieExp (s • lieMap φ SU2.torusGenerator) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  dsimp only
  rw [← SU2.lieExp_smul_torusGenerator, map_lieExp, map_smul]

/-- **The image of `diag(i, -i)` has period `2π`.** For a smooth homomorphism `φ : SU(2) → G`,
`exp_G(2π dφ(diag(i, -i))) = 1`: the vector `dφ(diag(i, -i))` lies in the period lattice
`(2π)⁻¹ ker(exp_G)`. For the rank-one homomorphism of a root it is the coroot, which is therefore
an integral cocharacter. -/
theorem lieExp_two_pi_smul_lieMap_torusGenerator
    (φ : ContMDiffMonoidMorphism 𝓘(ℝ, SU2.lieAlgebra.toSubmodule) I ∞
      (GLSpecialUnitary (Fin 2) ℂ) G) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    lieExp ((2 * Real.pi) • lieMap φ SU2.torusGenerator) = 1 := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  dsimp only
  rw [← map_torusExp, SU2.torusExp_eq_one_iff.mpr ⟨1, by ring⟩, map_one, map_one]

/-- **The kernel bound.** A smooth homomorphism `φ : SU(2) → G` with `dφ(diag(i, -i)) ≠ 0` has
kernel contained in the center `{1, -1}` of `SU(2)`, read through the identification of the
special unitary subgroup of `GL(2, ℂ)` with the matrix group `SU(2)`. This applies to the rank-one
homomorphism of a root, whose differential sends `diag(i, -i)` to the coroot. -/
theorem ker_le_center_of_lieMap_ne_zero
    (φ : ContMDiffMonoidMorphism 𝓘(ℝ, SU2.lieAlgebra.toSubmodule) I ∞
      (GLSpecialUnitary (Fin 2) ℂ) G)
    (hφ : lieMap φ SU2.torusGenerator ≠ 0) :
    (φ.toMonoidHom.comp (GLSpecialUnitary.continuousMulEquiv (Fin 2) ℂ).symm.toMonoidHom).ker ≤
      Subgroup.center SU2 := by
  refine SU2.ker_le_center fun h ↦ hφ ?_
  -- A trivial composite forces `φ` itself to be trivial, whose differential vanishes.
  have h1 : φ = 1 := DFunLike.ext _ _ fun x ↦ by
    simpa using DFunLike.congr_fun h (GLSpecialUnitary.continuousMulEquiv (Fin 2) ℂ x)
  rw [h1, lieMap_one, zero_apply]

end ContMDiffMonoidMorphism

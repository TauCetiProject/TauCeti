/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.PosUpperTriangular.Immersed
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Lie groups immersed in `GL_n` through the positive triangular group

Let `C` be a connected real Lie group and `f : C →* GL_n(𝕜)`, for `𝕜` the real or complex numbers,
an injective homomorphism which is a smooth immersion into the general linear group (as a real
Lie group of units) and takes values in the positive triangular group `AN` of upper-triangular
matrices with positive real diagonal. Corestricting `f` to `AN` presents `C` as a connected
immersed Lie subgroup of `AN`, for the closed-subgroup smooth structure of `AN`. The results on
such subgroups (`TauCeti.Lie.ImmersedLieSubgroupData.lieExp_bijective_of_posUpperTriangular` and
its companions) then apply to `C` with its own intrinsic topology: the exponential of `C` is a
global diffeomorphism and `f` is a smooth embedding with closed image.

## Main definitions

* `TauCeti.Lie.lieExpDiffeomorphOfImmersedPosUpperTriangular`: the exponential of `C` as a global
  diffeomorphism.

## Main results

* `TauCeti.Lie.isImmersion_codRestrict_posUpperTriangularGroup`: the corestriction of `f` to `AN`
  is an immersion.
* `TauCeti.Lie.lieExp_bijective_of_immersed_posUpperTriangular`: the exponential of `C` is
  bijective.
* `TauCeti.Lie.isSmoothEmbedding_of_immersed_posUpperTriangular` and
  `TauCeti.Lie.isClosedEmbedding_of_immersed_posUpperTriangular`: `f` is a smooth embedding and a
  closed embedding, so its image is closed.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition (1996), Chapter VI,
  Section 4, Example, pp.311–312, for the positive triangular factor.
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups* (2012), Section 14.4,
  Theorem 14.4.8, for Lie groups whose exponential is a global diffeomorphism.
-/

public noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Matrix.Norms.Operator

attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace TauCeti.Lie

attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

attribute [local instance] ImmersedLieSubgroupData.group
  ImmersedLieSubgroupData.topologicalSpace ImmersedLieSubgroupData.normedAddCommGroup
  ImmersedLieSubgroupData.normedSpace ImmersedLieSubgroupData.finiteDimensional
  ImmersedLieSubgroupData.modelTopology ImmersedLieSubgroupData.chartedSpace
  ImmersedLieSubgroupData.lieGroup ImmersedLieSubgroupData.connectedSpace

section Immersion

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {C : Type*} [Group C] [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]

/-- A smooth immersion into `GL ι 𝕜` with values in the positive triangular group `AN` is a
smooth immersion into `AN`, for the closed-subgroup smooth structure of `AN`. -/
theorem isImmersion_codRestrict_posUpperTriangularGroup {f : C →* GL ι 𝕜}
    (himm : IsImmersion I 𝓘(ℝ, Matrix ι ι 𝕜) ∞ f) (hf : ∀ c, f c ∈ posUpperTriangularGroup ι 𝕜) :
    IsImmersion I 𝓘(ℝ, LieSubalgebra.toSubmodule (lieSubalgebraOfSubgroup
      (I := 𝓘(ℝ, Matrix ι ι 𝕜)) (posUpperTriangularGroup ι 𝕜))) ∞
      (f.codRestrict (posUpperTriangularGroup ι 𝕜) hf) := by
  have he :=
    (posUpperTriangularEmbeddedLieSubgroupData (ι := ι) (𝕜 := 𝕜)).isSmoothEmbedding_subtypeVal
  exact (he.contMDiff_iff_comp.2 himm.contMDiff).isImmersion_of_isImmersion_comp (by simp)
    (fun _ ↦ he.contMDiff.mdifferentiableAt (by simp)) himm

end Immersion

section GeneralLinear

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {C : Type*} [Group C] [TopologicalSpace C] [ChartedSpace H C] [LieGroup I ∞ C]

local notation "Mat" => Matrix (Fin n) (Fin n) 𝕜
local notation "AN" => posUpperTriangularGroup (Fin n) 𝕜
local notation "Model" => LieSubalgebra.toSubmodule
  (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Mat)) AN)

variable [FiniteDimensional ℝ E] [T2Space C] [ConnectedSpace C]

/-- A connected real Lie group `C` with an injective smooth immersive homomorphism into `GL_n(𝕜)`
with values in the positive triangular group `AN` presents a connected immersed Lie subgroup
of `AN`. -/
private def immersedLieSubgroupDataOfPosUpperTriangular (f : C →* GL (Fin n) 𝕜) (hinj : Injective f)
    (himm : IsImmersion I 𝓘(ℝ, Mat) ∞ f) (hf : ∀ c, f c ∈ AN) :
    ImmersedLieSubgroupData 𝓘(ℝ, Model) (f.codRestrict AN hf).range where
  X := C
  E' := E
  H' := H
  I' := I
  toHom := f.codRestrict AN hf
  injective _ _ hab := hinj (congrArg Subtype.val hab)
  range_eq := rfl
  isImmersion := isImmersion_codRestrict_posUpperTriangularGroup himm hf

/-- **Exponential coordinates on Lie groups immersed in the positive triangular group.** If a
connected real Lie group `C` has an injective smooth immersive homomorphism into `GL_n(𝕜)` with
values in the positive triangular group, then the exponential of `C` is bijective. -/
theorem lieExp_bijective_of_immersed_posUpperTriangular {f : C →* GL (Fin n) 𝕜}
    (hinj : Injective f) (himm : IsImmersion I 𝓘(ℝ, Mat) ∞ f) (hf : ∀ c, f c ∈ AN) :
    Bijective (lieExp : LeftInvariantDerivation I C → C) :=
  (immersedLieSubgroupDataOfPosUpperTriangular f hinj himm
    hf).lieExp_bijective_of_posUpperTriangular

/-- The exponential of a connected real Lie group immersed in `GL_n(𝕜)` through the positive
triangular group, as a global diffeomorphism. -/
def lieExpDiffeomorphOfImmersedPosUpperTriangular {f : C →* GL (Fin n) 𝕜}
    (hinj : Injective f) (himm : IsImmersion I 𝓘(ℝ, Mat) ∞ f) (hf : ∀ c, f c ∈ AN) :
    Diffeomorph 𝓘(ℝ, LeftInvariantDerivation I C) I (LeftInvariantDerivation I C) C ∞ :=
  (immersedLieSubgroupDataOfPosUpperTriangular f hinj himm
    hf).posUpperTriangularLieExpDiffeomorph

/-- The exponential diffeomorphism of a connected Lie group immersed in `GL_n(𝕜)` through the
positive triangular group is its Lie exponential. -/
@[simp]
theorem lieExpDiffeomorphOfImmersedPosUpperTriangular_apply {f : C →* GL (Fin n) 𝕜}
    (hinj : Injective f) (himm : IsImmersion I 𝓘(ℝ, Mat) ∞ f) (hf : ∀ c, f c ∈ AN)
    (X : LeftInvariantDerivation I C) :
    lieExpDiffeomorphOfImmersedPosUpperTriangular hinj himm hf X = lieExp X :=
  (immersedLieSubgroupDataOfPosUpperTriangular f hinj himm
    hf).posUpperTriangularLieExpDiffeomorph_apply X

omit [T2Space C] in
/-- An injective smooth immersive homomorphism from a connected real Lie group into `GL_n(𝕜)`
with values in the positive triangular group is a closed embedding for the intrinsic topology
of its source. -/
theorem isClosedEmbedding_of_immersed_posUpperTriangular {f : C →* GL (Fin n) 𝕜}
    (hinj : Injective f) (himm : IsImmersion I 𝓘(ℝ, Mat) ∞ f) (hf : ∀ c, f c ∈ AN) :
    Topology.IsClosedEmbedding f :=
  (isClosed_posUpperTriangularGroup (Fin n) 𝕜).isClosedEmbedding_subtypeVal.comp
    (immersedLieSubgroupDataOfPosUpperTriangular f hinj himm
      hf).isClosedEmbedding_toHom_of_posUpperTriangular

omit [T2Space C] in
/-- An injective smooth immersive homomorphism from a connected real Lie group into `GL_n(𝕜)`
with values in the positive triangular group is a smooth embedding. -/
theorem isSmoothEmbedding_of_immersed_posUpperTriangular {f : C →* GL (Fin n) 𝕜}
    (hinj : Injective f) (himm : IsImmersion I 𝓘(ℝ, Mat) ∞ f) (hf : ∀ c, f c ∈ AN) :
    IsSmoothEmbedding I 𝓘(ℝ, Mat) ∞ f :=
  ⟨himm, (isClosedEmbedding_of_immersed_posUpperTriangular hinj himm hf).isEmbedding⟩

end GeneralLinear

end TauCeti.Lie

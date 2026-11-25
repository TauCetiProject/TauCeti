/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.PosUpperTriangular.Immersed
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MaximalCompact
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
global diffeomorphism and `f` is a smooth embedding with closed image. Over `ℂ`, a compact
subgroup of `GL_n(ℂ)` meets the image of `f` only in the identity.

## Main definitions

* `TauCeti.Lie.posUpperTriangularCodRestrict`: the corestriction of `f` to `AN`.
* `TauCeti.Lie.immersedLieSubgroupDataOfPosUpperTriangular`: the presentation of `C` as a
  connected immersed Lie subgroup of `AN`.
* `TauCeti.Lie.lieExpDiffeomorphOfImmersedPositiveTriangular`: the exponential of `C` as a global
  diffeomorphism.

## Main results

* `TauCeti.Lie.isImmersion_posUpperTriangularCodRestrict`: the corestriction is an immersion.
* `TauCeti.Lie.lieExp_bijective_of_immersed_positiveTriangular`: the exponential of `C` is
  bijective.
* `TauCeti.Lie.isSmoothEmbedding_of_immersed_positiveTriangular` and
  `TauCeti.Lie.isClosedEmbedding_of_immersed_positiveTriangular`: `f` is a smooth embedding and a
  closed embedding.
* `TauCeti.Lie.inf_range_eq_bot_of_isCompact_of_positiveTriangular` and
  `TauCeti.Lie.comap_eq_bot_of_isCompact_of_positiveTriangular`: a compact subgroup `K` of
  `GL_n(ℂ)` meets the image of `f` trivially, and its preimage under an injective `f` is trivial.

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

universe u

section GeneralLinear

variable {n : ℕ} {𝕜 : Type u} [RCLike 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {C : Type u} [Group C] [TopologicalSpace C] [ChartedSpace H C] [LieGroup I ∞ C]

local notation "Mat" => Matrix (Fin n) (Fin n) 𝕜
local notation "AN" => posUpperTriangularGroup (Fin n) 𝕜
local notation "Model" => LieSubalgebra.toSubmodule
  (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Mat)) AN)

/-- The inclusion of the positive triangular group into the general linear group is a smooth
embedding for its closed-subgroup smooth structure. -/
theorem isSmoothEmbedding_subtypeVal_posUpperTriangularGroup :
    IsSmoothEmbedding 𝓘(ℝ, Model) 𝓘(ℝ, Mat) ∞ (fun k : AN ↦ (k : GL (Fin n) 𝕜)) :=
  (posUpperTriangularEmbeddedLieSubgroupData (ι := Fin n) (𝕜 := 𝕜)).isSmoothEmbedding_subtypeVal

/-- The corestriction to the positive triangular group `AN` of a homomorphism into `GL_n(𝕜)`
with values in `AN`. -/
abbrev posUpperTriangularCodRestrict (f : C →* GL (Fin n) 𝕜) (hf : ∀ c, f c ∈ AN) : C →* AN :=
  f.codRestrict AN hf

/-- A smooth immersion into `GL_n(𝕜)` with values in the positive triangular group `AN` is a
smooth immersion into `AN`, for the closed-subgroup smooth structure of `AN`. -/
theorem isImmersion_posUpperTriangularCodRestrict {f : C →* GL (Fin n) 𝕜}
    (himm : IsImmersion I 𝓘(ℝ, Mat) ∞ f) (hf : ∀ c, f c ∈ AN) :
    IsImmersion I 𝓘(ℝ, Model) ∞ (posUpperTriangularCodRestrict f hf) := by
  have he := isSmoothEmbedding_subtypeVal_posUpperTriangularGroup (n := n) (𝕜 := 𝕜)
  have hsm : ContMDiff I 𝓘(ℝ, Model) ∞ (posUpperTriangularCodRestrict f hf) :=
    he.contMDiff_iff_comp.2 himm.contMDiff
  refine hsm.isImmersion_of_injective_mfderiv (by simp) fun x ↦ ?_
  have hcomp := mfderiv_comp x (he.contMDiff.mdifferentiable (by simp) _)
    (hsm.mdifferentiable (by simp) x)
  have hinj : Injective ((mfderiv 𝓘(ℝ, Model) 𝓘(ℝ, Mat) (fun k : AN ↦ (k : GL (Fin n) 𝕜))
      (posUpperTriangularCodRestrict f hf x)).comp
      (mfderiv I 𝓘(ℝ, Model) (posUpperTriangularCodRestrict f hf) x)) := by
    rw [← hcomp]
    exact (himm.isImmersionAt x).mfderiv_injective (by simp)
  exact Injective.of_comp (f := ⇑(mfderiv 𝓘(ℝ, Model) 𝓘(ℝ, Mat)
    (fun k : AN ↦ (k : GL (Fin n) 𝕜)) (posUpperTriangularCodRestrict f hf x))) hinj

variable [FiniteDimensional ℝ E] [T2Space C] [ConnectedSpace C]

/-- A connected real Lie group `C` with an injective smooth immersive homomorphism into `GL_n(𝕜)`
with values in the positive triangular group `AN` presents a connected immersed Lie subgroup
of `AN`. -/
def immersedLieSubgroupDataOfPosUpperTriangular (f : C →* GL (Fin n) 𝕜) (hinj : Injective f)
    (himm : IsImmersion I 𝓘(ℝ, Mat) ∞ f) (hf : ∀ c, f c ∈ AN) :
    ImmersedLieSubgroupData 𝓘(ℝ, Model) (posUpperTriangularCodRestrict f hf).range where
  X := C
  E' := E
  H' := H
  I' := I
  toHom := posUpperTriangularCodRestrict f hf
  injective _ _ hab := hinj (congrArg Subtype.val hab)
  range_eq := rfl
  isImmersion := isImmersion_posUpperTriangularCodRestrict himm hf

/-- **Exponential coordinates on Lie groups immersed in the positive triangular group.** If a
connected real Lie group `C` has an injective smooth immersive homomorphism into `GL_n(𝕜)` with
values in the positive triangular group, then the exponential of `C` is bijective. -/
theorem lieExp_bijective_of_immersed_positiveTriangular {f : C →* GL (Fin n) 𝕜}
    (hinj : Injective f) (himm : IsImmersion I 𝓘(ℝ, Mat) ∞ f) (hf : ∀ c, f c ∈ AN) :
    Bijective (lieExp : LeftInvariantDerivation I C → C) :=
  (immersedLieSubgroupDataOfPosUpperTriangular f hinj himm
    hf).lieExp_bijective_of_posUpperTriangular

/-- The exponential of a connected real Lie group immersed in `GL_n(𝕜)` through the positive
triangular group, as a global diffeomorphism. -/
def lieExpDiffeomorphOfImmersedPositiveTriangular {f : C →* GL (Fin n) 𝕜}
    (hinj : Injective f) (himm : IsImmersion I 𝓘(ℝ, Mat) ∞ f) (hf : ∀ c, f c ∈ AN) :
    Diffeomorph 𝓘(ℝ, LeftInvariantDerivation I C) I (LeftInvariantDerivation I C) C ∞ :=
  (immersedLieSubgroupDataOfPosUpperTriangular f hinj himm
    hf).posUpperTriangularLieExpDiffeomorph

/-- The exponential diffeomorphism of a connected Lie group immersed in `GL_n(𝕜)` through the
positive triangular group is its Lie exponential. -/
@[simp]
theorem lieExpDiffeomorphOfImmersedPositiveTriangular_apply {f : C →* GL (Fin n) 𝕜}
    (hinj : Injective f) (himm : IsImmersion I 𝓘(ℝ, Mat) ∞ f) (hf : ∀ c, f c ∈ AN)
    (X : LeftInvariantDerivation I C) :
    lieExpDiffeomorphOfImmersedPositiveTriangular hinj himm hf X = lieExp X :=
  (immersedLieSubgroupDataOfPosUpperTriangular f hinj himm
    hf).posUpperTriangularLieExpDiffeomorph_apply X

omit [T2Space C] in
/-- An injective smooth immersive homomorphism from a connected real Lie group into `GL_n(𝕜)`
with values in the positive triangular group is a closed embedding for the intrinsic topology
of its source. -/
theorem isClosedEmbedding_of_immersed_positiveTriangular {f : C →* GL (Fin n) 𝕜}
    (hinj : Injective f) (himm : IsImmersion I 𝓘(ℝ, Mat) ∞ f) (hf : ∀ c, f c ∈ AN) :
    Topology.IsClosedEmbedding f :=
  (isClosed_posUpperTriangularGroup (Fin n) 𝕜).isClosedEmbedding_subtypeVal.comp
    (immersedLieSubgroupDataOfPosUpperTriangular f hinj himm
      hf).isClosedEmbedding_toHom_of_posUpperTriangular

omit [T2Space C] in
/-- An injective smooth immersive homomorphism from a connected real Lie group into `GL_n(𝕜)`
with values in the positive triangular group is a smooth embedding. -/
theorem isSmoothEmbedding_of_immersed_positiveTriangular {f : C →* GL (Fin n) 𝕜}
    (hinj : Injective f) (himm : IsImmersion I 𝓘(ℝ, Mat) ∞ f) (hf : ∀ c, f c ∈ AN) :
    IsSmoothEmbedding I 𝓘(ℝ, Mat) ∞ f :=
  ⟨himm, (isClosedEmbedding_of_immersed_positiveTriangular hinj himm hf).isEmbedding⟩

omit [T2Space C] in
/-- The image of an injective smooth immersive homomorphism from a connected real Lie group into
`GL_n(𝕜)` with values in the positive triangular group is closed. -/
theorem isClosed_range_of_immersed_positiveTriangular {f : C →* GL (Fin n) 𝕜}
    (hinj : Injective f) (himm : IsImmersion I 𝓘(ℝ, Mat) ∞ f) (hf : ∀ c, f c ∈ AN) :
    IsClosed (range f) :=
  (isClosedEmbedding_of_immersed_positiveTriangular hinj himm hf).isClosed_range

end GeneralLinear

section Compact

variable {n : ℕ} {C : Type*} [Group C]

/-- A compact subgroup `K` of `GL_n(ℂ)` meets the image of a homomorphism with values in the
positive triangular group only in the identity. -/
theorem inf_range_eq_bot_of_isCompact_of_positiveTriangular {K : Subgroup (GL (Fin n) ℂ)}
    (hK : IsCompact (K : Set (GL (Fin n) ℂ))) {f : C →* GL (Fin n) ℂ}
    (hf : ∀ c, f c ∈ posUpperTriangularGroup (Fin n) ℂ) : K ⊓ f.range = ⊥ := by
  refine eq_bot_iff.mpr ((inf_le_inf_left K ?_).trans
    (Matrix.GeneralLinearGroup.inf_posUpperTriangularGroup_eq_bot_of_isCompact hK).le)
  rintro _ ⟨c, rfl⟩
  exact hf c

/-- For an injective homomorphism `f` into `GL_n(ℂ)` with values in the positive triangular
group, the preimage of a compact subgroup is trivial. -/
theorem comap_eq_bot_of_isCompact_of_positiveTriangular {K : Subgroup (GL (Fin n) ℂ)}
    (hK : IsCompact (K : Set (GL (Fin n) ℂ))) {f : C →* GL (Fin n) ℂ} (hinj : Injective f)
    (hf : ∀ c, f c ∈ posUpperTriangularGroup (Fin n) ℂ) : K.comap f = ⊥ := by
  refine eq_bot_iff.mpr fun c hc ↦ Subgroup.mem_bot.mpr (hinj ?_)
  have hmem : f c ∈ K ⊓ f.range := ⟨hc, c, rfl⟩
  rw [inf_range_eq_bot_of_isCompact_of_positiveTriangular hK hf] at hmem
  simpa using hmem

end Compact

end TauCeti.Lie

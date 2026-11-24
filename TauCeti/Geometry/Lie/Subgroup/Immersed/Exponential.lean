/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Immersed.Differential
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Lie.Exponential.Smoothness

/-!
# Exponential coordinates on immersed subgroups of an exponential group

Let `G` be a finite-dimensional real Lie group whose exponential `lieExp : 𝔤 → G` is a global
diffeomorphism, and let `d` present a connected immersed Lie subgroup `K` of `G` by an injective
immersive homomorphism `d.toHom : d.X → G`. Then the exponential of the intrinsic Lie group
`d.X` is a global diffeomorphism as well. No closedness or embeddedness of `K` is assumed: these
are conclusions.

The proof follows the exponential naturality `d.toHom ∘ lieExp = lieExp ∘ d.lieMapToHom`. Its
right side has injective differential, because the ambient exponential is a diffeomorphism and
`d.lieMapToHom` is injective; hence so does the intrinsic exponential, which is therefore a local
diffeomorphism by dimension count and the inverse function theorem. Its range is open. The range
is also closed: it is the preimage under `d.toHom` of the ambient exponential image of the
finite-dimensional subspace `d.lieMapToHom.range`, which is closed since the ambient exponential
is a homeomorphism. Connectedness of `d.X` gives surjectivity, and injectivity of the ambient
exponential gives injectivity.

Consequently `K` is the exponential image of `d.lieMapToHom.range`, it is closed in `G`, and the
presenting homomorphism is a closed embedding for the intrinsic topology of `d.X`.

## Main results

* `TauCeti.Lie.ImmersedLieSubgroupData.t2Space`: the source of a presentation is Hausdorff.
* `TauCeti.Lie.ImmersedLieSubgroupData.isLocalDiffeomorph_lieExp_of_diffeomorph`: the intrinsic
  exponential is a local diffeomorphism.
* `TauCeti.Lie.ImmersedLieSubgroupData.lieExp_bijective_of_diffeomorph`: it is bijective.
* `TauCeti.Lie.ImmersedLieSubgroupData.lieExpDiffeomorphOfDiffeomorph`: the resulting global
  diffeomorphism.
* `TauCeti.Lie.ImmersedLieSubgroupData.coe_eq_image_lieExp_of_diffeomorph`: `K` is the ambient
  exponential image of the differential range.
* `TauCeti.Lie.ImmersedLieSubgroupData.isClosed_of_diffeomorph`: `K` is closed.
* `TauCeti.Lie.ImmersedLieSubgroupData.isClosedEmbedding_toHom_of_diffeomorph`: the presenting
  homomorphism is a closed embedding.
-/

public section

noncomputable section

open Set Function Manifold Module
open scoped ContDiff Manifold Topology

namespace TauCeti.Lie.ImmersedLieSubgroupData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  {K : Subgroup G}

attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

attribute [local instance] ImmersedLieSubgroupData.group
  ImmersedLieSubgroupData.topologicalSpace ImmersedLieSubgroupData.normedAddCommGroup
  ImmersedLieSubgroupData.normedSpace ImmersedLieSubgroupData.finiteDimensional
  ImmersedLieSubgroupData.modelTopology ImmersedLieSubgroupData.chartedSpace
  ImmersedLieSubgroupData.lieGroup ImmersedLieSubgroupData.connectedSpace

/-- The source of an immersed subgroup presentation is Hausdorff, being a Lie group. -/
instance t2Space (d : ImmersedLieSubgroupData I K) : T2Space d.X :=
  d.I'.t2Space_of_lieGroup ∞

/-- The Lie algebra of a finite-dimensional Lie group without boundary is finite-dimensional. -/
private local instance finiteDimensionalLie {E' H' X : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace X] [ChartedSpace H' X] [Group X]
    [LieGroup I' ∞ X] [T2Space X] : FiniteDimensional ℝ (LeftInvariantDerivation I' X) :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

variable (d : ImmersedLieSubgroupData I K)
  (e : Diffeomorph 𝓘(ℝ, LeftInvariantDerivation I G) I (LeftInvariantDerivation I G) G ∞)

/-- The differential of the immersed presentation as a continuous linear map. -/
private def lieMapCLM :
    LeftInvariantDerivation d.I' d.X →L[ℝ] LeftInvariantDerivation I G :=
  d.lieMapToHom.toLinearMap.toContinuousLinearMap

@[simp]
private theorem lieMapCLM_apply (X : LeftInvariantDerivation d.I' d.X) :
    lieMapCLM d X = d.lieMapToHom X := rfl

/-- If the ambient exponential is a diffeomorphism, every differential of the intrinsic
exponential of an immersed subgroup is injective. -/
private theorem injective_mfderiv_lieExp (he : ⇑e = lieExp)
    (X : LeftInvariantDerivation d.I' d.X) :
    Injective (mfderiv 𝓘(ℝ, LeftInvariantDerivation d.I' d.X) d.I' lieExp X) := by
  have hexpX : HasMFDerivAt 𝓘(ℝ, LeftInvariantDerivation d.I' d.X) d.I' lieExp X
      (mfderiv 𝓘(ℝ, LeftInvariantDerivation d.I' d.X) d.I' lieExp X) :=
    ((contMDiff_lieExp (I := d.I') (G := d.X)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hto : HasMFDerivAt d.I' I d.toHom (lieExp X) (mfderiv d.I' I d.toHom (lieExp X)) :=
    (d.contMDiff_toHom.mdifferentiableAt (by simp)).hasMFDerivAt
  have hleft := hto.comp X hexpX
  have he' : HasMFDerivAt 𝓘(ℝ, LeftInvariantDerivation I G) I e (lieMapCLM d X)
      (mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) I e (lieMapCLM d X)) :=
    ((e.contMDiff.mdifferentiableAt (by simp))).hasMFDerivAt
  have hright := he'.comp X (lieMapCLM d).hasMFDerivAt
  have hfun : (⇑d.toHom ∘ lieExp) = ⇑e ∘ ⇑(lieMapCLM d) := by
    funext Y
    simp only [comp_apply, lieMapCLM_apply, he]
    exact d.toHom_lieExp Y
  rw [hfun] at hleft
  have heq := (HasMFDerivAt.mfderiv hleft).symm.trans (HasMFDerivAt.mfderiv hright)
  have hinj : Injective (mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) I e (lieMapCLM d X)) := by
    have h := (e.mfderivToContinuousLinearEquiv (by simp) (lieMapCLM d X)).injective
    rwa [← ContinuousLinearEquiv.coe_coe, Diffeomorph.mfderivToContinuousLinearEquiv_coe] at h
  intro v w hvw
  have h1 := DFunLike.congr_fun heq v
  have h2 := DFunLike.congr_fun heq w
  exact d.injective_lieMapToHom (hinj (h1.symm.trans
    ((congrArg (mfderiv d.I' I d.toHom (lieExp X)) hvw).trans h2)))

/-- **Intrinsic exponentials of immersed subgroups are local diffeomorphisms.** If the
exponential of `G` is a diffeomorphism, then the exponential of every connected immersed Lie
subgroup, for its intrinsic Lie-group structure, is a local diffeomorphism. -/
theorem isLocalDiffeomorph_lieExp_of_diffeomorph (he : ⇑e = lieExp) :
    IsLocalDiffeomorph 𝓘(ℝ, LeftInvariantDerivation d.I' d.X) d.I' ∞
      (lieExp : LeftInvariantDerivation d.I' d.X → d.X) := by
  intro X
  have hdim : finrank ℝ (LeftInvariantDerivation d.I' d.X) =
      finrank ℝ (TangentSpace d.I' (lieExp X : d.X)) :=
    (leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := d.I') (G := d.X)
      ).toLinearEquiv.finrank_eq
  let L := LinearMap.linearEquivOfInjective
    (mfderiv 𝓘(ℝ, LeftInvariantDerivation d.I' d.X) d.I' lieExp X).toLinearMap
    (injective_mfderiv_lieExp d e he X) hdim
  have : CompleteSpace (LeftInvariantDerivation d.I' d.X) := FiniteDimensional.completeSpace ℝ _
  exact TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq (contMDiff_lieExp.contMDiffOn)
    isOpen_univ (mem_univ X) BoundarylessManifold.isInteriorPoint (by simp)
    (e := L.toContinuousLinearEquiv) (by ext; rfl)

/-- The range of the intrinsic exponential is the preimage of the ambient exponential image of
the differential range. -/
private theorem range_lieExp_eq_preimage :
    range (lieExp : LeftInvariantDerivation d.I' d.X → d.X) =
      d.toHom ⁻¹' (lieExp '' (d.lieMapToHom.range : Set (LeftInvariantDerivation I G))) := by
  ext x
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨d.lieMapToHom X, ⟨X, rfl⟩, (d.toHom_lieExp X).symm⟩
  · rintro ⟨_, ⟨X, rfl⟩, hx⟩
    exact ⟨X, d.injective ((d.toHom_lieExp X).trans hx)⟩

/-- **Exponential coordinates on an immersed subgroup.** If the exponential of `G` is a
diffeomorphism, then the exponential of every connected immersed Lie subgroup, for its intrinsic
Lie-group structure, is bijective. -/
theorem lieExp_bijective_of_diffeomorph (he : ⇑e = lieExp) :
    Bijective (lieExp : LeftInvariantDerivation d.I' d.X → d.X) := by
  refine ⟨fun X Y h ↦ ?_, ?_⟩
  · apply d.injective_lieMapToHom
    apply e.injective
    change e _ = e _
    rw [he, ← d.toHom_lieExp, ← d.toHom_lieExp, h]
  · rw [← range_eq_univ]
    have hopen : IsOpen (range (lieExp : LeftInvariantDerivation d.I' d.X → d.X)) :=
      (isLocalDiffeomorph_lieExp_of_diffeomorph d e he).isOpenMap.isOpen_range
    have hclosed : IsClosed (range (lieExp : LeftInvariantDerivation d.I' d.X → d.X)) := by
      rw [range_lieExp_eq_preimage]
      refine IsClosed.preimage d.contMDiff_toHom.continuous ?_
      rw [← he]
      exact e.toHomeomorph.isClosedMap _ (Submodule.isClosed_of_finiteDimensional _)
    exact IsClopen.eq_univ ⟨hclosed, hopen⟩ (range_nonempty _)

/-- The intrinsic exponential of a connected immersed subgroup of a group with exponential
diffeomorphism, as a global diffeomorphism. -/
def lieExpDiffeomorphOfDiffeomorph (he : ⇑e = lieExp) :
    Diffeomorph 𝓘(ℝ, LeftInvariantDerivation d.I' d.X) d.I'
      (LeftInvariantDerivation d.I' d.X) d.X ∞ :=
  (isLocalDiffeomorph_lieExp_of_diffeomorph d e he).diffeomorphOfBijective
    (lieExp_bijective_of_diffeomorph d e he)

/-- The intrinsic exponential diffeomorphism is the intrinsic Lie exponential. -/
@[simp]
theorem lieExpDiffeomorphOfDiffeomorph_apply (he : ⇑e = lieExp)
    (X : LeftInvariantDerivation d.I' d.X) :
    d.lieExpDiffeomorphOfDiffeomorph e he X = lieExp X :=
  congrFun (IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _) X

/-- If the exponential of `G` is a diffeomorphism, a connected immersed Lie subgroup is the
exponential image of its differential range. -/
theorem coe_eq_image_lieExp_of_diffeomorph (he : ⇑e = lieExp) :
    (K : Set G) = lieExp '' (d.lieMapToHom.range : Set (LeftInvariantDerivation I G)) := by
  have hK : (K : Set G) = range d.toHom := by rw [← MonoidHom.coe_range, d.range_eq]
  rw [hK]
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨X, rfl⟩ := (d.lieExp_bijective_of_diffeomorph e he).2 x
    exact ⟨d.lieMapToHom X, ⟨X, rfl⟩, (d.toHom_lieExp X).symm⟩
  · rintro ⟨_, ⟨X, rfl⟩, rfl⟩
    exact ⟨lieExp X, d.toHom_lieExp X⟩

include d in
/-- If the exponential of `G` is a diffeomorphism, every connected immersed Lie subgroup of `G`
is closed. -/
theorem isClosed_of_diffeomorph (he : ⇑e = lieExp) : IsClosed (K : Set G) := by
  rw [d.coe_eq_image_lieExp_of_diffeomorph e he, ← he]
  exact e.toHomeomorph.isClosedMap _ (Submodule.isClosed_of_finiteDimensional _)

/-- If the exponential of `G` is a diffeomorphism, the homomorphism presenting a connected
immersed Lie subgroup is a closed embedding for the intrinsic topology of its source. -/
theorem isClosedEmbedding_toHom_of_diffeomorph (he : ⇑e = lieExp) :
    Topology.IsClosedEmbedding d.toHom := by
  let eX := d.lieExpDiffeomorphOfDiffeomorph e he
  have hfun : ⇑d.toHom = ⇑e ∘ ⇑(lieMapCLM d) ∘ ⇑eX.symm := by
    funext x
    have hx : lieExp (eX.symm x) = x :=
      (lieExpDiffeomorphOfDiffeomorph_apply d e he _).symm.trans (eX.apply_symm_apply x)
    have h : d.toHom (lieExp (eX.symm x)) = lieExp (d.lieMapToHom (eX.symm x)) :=
      d.toHom_lieExp _
    rw [hx] at h
    simp only [comp_apply, lieMapCLM_apply, he]
    exact h
  rw [hfun]
  have hlin : Topology.IsClosedEmbedding (lieMapCLM d) :=
    LinearMap.isClosedEmbedding_of_injective (f := d.lieMapToHom.toLinearMap)
      (LinearMap.ker_eq_bot.mpr d.injective_lieMapToHom)
  exact e.toHomeomorph.isClosedEmbedding.comp (hlin.comp eX.symm.toHomeomorph.isClosedEmbedding)

end TauCeti.Lie.ImmersedLieSubgroupData

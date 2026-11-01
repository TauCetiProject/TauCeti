/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Cotangent bundles of open submanifolds

For an open subset `U` of a manifold `M`, the differential of its inclusion identifies
its tangent spaces with the ambient tangent spaces. Dualizing gives the canonical inclusion
`CotangentBundle.openInclusion : T*U → T*M`. It identifies `T*U` diffeomorphically with the
open inverse image of `U` under the cotangent projection (`CotangentBundle.restrictOpen`).
The pairing formula uses the differential of the base inclusion, so it does not depend on
unfolding the model-space implementation of tangent spaces.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11.
-/

public section

noncomputable section

open Bundle Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace TauCeti.CotangentBundle

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]

/-- Extend a covector on an open submanifold to the ambient tangent space using the
inverse differential of the inclusion. -/
def openInclusion (U : Opens M) (z : CotangentBundle I U) : CotangentBundle I M :=
  TotalSpace.mk' (E →L[𝕜] 𝕜) (z.proj : M)
    (z.2 ∘L (Manifold.tangentSpaceOpenEquiv (I := I) z.proj).symm.toContinuousLinearMap)

/-- The cotangent inclusion covers the inclusion of the open base. -/
@[simp]
theorem proj_openInclusion (U : Opens M) (z : CotangentBundle I U) :
    (openInclusion U z).proj = (z.proj : M) := (rfl)

/-- The ambient covector is evaluated using the inverse tangent-space identification. -/
@[simp]
theorem openInclusion_snd_apply (U : Opens M) (z : CotangentBundle I U)
    (v : TangentSpace I (z.proj : M)) :
    (openInclusion U z).2 v =
      z.2 ((Manifold.tangentSpaceOpenEquiv (I := I) z.proj).symm v) := (rfl)

/-- The cotangent inclusion preserves the covector-vector pairing under the differential
of the inclusion of the base. -/
theorem openInclusion_snd_apply_mfderiv (U : Opens M) (z : CotangentBundle I U)
    (v : TangentSpace I z.proj) :
    (openInclusion U z).2 (mfderiv I I (Subtype.val : U → M) z.proj v) = z.2 v := by
  rw [openInclusion_snd_apply, Manifold.mfderiv_subtype_val]
  exact congrArg z.2 ((Manifold.tangentSpaceOpenEquiv (I := I) z.proj).symm_apply_apply v)

variable [IsManifold I 1 M]

private theorem inCoordinates_open_eventuallyEq (U : Opens M) (x : U) :
    ∀ᶠ y in 𝓝 x, ∀ p : TangentSpace I y →L[𝕜] 𝕜,
      ContinuousLinearMap.inCoordinates E (TangentSpace I : U → Type _) 𝕜
          (Bundle.Trivial U 𝕜) x y x y p =
        ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) 𝕜
          (Bundle.Trivial M 𝕜) (x : M) (y : M) (x : M) (y : M)
          (p ∘L (Manifold.tangentSpaceOpenEquiv (I := I) y).symm.toContinuousLinearMap) := by
  filter_upwards [Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq
    (I := I) x] with y hy
  intro p
  ext v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivial.fiberBundle_trivializationAt', Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [← hy v, ContinuousLinearEquiv.symm_apply_apply]

variable {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
  [TopologicalSpace HX] {IX : ModelWithCorners 𝕜 EX HX}
  [TopologicalSpace X] [ChartedSpace HX X]

/-- Smoothness of a map into `T*U` can be tested after the canonical inclusion into `T*M`. -/
@[simp]
theorem contMDiffAt_openInclusion_iff (U : Opens M) (f : X → CotangentBundle I U) (x : X) :
    ContMDiffAt IX (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) ∞ (openInclusion U ∘ f) x ↔
      ContMDiffAt IX (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) ∞ f x := by
  rw [contMDiffAt_hom_bundle, contMDiffAt_hom_bundle]
  have hb : ContMDiffAt IX I ∞ (fun z ↦ ((f z).proj : M)) x ↔
      ContMDiffAt IX I ∞ (fun z ↦ (f z).proj) x :=
    ContMDiffAt.subtypeVal_comp_iff U _ x
  constructor <;> rintro ⟨hbase, hcoord⟩
  · have hfbase := hb.mp hbase
    refine ⟨hfbase, hcoord.congr_of_eventuallyEq ?_⟩
    filter_upwards [hfbase.continuousAt.eventually
      (inCoordinates_open_eventuallyEq (I := I) U (f x).proj)] with z hz
    exact hz (f z).2
  · refine ⟨hb.mpr hbase, hcoord.congr_of_eventuallyEq ?_⟩
    filter_upwards [hbase.continuousAt.eventually
      (inCoordinates_open_eventuallyEq (I := I) U (f x).proj)] with z hz
    exact (hz (f z).2).symm

/-- The canonical inclusion of the cotangent bundle of an open submanifold is smooth. -/
theorem contMDiff_openInclusion (U : Opens M) :
    ContMDiff (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) ∞
      (openInclusion (I := I) U) :=
  fun z ↦ (contMDiffAt_openInclusion_iff U id z).mpr contMDiffAt_id

/-- The open subset of `T*M` lying over `U`. -/
def overOpen (U : Opens M) : Opens (CotangentBundle I M) :=
  ⟨{z | z.proj ∈ U}, U.isOpen.preimage
    (FiberBundle.continuous_proj (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜))⟩

/-- Membership in the open cotangent restriction is membership of the base point. -/
@[simp]
theorem mem_overOpen (U : Opens M) (z : CotangentBundle I M) :
    z ∈ overOpen (I := I) U ↔ z.proj ∈ U := Iff.rfl

/-- The cotangent bundle of an open submanifold is diffeomorphic to the open part of
the ambient cotangent bundle over that submanifold. -/
def restrictOpen (U : Opens M) :
    CotangentBundle I U ≃ₘ⟮I.prod 𝓘(𝕜, E →L[𝕜] 𝕜), I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)⟯
      overOpen (I := I) U where
  toFun z := ⟨openInclusion U z, z.proj.2⟩
  invFun z := TotalSpace.mk' (E →L[𝕜] 𝕜) (⟨z.val.proj, z.property⟩ : U)
    (z.val.2 ∘L (Manifold.tangentSpaceOpenEquiv (I := I)
      ⟨z.val.proj, z.property⟩).toContinuousLinearMap)
  left_inv z := by
    apply CotangentBundle.ext
    · rfl
    intro v
    exact congrArg z.2 ((Manifold.tangentSpaceOpenEquiv (I := I) z.proj).symm_apply_apply v)
  right_inv z := by
    apply Subtype.ext
    apply CotangentBundle.ext
    · rfl
    intro v
    exact congrArg z.val.2
      ((Manifold.tangentSpaceOpenEquiv (I := I)
          (⟨z.val.proj, z.property⟩ : U)).apply_symm_apply v)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff (overOpen U) _).mp
    (contMDiff_openInclusion U)
  contMDiff_invFun := by
    intro z
    apply (contMDiffAt_openInclusion_iff U _ z).mp
    have heq : (openInclusion U ∘ fun z : overOpen (I := I) U ↦
        TotalSpace.mk' (E →L[𝕜] 𝕜) (⟨z.val.proj, z.property⟩ : U)
          (z.val.2 ∘L (Manifold.tangentSpaceOpenEquiv (I := I)
            ⟨z.val.proj, z.property⟩).toContinuousLinearMap)) = Subtype.val := by
      funext z
      apply CotangentBundle.ext
      · rfl
      intro v
      exact congrArg z.val.2
        ((Manifold.tangentSpaceOpenEquiv (I := I)
          (⟨z.val.proj, z.property⟩ : U)).apply_symm_apply v)
    exact contMDiff_subtype_val.contMDiffAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (congrFun heq))

/-- The restriction identification, viewed in the ambient cotangent bundle, is the canonical
cotangent inclusion. -/
@[simp]
theorem coe_restrictOpen (U : Opens M) (z : CotangentBundle I U) :
    (restrictOpen U z).val = openInclusion U z := (rfl)

/-- The inverse restriction identification covers the identity on the ambient base. -/
@[simp]
theorem proj_restrictOpen_symm (U : Opens M) (z : overOpen (I := I) U) :
    (((restrictOpen U).symm z).proj : M) = z.val.proj := (rfl)

/-- The cotangent inclusion is an open embedding. -/
theorem isOpenEmbedding_openInclusion (U : Opens M) :
    Topology.IsOpenEmbedding (openInclusion (I := I) U) :=
  (overOpen U).isOpenEmbedding'.comp (restrictOpen U).toHomeomorph.isOpenEmbedding

/-- The image of the cotangent inclusion is exactly the part over the open base. -/
@[simp]
theorem range_openInclusion (U : Opens M) :
    Set.range (openInclusion (I := I) U) = overOpen (I := I) U := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact w.proj.property
  · intro hz
    exact ⟨(restrictOpen U).symm ⟨z, hz⟩,
      congrArg Subtype.val ((restrictOpen U).apply_symm_apply ⟨z, hz⟩)⟩

/-- Restricting an ambient covector pairs it with the differential of the base inclusion. -/
theorem restrictOpen_symm_snd_apply (U : Opens M) (z : overOpen (I := I) U)
    (v : TangentSpace I ((restrictOpen U).symm z).proj) :
    ((restrictOpen U).symm z).2 v =
      z.val.2 (mfderiv I I (Subtype.val : U → M) ((restrictOpen U).symm z).proj v) := by
  rw [Manifold.mfderiv_subtype_val]
  rfl

end TauCeti.CotangentBundle

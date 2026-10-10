/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Topology
public import TauCeti.Geometry.Manifold.TubularNeighborhood.NormalFrame

/-!
# Quotient and orthogonal Euclidean normal bundles

The intrinsic normal fibre of an embedding is a quotient of the ambient tangent space.
For an embedding into a real Hilbert space, orthogonal projection selects a unique normal
representative. The quotient topology on the total space, induced by taking normal classes
in the pullback of the ambient tangent bundle (whose total space is identified with `M × V`),
agrees with the subspace topology on the orthogonal normal bundle.

`SmoothEmbedding.normalBundleHomeomorphOrthogonal` establishes this agreement for an embedding
of positive regularity from a finite-dimensional boundaryless manifold. It preserves base points,
is linear on fibres, and sends the zero section to the zero section. Thus the orthogonal
normal-bundle charts can be used for intrinsic normal classes with their quotient topology.

The fibre equivalence reuses Mathlib's `Submodule.quotientEquivOfIsTopCompl`. Continuity of
orthogonal representatives uses `TauCeti.contMDiff_normalSubspace_starProjection`.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the normal-bundle
construction preceding Theorem 6.24.
-/

public section

noncomputable section

open Set Function Topology Bundle
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti.SmoothEmbedding

variable {E V H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

variable [CompleteSpace V]

private theorem isTopCompl_tangentRange_normalSubspace
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (x : M) (hn : n ≠ 0) :
    let A : E →L[ℝ] V := mfderiv I 𝓘(ℝ, V) f x
    Submodule.IsTopCompl A.range (normalSubspace I f x) := by
  let K : Submodule ℝ V := (mfderiv I 𝓘(ℝ, V) f x : E →L[ℝ] V).range
  have hclosed : IsClosed (K : Set V) := f.isClosed_tangentRange x hn
  let : CompleteSpace K := hclosed.completeSpace_coe
  exact K.isTopCompl_orthogonal

/-- Orthogonal representatives identify the quotient normal fibre with the orthogonal
normal subspace, as topological vector spaces. -/
def normalSpaceOrthogonalEquiv (f : SmoothEmbedding I 𝓘(ℝ, V) n M V)
    (x : M) (hn : n ≠ 0) : f.NormalSpace x hn ≃L[ℝ] normalSubspace I f x :=
  let A : E →L[ℝ] V := mfderiv I 𝓘(ℝ, V) f x
  A.range.quotientEquivOfIsTopCompl _ (isTopCompl_tangentRange_normalSubspace f x hn)

/-- The inverse fibre identification takes the normal class of a normal vector. -/
@[simp] theorem normalSpaceOrthogonalEquiv_symm_apply
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (x : M) (hn : n ≠ 0)
    (v : normalSubspace I f x) :
    (f.normalSpaceOrthogonalEquiv x hn).symm v =
      f.normalClass x hn ((NormedSpace.fromTangentSpace (f x)).symm v) := by
  rw [normalClass_def]
  -- In Euclidean tangent coordinates the inverse is Mathlib's quotient map on the
  -- same ambient vector. The casts in the statement make this identification explicit.
  let A : E →L[ℝ] V := mfderiv I 𝓘(ℝ, V) f x
  change (A.range.quotientEquivOfIsTopCompl
    (normalSubspace I f x) (isTopCompl_tangentRange_normalSubspace f x hn)).symm v = _
  exact Submodule.quotientEquivOfIsTopCompl_symm_apply
    (isTopCompl_tangentRange_normalSubspace f x hn) v

/-- The orthogonal representative of an ambient normal class is its normal projection. -/
@[simp] theorem normalSpaceOrthogonalEquiv_normalClass
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (x : M) (hn : n ≠ 0) (v : V) :
    f.normalSpaceOrthogonalEquiv x hn
      (f.normalClass x hn ((NormedSpace.fromTangentSpace (f x)).symm v)) =
      (normalSubspace I f x).orthogonalProjectionOnto v := by
  let K : Submodule ℝ V := (mfderiv I 𝓘(ℝ, V) f x : E →L[ℝ] V).range
  have hclosed : IsClosed (K : Set V) := f.isClosed_tangentRange x hn
  let : CompleteSpace K := hclosed.completeSpace_coe
  apply (f.normalSpaceOrthogonalEquiv x hn).symm.injective
  rw [ContinuousLinearEquiv.symm_apply_apply, normalSpaceOrthogonalEquiv_symm_apply]
  apply (f.normalClass_eq_iff x hn _ _).mpr
  -- The canonical tangent-space identification and the normal quotient use the same
  -- ambient vectors; compare them in the model space where the projections are defined.
  change v - (Kᗮ).starProjection v ∈ K
  simpa only [Submodule.starProjection_orthogonal_val, sub_sub_cancel]
    using K.starProjection_apply_mem v

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 1 M]

/-- The quotient normal bundle and the orthogonal normal bundle have the same topology.
The identification sends each class to its orthogonal representative. -/
def normalBundleHomeomorphOrthogonal (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0) :
    TotalSpace F (fun x => f.NormalSpace x hn) ≃ₜ
      TotalSpace F (fun x => normalSubspace I f x) where
  toFun p := ⟨p.proj, f.normalSpaceOrthogonalEquiv p.proj hn p.2⟩
  invFun p := ⟨p.proj, f.normalClass p.proj hn
    ((NormedSpace.fromTangentSpace (f p.proj)).symm p.2)⟩
  left_inv p := by
    rcases p with ⟨x, v⟩
    simp only [← normalSpaceOrthogonalEquiv_symm_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  right_inv p := by
    rcases p with ⟨x, v⟩
    simp only [← normalSpaceOrthogonalEquiv_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  continuous_toFun := by
    have : IsManifold I ((0 : ℕ∞ω) + 1) M := by simpa using
      (inferInstance : IsManifold I 1 M)
    apply (f.isQuotientMap_normalQuotientMap hn).continuous_iff.mpr
    apply (isEmbedding_totalSpace_normalSubspace (F := F) f).isInducing.continuous_iff.mpr
    have hproj := (contMDiff_normalSubspace_starProjection (n := 0)
      (f.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn))
      (f.isImmersion.mfderiv_injective hn)).continuous
    have hb := Pullback.continuous_proj V (TangentSpace 𝓘(ℝ, V)) (f : M → V)
    have hv := ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, V)).continuous.comp
      (Pullback.continuous_lift V (TangentSpace 𝓘(ℝ, V)) (f : M → V))).snd
    convert hb.prodMk ((hproj.comp hb).clm_apply hv) using 1
    funext p
    simp only [Function.comp_apply]
    rw [normalQuotientMap_apply]
    simp only [tangentBundleModelSpaceHomeomorph_coe, Equiv.coe_fn_mk,
      TotalSpace.toProd, Pullback.lift]
    -- In a Euclidean target the model-space tangent identification is the identity.
    convert congrArg (fun w : normalSubspace I f p.proj => (p.proj, (w : V)))
      (f.normalSpaceOrthogonalEquiv_normalClass p.proj hn (p.2 : V)) using 1 <;> rfl
  continuous_invFun := by
    let L : TotalSpace F (fun x => normalSubspace I f x) →
        TotalSpace V ((f : M → V) *ᵖ (TangentSpace 𝓘(ℝ, V))) := fun p =>
      ⟨p.proj, (NormedSpace.fromTangentSpace (f p.proj)).symm p.2⟩
    have hL : Continuous L := by
      apply (inducing_pullbackTotalSpaceEmbedding V (TangentSpace 𝓘(ℝ, V)) f).continuous_iff.mpr
      have hp := (isEmbedding_totalSpace_normalSubspace (I := I) (F := F) f).continuous
      convert hp.fst.prodMk ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, V)).symm.continuous.comp
        ((f.contMDiff.continuous.comp hp.fst).prodMk hp.snd)) using 1
      -- The pullback lift has the standard model-space tangent coordinates.
      rfl
    convert (f.isQuotientMap_normalQuotientMap (K := F) hn).continuous.comp hL using 1
    funext p
    simp only [Function.comp_apply, normalQuotientMap_apply, L]

/-- The normal-bundle identification takes orthogonal representatives and preserves bases. -/
@[simp] theorem normalBundleHomeomorphOrthogonal_apply
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0)
    (p : TotalSpace F (fun x => f.NormalSpace x hn)) :
    f.normalBundleHomeomorphOrthogonal hn p =
      ⟨p.proj, f.normalSpaceOrthogonalEquiv p.proj hn p.2⟩ := (rfl)

/-- The inverse normal-bundle identification takes the class of the orthogonal vector. -/
@[simp] theorem normalBundleHomeomorphOrthogonal_symm_apply
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0)
    (p : TotalSpace F (fun x => normalSubspace I f x)) :
    (f.normalBundleHomeomorphOrthogonal hn).symm p =
      ⟨p.proj, f.normalClass p.proj hn
        ((NormedSpace.fromTangentSpace (f p.proj)).symm p.2)⟩ := (rfl)

/-- Taking an ambient normal class and then its orthogonal representative is the normal
projection, with the base point fixed. -/
theorem normalBundleHomeomorphOrthogonal_normalQuotientMap
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0)
    (p : TotalSpace V ((f : M → V) *ᵖ (TangentSpace 𝓘(ℝ, V)))) :
    f.normalBundleHomeomorphOrthogonal hn (f.normalQuotientMap (K := F) hn p) =
      ⟨p.1, (normalSubspace I f p.1).orthogonalProjectionOnto p.2⟩ := by
  simp only [normalQuotientMap_apply, normalBundleHomeomorphOrthogonal_apply]
  exact congrArg (TotalSpace.mk p.proj)
    (f.normalSpaceOrthogonalEquiv_normalClass p.proj hn (p.2 : V))

/-- The identification sends the intrinsic zero section to the orthogonal zero section. -/
theorem normalBundleHomeomorphOrthogonal_zeroSection
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (hn : n ≠ 0) (x : M) :
    f.normalBundleHomeomorphOrthogonal hn
      (zeroSection F (fun x => f.NormalSpace x hn) x) =
      zeroSection F (fun x => normalSubspace I f x) x := by
  simp only [zeroSection, normalBundleHomeomorphOrthogonal_apply, map_zero]

/-- The quotient total topology restricts on each fibre to its intrinsic quotient topology. -/
theorem isEmbedding_normalBundle_mk (f : SmoothEmbedding I 𝓘(ℝ, V) n M V)
    (hn : n ≠ 0) (x : M) :
    IsEmbedding (@TotalSpace.mk M F (fun x => f.NormalSpace x hn) x) := by
  apply (f.normalBundleHomeomorphOrthogonal (F := F) hn).isEmbedding.of_comp_iff.mp
  apply (isEmbedding_totalSpace_normalSubspace (F := F) f).of_comp_iff.mp
  convert (isEmbedding_prodMkRight x).comp (Topology.IsEmbedding.subtypeVal.comp
    (f.normalSpaceOrthogonalEquiv x hn).toHomeomorph.isEmbedding) using 1
  funext v
  simp only [Function.comp_apply, normalBundleHomeomorphOrthogonal_apply]
  rfl

end TauCeti.SmoothEmbedding

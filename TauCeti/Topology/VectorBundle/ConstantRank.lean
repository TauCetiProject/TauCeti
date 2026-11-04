/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Splitting.ConstantRank
public import TauCeti.Topology.VectorBundle.Subbundle
public import TauCeti.Topology.VectorBundle.Hom

/-!
# Kernel and image bundles of bundle maps of constant rank

Let `φ x : E₁ x →L[𝕜] E₂ x` be a continuous map between finite-rank vector bundles over a
complete field, continuous as a section of Mathlib's Hom bundle. If its rank is the same number
`r` at every point, then its kernels and its images have continuous local frames near every point
(`TauCeti.hasLocalSubbundleFrames_ker` and `TauCeti.hasLocalSubbundleFrames_range`), with
`finrank F₁ - r` and `r` members respectively. Over `ℝ` or `ℂ` the local frame criterion
`TauCeti.HasLocalSubbundleFrames.vectorBundle` then makes the kernels and the images, with the
subspace topologies of `E₁` and `E₂`, into vector bundles: subbundles of `E₁` and of `E₂`.

The frames are read off from the local matrices of `φ`, its expressions
`ContinuousLinearMap.inCoordinates` in the trivializations of `E₁` and `E₂` at a point. These form
a continuous family of operators (`TauCeti.continuousOn_inCoordinates`) of constant rank
(`ContinuousLinearMap.finrank_range_inCoordinates`) between the model fibres, whose kernels and
ranges move continuously by `ContinuousLinearMap.exists_continuousOn_ker_parametrization` and
`ContinuousLinearMap.exists_continuousOn_range_parametrization`.

A fibrewise surjective map has constant rank `finrank F₂`, and a fibrewise injective map has
constant rank `finrank F₁`. So the kernel of a fibrewise surjection and the image of a fibrewise
injection are subbundles (`TauCeti.hasLocalSubbundleFrames_ker_of_surjective` and
`TauCeti.hasLocalSubbundleFrames_range_of_injective`). In a short exact sequence of bundles these
are the same family of subspaces, the image of the first map and the kernel of the second. A map
whose rank is only locally constant has these frames on each clopen set where the rank takes a
fixed value, by restricting the bundles to that set.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 10.34,
  for the smooth counterpart.
-/

public section

open Bundle Function Module Set Topology

namespace TauCeti

variable {𝕜 B F₁ F₂ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₁ E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {φ : Π x, E₁ x →L[𝕜] E₂ x} {r : ℕ}

/-- **Kernels of a bundle map of constant rank have local frames.** If a continuous bundle map
`φ` between finite-rank vector bundles has rank `r` at every point, then its kernels have
continuous local frames with `finrank F₁ - r` members near every point. Over `ℝ` or `ℂ` they
therefore form a subbundle of `E₁` (`TauCeti.HasLocalSubbundleFrames.vectorBundle`). -/
theorem hasLocalSubbundleFrames_ker
    (hφ : Continuous fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (φ x))
    (hr : ∀ x, finrank 𝕜 (φ x).range = r) :
    HasLocalSubbundleFrames F₁ (Fin (finrank 𝕜 F₁ - r)) fun x ↦ (φ x).ker := by
  refine hasLocalSubbundleFrames_iff.mpr fun x₀ ↦ ?_
  set W := (trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet
  have hx₀ : x₀ ∈ W :=
    ⟨FiberBundle.mem_baseSet_trivializationAt' x₀, FiberBundle.mem_baseSet_trivializationAt' x₀⟩
  obtain ⟨U, hUW, hU, hx₀U, κ, hκ, hκU⟩ :=
    ContinuousLinearMap.exists_continuousOn_ker_parametrization (continuousOn_inCoordinates hφ x₀)
      ((trivializationAt F₁ E₁ x₀).open_baseSet.inter (trivializationAt F₂ E₂ x₀).open_baseSet)
      hx₀ fun x hx ↦ by rw [ContinuousLinearMap.finrank_range_inCoordinates hx.1 hx.2,
        ContinuousLinearMap.finrank_range_inCoordinates hx₀.1 hx₀.2, hr, hr]
  -- The model kernel at `x₀` has dimension `finrank F₁ - r`, by rank–nullity.
  have hdim : finrank 𝕜
      (ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ x₀ x₀ x₀ (φ x₀)).ker =
      finrank 𝕜 F₁ - r := by
    have h := LinearMap.finrank_range_add_finrank_ker
      (ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ x₀ x₀ x₀ (φ x₀) : F₁ →ₗ[𝕜] F₂)
    have h' := ContinuousLinearMap.finrank_range_inCoordinates (ϕ := φ x₀) hx₀.1 hx₀.2
    rw [hr] at h'
    omega
  exact ⟨U, hU, hx₀U, _, Trivialization.isSubbundleFrameOn_symm_comp _
    (hUW.trans inter_subset_left) hκ
    (finBasisOfFinrankEq 𝕜 _ hdim) (fun x hx ↦ (hκU x hx).1) fun x hx v ↦ by
      rw [(hκU x hx).2, ContinuousLinearMap.mem_ker_inCoordinates_iff (hUW hx).1 (hUW hx).2]⟩

/-- **Images of a bundle map of constant rank have local frames.** If a continuous bundle map
`φ` between finite-rank vector bundles has rank `r` at every point, then its images have
continuous local frames with `r` members near every point. Over `ℝ` or `ℂ` they therefore form a
subbundle of `E₂` (`TauCeti.HasLocalSubbundleFrames.vectorBundle`). -/
theorem hasLocalSubbundleFrames_range
    (hφ : Continuous fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (φ x))
    (hr : ∀ x, finrank 𝕜 (φ x).range = r) :
    HasLocalSubbundleFrames F₂ (Fin r) fun x ↦ (φ x).range := by
  refine hasLocalSubbundleFrames_iff.mpr fun x₀ ↦ ?_
  set W := (trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet
  have hx₀ : x₀ ∈ W :=
    ⟨FiberBundle.mem_baseSet_trivializationAt' x₀, FiberBundle.mem_baseSet_trivializationAt' x₀⟩
  obtain ⟨U, hUW, hU, hx₀U, ρ, hρ, hρU⟩ :=
    ContinuousLinearMap.exists_continuousOn_range_parametrization
      (continuousOn_inCoordinates hφ x₀)
      ((trivializationAt F₁ E₁ x₀).open_baseSet.inter (trivializationAt F₂ E₂ x₀).open_baseSet)
      hx₀ fun x hx ↦ by rw [ContinuousLinearMap.finrank_range_inCoordinates hx.1 hx.2,
        ContinuousLinearMap.finrank_range_inCoordinates hx₀.1 hx₀.2, hr, hr]
  have hdim : finrank 𝕜
      (ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ x₀ x₀ x₀ (φ x₀)).range = r := by
    rw [ContinuousLinearMap.finrank_range_inCoordinates hx₀.1 hx₀.2, hr]
  exact ⟨U, hU, hx₀U, _, Trivialization.isSubbundleFrameOn_symm_comp _
    (hUW.trans inter_subset_right) hρ
    (finBasisOfFinrankEq 𝕜 _ hdim) (fun x hx ↦ (hρU x hx).1) fun x hx w ↦ by
      rw [(hρU x hx).2, ContinuousLinearMap.mem_range_inCoordinates_iff (hUW hx).1 (hUW hx).2]⟩

/-- The kernel of a continuous fibrewise surjective bundle map is a subbundle: its kernels have
continuous local frames with `finrank F₁ - finrank F₂` members near every point. -/
theorem hasLocalSubbundleFrames_ker_of_surjective
    (hφ : Continuous fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (φ x))
    (hsurj : ∀ x, Surjective (φ x)) :
    HasLocalSubbundleFrames F₁ (Fin (finrank 𝕜 F₁ - finrank 𝕜 F₂)) fun x ↦ (φ x).ker :=
  hasLocalSubbundleFrames_ker hφ fun x ↦ by
    rw [LinearMap.range_eq_top.mpr (hsurj x), finrank_top,
      ((trivializationAt F₂ E₂ x).continuousLinearEquivAt 𝕜 x
        (FiberBundle.mem_baseSet_trivializationAt' x)).toLinearEquiv.finrank_eq]

/-- The image of a continuous fibrewise injective bundle map is a subbundle: its images have
continuous local frames with `finrank F₁` members near every point. -/
theorem hasLocalSubbundleFrames_range_of_injective
    (hφ : Continuous fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (φ x))
    (hinj : ∀ x, Injective (φ x)) :
    HasLocalSubbundleFrames F₂ (Fin (finrank 𝕜 F₁)) fun x ↦ (φ x).range :=
  hasLocalSubbundleFrames_range hφ fun x ↦ by
    rw [LinearMap.finrank_range_of_inj (hinj x),
      ((trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 x
        (FiberBundle.mem_baseSet_trivializationAt' x)).toLinearEquiv.finrank_eq]

end TauCeti

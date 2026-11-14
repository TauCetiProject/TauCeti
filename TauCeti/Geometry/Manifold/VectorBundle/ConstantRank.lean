/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.ContMDiff.Kernel
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Smooth kernel subbundles of constant-rank bundle maps

A `C^n` bundle map of constant rank between finite-rank bundles has `C^n` local kernel
frames, of size the source rank minus the map rank
(`TauCeti.hasLocalContMDiffSubbundleFrames_ker`). In particular this applies to fibrewise
surjective bundle maps (`TauCeti.hasLocalContMDiffSubbundleFrames_ker_of_surjective`).

Over the real or complex numbers these frames give the kernels, with their subspace topology,
a smooth vector bundle by `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`.
The same API supplies the smooth inclusion and the smoothness criterion for maps into the
kernel. No fibre norms, Hausdorffness of the base, or global trivialization are required.

The construction reads the map in local bundle coordinates and parametrizes its kernels by
the kernel at the centre. Applying that smooth parametrization to a basis gives the frames.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Theorem 10.34.
-/

public section

open Bundle Function Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 EB HB B F₁ F₂ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {I : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₁ E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F₁ E₁ I] [ContMDiffVectorBundle n F₂ E₂ I]
  {φ : Π x, E₁ x →L[𝕜] E₂ x} {r : ℕ}

/-- The kernels of a `C^n` bundle map of constant rank `r` have `C^n` local frames with
`finrank 𝕜 F₁ - r` members. Over `ℝ` or `ℂ` these frames construct a smooth kernel subbundle
with the subspace topology via `HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`. -/
theorem hasLocalContMDiffSubbundleFrames_ker
    (hφ : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (φ x)))
    (hr : ∀ x, finrank 𝕜 (φ x).range = r) :
    HasLocalContMDiffSubbundleFrames I n F₁ (Fin (finrank 𝕜 F₁ - r)) fun x ↦ (φ x).ker := by
  refine hasLocalContMDiffSubbundleFrames_iff.mpr fun x₀ ↦ ?_
  let W := (trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet
  have hW : IsOpen W :=
    (trivializationAt F₁ E₁ x₀).open_baseSet.inter (trivializationAt F₂ E₂ x₀).open_baseSet
  have hx₀ : x₀ ∈ W :=
    ⟨FiberBundle.mem_baseSet_trivializationAt' x₀, FiberBundle.mem_baseSet_trivializationAt' x₀⟩
  -- Read the bundle map in the two preferred trivializations at the centre.
  let A := fun x ↦ ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ x x₀ x (φ x)
  have hA : ContMDiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₂) n A W := by
    let e := trivializationAt (F₁ →L[𝕜] F₂) (fun x ↦ E₁ x →L[𝕜] E₂ x) x₀
    have hWe : W ⊆ e.baseSet := by
      simp only [e, hom_trivializationAt_baseSet, W, subset_refl]
    have h := (e.contMDiffOn_section_iff hW hWe).mp hφ.contMDiffOn
    simpa only [e, hom_trivializationAt_apply] using h
  have hAr (x : B) (hx : x ∈ W) : finrank 𝕜 (A x).range = r := by
    rw [ContinuousLinearMap.finrank_range_inCoordinates hx.1 hx.2, hr]
  have hAk (x : B) (hx : x ∈ W) : finrank 𝕜 (A x).ker = finrank 𝕜 F₁ - r := by
    have h := LinearMap.finrank_range_add_finrank_ker (A x : F₁ →ₗ[𝕜] F₂)
    have h' := hAr x hx
    omega
  obtain ⟨U, hU, hx₀U, hUW, v, hv, hvU⟩ :=
    hA.exists_contMDiffOn_basis_ker hW hAk hx₀
  let e := trivializationAt F₁ E₁ x₀
  -- Transport the coordinate kernel basis back to the ambient bundle.
  have hframes : IsSubbundleFrameOn F₁ (fun x ↦ (φ x).ker)
      (fun i x ↦ e.symm x (v i x)) U := by
    refine ⟨fun i ↦ ((e.contMDiffOn_section_symm hU (hUW.trans inter_subset_left)
      (hv i)).continuousOn), fun {x} hx ↦ ?_, fun {x} hx ↦ ?_⟩
    · simp_rw [← e.linearEquivAt_symm_apply (R := 𝕜) x (hUW hx).1]
      exact (hvU x hx).1.map' (e.linearEquivAt 𝕜 x (hUW hx).1).symm.toLinearMap
        (e.linearEquivAt 𝕜 x (hUW hx).1).symm.ker
    · ext w
      rw [← Function.comp_def (e.symm x) (v · x), Set.range_comp,
        ← e.coe_symmₗ (R := 𝕜) (hUW hx).1, ← Submodule.map_span, (hvU x hx).2]
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [e.symmₗ_apply (R := 𝕜) (hUW hx).1] using
          (ContinuousLinearMap.mem_ker_inCoordinates_iff (ϕ := φ x)
            (hUW hx).1 (hUW hx).2 z).mp hz
      · intro hw
        refine ⟨(e (TotalSpace.mk' F₁ x w)).2, ?_, ?_⟩
        · apply (ContinuousLinearMap.mem_ker_inCoordinates_iff (ϕ := φ x)
            (hUW hx).1 (hUW hx).2 _).mpr
          simpa only [e, Trivialization.symm_apply_apply_mk _ (hUW hx).1] using hw
        · simpa only [e.symmₗ_apply (R := 𝕜) (hUW hx).1] using
            e.symm_apply_apply_mk (hUW hx).1 w
  exact ⟨U, hU, hx₀U, _, hframes, fun i ↦
    e.contMDiffOn_section_symm hU (hUW.trans inter_subset_left) (hv i)⟩

/-- A fibrewise surjective `C^n` bundle map has smooth local kernel frames with
`finrank 𝕜 F₁ - finrank 𝕜 F₂` members. -/
theorem hasLocalContMDiffSubbundleFrames_ker_of_surjective
    (hφ : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (φ x)))
    (hsurj : ∀ x, Surjective (φ x)) :
    HasLocalContMDiffSubbundleFrames I n F₁ (Fin (finrank 𝕜 F₁ - finrank 𝕜 F₂))
      fun x ↦ (φ x).ker :=
  hasLocalContMDiffSubbundleFrames_ker hφ fun x ↦ by
    rw [LinearMap.range_eq_top.mpr (hsurj x), finrank_top,
      ((trivializationAt F₂ E₂ x).continuousLinearEquivAt 𝕜 x
        (FiberBundle.mem_baseSet_trivializationAt' x)).toLinearEquiv.finrank_eq]

end TauCeti

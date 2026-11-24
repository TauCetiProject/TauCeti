/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.Notation
import TauCeti.Geometry.Manifold.ContMDiff.Kernel
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# `C^n` kernel subbundles of constant-rank bundle maps

A `C^n` bundle map of constant rank between finite-rank bundles has `C^n` local kernel
frames, of size the source rank minus the map rank, near every point of an open set on which it
is `C^n` of that rank (`TauCeti.exists_isSubbundleFrameOn_ker`); globally this is
`TauCeti.hasLocalContMDiffSubbundleFrames_ker`. In particular this applies to fibrewise
surjective bundle maps (`TauCeti.exists_isSubbundleFrameOn_ker_of_surjective` and
`TauCeti.hasLocalContMDiffSubbundleFrames_ker_of_surjective`).

Over the real or complex numbers these frames give the kernels, with their subspace topology,
a `C^n` vector bundle by `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`.
The same API supplies the `C^n` inclusion
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_inclusion`) and the `C^n`
criterion for maps into the kernel
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffAt_totalSpace_mk`).
No fibre norms, Hausdorffness of the base, or global trivialization are required.

Bundle maps are supplied as `C^n` sections of Mathlib's Hom bundle. Read in local bundle
coordinates, they become `C^n` families of operators between the model fibres, and the frames
come from `ContMDiffOn.exists_contMDiffOn_basis_ker`.

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

/-- **Local kernel frames of a constant-rank bundle map.** Let `φ` be a bundle map that is `C^n`
on an open set `S` of the base and has rank `r` at every point of `S`. Then every point of `S` has
an open neighbourhood `U ⊆ S` on which the kernels of `φ` have a `C^n` local frame with
`finrank 𝕜 F₁ - r` members. -/
theorem exists_isSubbundleFrameOn_ker {S : Set B} (hS : IsOpen S)
    (hφ : ContMDiffOn I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (φ x)) S)
    (hr : ∀ x ∈ S, finrank 𝕜 (φ x).range = r) {x₀ : B} (hx₀ : x₀ ∈ S) :
    ∃ U ⊆ S, IsOpen U ∧ x₀ ∈ U ∧ ∃ X : Fin (finrank 𝕜 F₁ - r) → Π x, E₁ x,
      IsSubbundleFrameOn F₁ (fun x ↦ (φ x).ker) X U ∧ ∀ i, CMDiff[U] n (T% (X i)) := by
  let W := (trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet ∩ S
  have hW : IsOpen W :=
    ((trivializationAt F₁ E₁ x₀).open_baseSet.inter
      (trivializationAt F₂ E₂ x₀).open_baseSet).inter hS
  have hx₀W : x₀ ∈ W :=
    ⟨⟨FiberBundle.mem_baseSet_trivializationAt' x₀,
      FiberBundle.mem_baseSet_trivializationAt' x₀⟩, hx₀⟩
  -- Read the bundle map in the two preferred trivializations at the centre.
  let A := fun x ↦ ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ x x₀ x (φ x)
  have hA : ContMDiffOn I 𝓘(𝕜, F₁ →L[𝕜] F₂) n A W := by
    let e := trivializationAt (F₁ →L[𝕜] F₂) (fun x ↦ E₁ x →L[𝕜] E₂ x) x₀
    have hWe : W ⊆ e.baseSet := by
      simp only [e, hom_trivializationAt_baseSet, W]
      exact inter_subset_left
    have h := (e.contMDiffOn_section_iff hW hWe).mp (hφ.mono inter_subset_right)
    simpa only [e, hom_trivializationAt_apply] using h
  have hAk (x : B) (hx : x ∈ W) : finrank 𝕜 (A x).ker = finrank 𝕜 F₁ - r := by
    have h := LinearMap.finrank_range_add_finrank_ker (A x : F₁ →ₗ[𝕜] F₂)
    have h' : finrank 𝕜 (A x).range = r := by
      rw [ContinuousLinearMap.finrank_range_inCoordinates hx.1.1 hx.1.2, hr x hx.2]
    omega
  obtain ⟨U, hU, hx₀U, hUW, v, hv, hvU⟩ :=
    hA.exists_contMDiffOn_basis_ker hW hAk hx₀W
  let e := trivializationAt F₁ E₁ x₀
  have hUe : U ⊆ e.baseSet := fun x hx ↦ (hUW hx).1.1
  -- Transport the coordinate kernel basis back to the ambient bundle.
  have hframes : IsSubbundleFrameOn F₁ (fun x ↦ (φ x).ker)
      (fun i x ↦ e.symm x (v i x)) U := by
    refine ⟨fun i ↦ (e.contMDiffOn_section_symm hU hUe (hv i)).continuousOn,
      fun {x} hx ↦ ?_, fun {x} hx ↦ ?_⟩ <;>
    let L := e.linearEquivAt 𝕜 x (hUe hx)
    · simp_rw [← e.linearEquivAt_symm_apply (R := 𝕜) x (hUe hx)]
      exact (hvU x hx).1.map' L.symm.toLinearMap L.symm.ker
    · ext w
      rw [show (fun i ↦ e.symm x (v i x)) = L.symm.toLinearMap ∘ (v · x) by
          funext i
          exact (e.linearEquivAt_symm_apply (R := 𝕜) x (hUe hx) (v i x)).symm,
        Set.range_comp, ← Submodule.map_span, (hvU x hx).2, Submodule.mem_map_equiv,
        LinearEquiv.symm_symm, ContinuousLinearMap.mem_ker_inCoordinates_iff (hUW hx).1.1
          (hUW hx).1.2, e.linearEquivAt_apply, e.symm_apply_apply_mk (hUe hx)]
  exact ⟨U, fun x hx ↦ (hUW hx).2, hU, hx₀U, _, hframes, fun i ↦
    e.contMDiffOn_section_symm hU hUe (hv i)⟩

/-- The kernels of a `C^n` bundle map of constant rank `r` have `C^n` local frames with
`finrank 𝕜 F₁ - r` members. Over `ℝ` or `ℂ` these frames construct a `C^n` kernel subbundle
with the subspace topology via `HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`. -/
theorem hasLocalContMDiffSubbundleFrames_ker
    (hφ : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (φ x)))
    (hr : ∀ x, finrank 𝕜 (φ x).range = r) :
    HasLocalContMDiffSubbundleFrames I n F₁ (Fin (finrank 𝕜 F₁ - r)) fun x ↦ (φ x).ker := by
  refine hasLocalContMDiffSubbundleFrames_iff.mpr fun x₀ ↦ ?_
  obtain ⟨U, -, hU⟩ := exists_isSubbundleFrameOn_ker isOpen_univ hφ.contMDiffOn
    (fun x _ ↦ hr x) (mem_univ x₀)
  exact ⟨U, hU⟩

omit [FiniteDimensional 𝕜 F₂] in
/-- **Local kernel frames of a fibrewise surjective bundle map.** Let `φ` be a bundle map that is
`C^n` and fibrewise surjective on an open set `S` of the base. Then every point of `S` has an open
neighbourhood `U ⊆ S` on which the kernels of `φ` have a `C^n` local frame with
`finrank 𝕜 F₁ - finrank 𝕜 F₂` members. -/
theorem exists_isSubbundleFrameOn_ker_of_surjective {S : Set B} (hS : IsOpen S)
    (hφ : ContMDiffOn I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (φ x)) S)
    (hsurj : ∀ x ∈ S, Surjective (φ x)) {x₀ : B} (hx₀ : x₀ ∈ S) :
    ∃ U ⊆ S, IsOpen U ∧ x₀ ∈ U ∧ ∃ X : Fin (finrank 𝕜 F₁ - finrank 𝕜 F₂) → Π x, E₁ x,
      IsSubbundleFrameOn F₁ (fun x ↦ (φ x).ker) X U ∧ ∀ i, CMDiff[U] n (T% (X i)) := by
  -- The model fibre `F₂` is a linear image of `F₁` through the fibre over `x₀`.
  have : FiniteDimensional 𝕜 F₂ := by
    let L₁ := (trivializationAt F₁ E₁ x₀).linearEquivAt 𝕜 x₀
      (FiberBundle.mem_baseSet_trivializationAt' x₀)
    let L₂ := (trivializationAt F₂ E₂ x₀).linearEquivAt 𝕜 x₀
      (FiberBundle.mem_baseSet_trivializationAt' x₀)
    exact Module.Finite.of_surjective (L₂.toLinearMap ∘ₗ (φ x₀ : E₁ x₀ →ₗ[𝕜] E₂ x₀) ∘ₗ
      L₁.symm.toLinearMap) (L₂.surjective.comp ((hsurj x₀ hx₀).comp L₁.symm.surjective))
  exact exists_isSubbundleFrameOn_ker hS hφ (fun x hx ↦ by
    rw [LinearMap.range_eq_top.mpr (hsurj x hx), finrank_top,
      ((trivializationAt F₂ E₂ x).continuousLinearEquivAt 𝕜 x
        (FiberBundle.mem_baseSet_trivializationAt' x)).toLinearEquiv.finrank_eq]) hx₀

omit [FiniteDimensional 𝕜 F₂] in
/-- A fibrewise surjective `C^n` bundle map has `C^n` local kernel frames with
`finrank 𝕜 F₁ - finrank 𝕜 F₂` members. -/
theorem hasLocalContMDiffSubbundleFrames_ker_of_surjective
    (hφ : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (φ x)))
    (hsurj : ∀ x, Surjective (φ x)) :
    HasLocalContMDiffSubbundleFrames I n F₁ (Fin (finrank 𝕜 F₁ - finrank 𝕜 F₂))
      fun x ↦ (φ x).ker := by
  refine hasLocalContMDiffSubbundleFrames_iff.mpr fun x₀ ↦ ?_
  obtain ⟨U, -, hU⟩ := exists_isSubbundleFrameOn_ker_of_surjective isOpen_univ hφ.contMDiffOn
    (fun x _ ↦ hsurj x) (mem_univ x₀)
  exact ⟨U, hU⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Basic

import TauCeti.Analysis.InnerProductSpace.Adjoint

/-!
# Orthogonal projection and semilinear transport of joint kernels

`LinearMap.orthogonal_iInf_ker_eq_iSup_range_of_isStarNormal` identifies the orthogonal
complement of a joint kernel with the sum of the ranges by
`ContinuousLinearMap.IsStarNormal.orthogonal_range`. An intertwining semilinear map sends
this complement into the target complement by
`LinearMap.orthogonal_iInf_ker_le_comap_of_isStarNormal`, and
`LinearMap.map_orthogonal_iInf_ker_eq_of_isStarNormal` gives equality for surjective maps.

For `Z` contained in the source joint kernel, the projections to `Z` and to the joint kernel
agree on vectors orthogonal to the complement of `Z` inside that kernel. Combining
`Submodule.starProjection_eq_iff_mem_orthogonal_inf` with Mathlib's projection criterion
by the residual gives `LinearMap.map_starProjection_eq_of_intertwining_normal`.
`LinearMap.norm_map_starProjection_le_of_intertwining_normal` then bounds the norm of the
projection measured after transport.

This is the linear-algebra step of `New.DescentPair.normSqAt_starProjection_le` in
`grh/src/New/OneLift/TestedForms.lean` of [grh-lean](https://github.com/lsernau/grh-lean)
at revision `72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open scoped InnerProductSpace

namespace LinearMap

/-- For a family of normal operators on a finite-dimensional inner product space, the
orthogonal complement of the joint kernel is the sum of their ranges. -/
theorem orthogonal_iInf_ker_eq_iSup_range_of_isStarNormal {𝕜 E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {A : ι → E →ₗ[𝕜] E} (hA : ∀ i, IsStarNormal (A i)) :
    (⨅ i, (A i).ker)ᗮ = ⨆ i, (A i).range := by
  have hker (i : ι) : (A i).rangeᗮ = (A i).ker := by
    have := FiniteDimensional.completeSpace 𝕜 E
    have : IsStarNormal (A i) := hA i
    simpa only [coe_toContinuousLinearMap] using ContinuousLinearMap.IsStarNormal.orthogonal_range
      (T := (A i).toContinuousLinearMap) inferInstance
  simp only [← hker, Submodule.iInf_orthogonal, Submodule.orthogonal_orthogonal]

variable {𝕜 𝕝 E F ι : Type*} [RCLike 𝕜] [RCLike 𝕝]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕝 F] [FiniteDimensional 𝕝 F]
  {σ : 𝕜 →+* 𝕝}
  (f : E →ₛₗ[σ] F) {A : ι → E →ₗ[𝕜] E} {B : ι → F →ₗ[𝕝] F}

/-- A semilinear map intertwining two families of normal operators sends the orthogonal
complement of the source joint kernel into the orthogonal complement of the target joint kernel. -/
theorem orthogonal_iInf_ker_le_comap_of_isStarNormal
    (hA : ∀ i, IsStarNormal (A i)) (hB : ∀ i, IsStarNormal (B i))
    (hintertwine : ∀ i x, f (A i x) = B i (f x)) :
    (⨅ i, (A i).ker)ᗮ ≤ ((⨅ i, (B i).ker)ᗮ).comap f := by
  rw [orthogonal_iInf_ker_eq_iSup_range_of_isStarNormal hA,
    orthogonal_iInf_ker_eq_iSup_range_of_isStarNormal hB]
  refine iSup_le fun i y hy ↦ Submodule.mem_comap.mpr ?_
  obtain ⟨x, rfl⟩ := mem_range.mp hy
  rw [hintertwine i x]
  exact le_iSup (fun j ↦ (B j).range) i (mem_range_self _ _)

/-- A surjective semilinear map intertwining two families of normal operators maps the orthogonal
complement of the source joint kernel onto the orthogonal complement of the target joint kernel. -/
theorem map_orthogonal_iInf_ker_eq_of_isStarNormal [RingHomSurjective σ]
    (hf : Function.Surjective f)
    (hA : ∀ i, IsStarNormal (A i)) (hB : ∀ i, IsStarNormal (B i))
    (hintertwine : ∀ i x, f (A i x) = B i (f x)) :
    ((⨅ i, (A i).ker)ᗮ).map f = (⨅ i, (B i).ker)ᗮ := by
  rw [orthogonal_iInf_ker_eq_iSup_range_of_isStarNormal hA,
    orthogonal_iInf_ker_eq_iSup_range_of_isStarNormal hB, Submodule.map_iSup]
  refine congrArg iSup (funext fun i ↦ ?_)
  have hcomp : f.comp (A i) = (B i).comp f := LinearMap.ext (hintertwine i)
  rw [← range_comp, hcomp, range_comp_of_range_eq_top _ (range_eq_top.mpr hf)]

/-- A semilinear map intertwining two families of normal operators carries the projection to
`Z` to the projection to the target joint kernel for vectors orthogonal to the complement of
`Z` inside the source joint kernel. -/
theorem map_starProjection_eq_of_intertwining_normal
    (hA : ∀ i, IsStarNormal (A i)) (hB : ∀ i, IsStarNormal (B i))
    (hintertwine : ∀ i x, f (A i x) = B i (f x)) {Z : Submodule 𝕜 E}
    (hZ : Z ≤ ⨅ i, (A i).ker) {x : E} (hx : x ∈ ((⨅ i, (A i).ker) ⊓ Zᗮ)ᗮ) :
    f (Z.starProjection x) = (⨅ i, (B i).ker).starProjection (f x) := by
  let V : Submodule 𝕜 E := ⨅ i, (A i).ker
  let W : Submodule 𝕝 F := ⨅ i, (B i).ker
  rw [(Submodule.starProjection_eq_iff_mem_orthogonal_inf hZ).mpr hx]
  symm
  refine W.eq_starProjection_of_mem_orthogonal ?_ ?_
  · refine (Submodule.mem_iInf _).mpr fun i ↦ LinearMap.mem_ker.mpr ?_
    rw [← hintertwine, LinearMap.mem_ker.mp
      ((Submodule.mem_iInf _).mp (V.starProjection_apply_mem x) i), map_zero]
  · rw [← map_sub]
    exact Submodule.mem_comap.mp
      (f.orthogonal_iInf_ker_le_comap_of_isStarNormal hA hB hintertwine
        (V.sub_starProjection_mem_orthogonal x))

/-- Projection to `Z` is contractive after semilinear transport intertwining normal operators,
on vectors orthogonal to the complement of `Z` inside their joint kernel. -/
theorem norm_map_starProjection_le_of_intertwining_normal
    (hA : ∀ i, IsStarNormal (A i)) (hB : ∀ i, IsStarNormal (B i))
    (hintertwine : ∀ i x, f (A i x) = B i (f x)) {Z : Submodule 𝕜 E}
    (hZ : Z ≤ ⨅ i, (A i).ker) {x : E} (hx : x ∈ ((⨅ i, (A i).ker) ⊓ Zᗮ)ᗮ) :
    ‖f (Z.starProjection x)‖ ≤ ‖f x‖ := by
  rw [f.map_starProjection_eq_of_intertwining_normal hA hB hintertwine hZ hx]
  exact Submodule.norm_starProjection_apply_le _ _

end LinearMap

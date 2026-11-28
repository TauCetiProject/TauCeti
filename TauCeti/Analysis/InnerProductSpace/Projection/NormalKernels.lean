/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Basic

import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.LinearAlgebra.LinearMap.Ker

/-!
# Orthogonal projection and semilinear transport of joint kernels

For `Z` contained in the source joint kernel, the projections to `Z` and to the joint kernel
agree on vectors orthogonal to the complement of `Z` inside that kernel. Combining
`Submodule.starProjection_eq_iff_mem_orthogonal_inf` with
`LinearMap.map_starProjection_eq_of_le_comap` and the joint-kernel complement transport in
`TauCeti.Analysis.InnerProductSpace.Adjoint` gives
`LinearMap.map_starProjection_eq_of_intertwining_normal`.
`LinearMap.norm_map_starProjection_le_of_intertwining_normal` then bounds the norm of the
projection measured after transport.

This is the linear-algebra step of `New.DescentPair.normSqAt_starProjection_le` in
`grh/src/New/OneLift/TestedForms.lean` of [grh-lean](https://github.com/lsernau/grh-lean)
at revision `72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 𝕝 E F ι : Type*} [RCLike 𝕜] [RCLike 𝕝]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕝 F] [FiniteDimensional 𝕝 F]
  {σ : 𝕜 →+* 𝕝}
  (f : E →ₛₗ[σ] F) {A : ι → E →ₗ[𝕜] E} {B : ι → F →ₗ[𝕝] F}

/-- A semilinear map intertwining two families of normal operators carries the projection to
`Z` to the projection to the target joint kernel for vectors orthogonal to the complement of
`Z` inside the source joint kernel. -/
theorem map_starProjection_eq_of_intertwining_normal
    (hA : ∀ i, IsStarNormal (A i)) (hB : ∀ i, IsStarNormal (B i))
    (hintertwine : ∀ i x, f (A i x) = B i (f x)) {Z : Submodule 𝕜 E}
    (hZ : Z ≤ ⨅ i, (A i).ker) {x : E} (hx : x ∈ ((⨅ i, (A i).ker) ⊓ Zᗮ)ᗮ) :
    f (Z.starProjection x) = (⨅ i, (B i).ker).starProjection (f x) := by
  have hker : (⨅ i, (A i).ker) ≤ (⨅ i, (B i).ker).comap f := by
    intro y hy
    refine Submodule.mem_comap.mpr ((Submodule.mem_iInf _).mpr fun i ↦ ?_)
    have hcomp : f.comp (A i) = (B i).comp f := LinearMap.ext (hintertwine i)
    exact LinearMap.map_mem_ker_of_comp_eq f hcomp ((Submodule.mem_iInf _).mp hy i)
  rw [(Submodule.starProjection_eq_iff_mem_orthogonal_inf hZ).mpr hx]
  exact f.map_starProjection_eq_of_le_comap hker
    (f.orthogonal_iInf_ker_le_comap_of_isStarNormal hA hB hintertwine) x

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

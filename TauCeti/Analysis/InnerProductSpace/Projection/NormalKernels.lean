/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Orthogonal projection and semilinear transport of joint kernels

A semilinear equivalence intertwining two families of normal operators carries the
orthogonal complement of their joint kernel to the orthogonal complement of the new
joint kernel. This follows from the description of those complements as sums of ranges
using `LinearMap.orthogonal_range` and the kernel identities for adjoint products.

If `Z ≤ V` and a vector is orthogonal to `V ⊓ Zᗮ`, its projections to `Z` and `V`
agree. When `V` is the joint kernel, the transported vector's projection to the new
joint kernel therefore computes the transported projection to `Z`. In particular,
projection to `Z` cannot increase the norm measured after transport.
This is `LinearEquiv.norm_map_starProjection_le_of_intertwining_normal`, using
Mathlib's characterization of an orthogonal projection by its residual.

This is the linear-algebra step of `New.DescentPair.normSqAt_starProjection_le` in
`grh/src/New/OneLift/TestedForms.lean` of [grh-lean](https://github.com/lsernau/grh-lean)
at revision `72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open scoped InnerProductSpace

namespace Submodule

/-- For `Z ≤ V`, the projections of `x` onto `Z` and `V` agree exactly when `x` is orthogonal
to the complement of `Z` inside `V`. -/
theorem starProjection_eq_iff_mem_orthogonal_inf {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {Z V : Submodule 𝕜 E}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hZ : Z ≤ V) {x : E} :
    Z.starProjection x = V.starProjection x ↔ x ∈ (V ⊓ Zᗮ)ᗮ := by
  constructor
  · intro h
    have hv := Submodule.orthogonal_le (inf_le_left : V ⊓ Zᗮ ≤ V)
      (V.sub_starProjection_mem_orthogonal x)
    have hz := Submodule.orthogonal_le (inf_le_right : V ⊓ Zᗮ ≤ Zᗮ)
      (Z.le_orthogonal_orthogonal (Z.starProjection_apply_mem x))
    rw [h] at hz
    simpa only [sub_add_cancel] using ((V ⊓ Zᗮ)ᗮ).add_mem hv hz
  · intro hx
    have hV : Z ⊔ (V ⊓ Zᗮ) = V := by
      rw [inf_comm, Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hZ]
    symm
    refine V.eq_starProjection_of_mem_orthogonal (hZ (Z.starProjection_apply_mem x)) ?_
    rw [← hV, ← Submodule.inf_orthogonal]
    refine ⟨Z.sub_starProjection_mem_orthogonal x, Submodule.sub_mem _ hx ?_⟩
    exact Submodule.orthogonal_le inf_le_right
      (Z.le_orthogonal_orthogonal (Z.starProjection_apply_mem x))

end Submodule

namespace LinearMap

/-- For a family of normal operators on a finite-dimensional inner product space, the
orthogonal complement of the joint kernel is the sum of their ranges. -/
theorem orthogonal_iInf_ker_eq_iSup_range_of_isStarNormal {𝕜 E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {A : ι → E →ₗ[𝕜] E} (hA : ∀ i, IsStarNormal (A i)) :
    (⨅ i, (A i).ker)ᗮ = ⨆ i, (A i).range := by
  have hker (i : ι) : (A i).rangeᗮ = (A i).ker := by
    have h := (hA i).star_comm_self.eq
    simp only [star_eq_adjoint, Module.End.mul_eq_comp] at h
    calc
      (A i).rangeᗮ = (A i).adjoint.ker := orthogonal_range _
      _ = ((A i) ∘ₗ (A i).adjoint).ker := (ker_self_comp_adjoint _).symm
      _ = ((A i).adjoint ∘ₗ A i).ker := congrArg LinearMap.ker h.symm
      _ = (A i).ker := ker_adjoint_comp_self _
  simp only [← hker, Submodule.iInf_orthogonal, Submodule.orthogonal_orthogonal]

end LinearMap

namespace LinearEquiv

variable {𝕜 𝕝 E F ι : Type*} [RCLike 𝕜] [RCLike 𝕝]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕝 F] [FiniteDimensional 𝕝 F]
  {σ : 𝕜 →+* 𝕝} {τ : 𝕝 →+* 𝕜} [RingHomInvPair σ τ] [RingHomInvPair τ σ]
  (e : E ≃ₛₗ[σ] F) {A : ι → E →ₗ[𝕜] E} {B : ι → F →ₗ[𝕝] F}

/-- A semilinear equivalence intertwining two families of normal operators transports the
orthogonal complement of the joint kernel. -/
theorem map_orthogonal_iInf_ker_eq_of_isStarNormal
    (hA : ∀ i, IsStarNormal (A i)) (hB : ∀ i, IsStarNormal (B i))
    (hintertwine : ∀ i x, e (A i x) = B i (e x)) :
    ((⨅ i, (A i).ker)ᗮ).map e.toLinearMap = (⨅ i, (B i).ker)ᗮ := by
  rw [LinearMap.orthogonal_iInf_ker_eq_iSup_range_of_isStarNormal hA,
    LinearMap.orthogonal_iInf_ker_eq_iSup_range_of_isStarNormal hB, Submodule.map_iSup]
  congr 1
  funext i
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, (hintertwine i x).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨A i x, ⟨x, rfl⟩, hintertwine i x⟩

/-- A semilinear equivalence intertwining two families of normal operators carries the projection
to `Z` to the projection to the new joint kernel for vectors orthogonal to the complement of
`Z` inside the old joint kernel. -/
theorem map_starProjection_eq_of_intertwining_normal
    (hA : ∀ i, IsStarNormal (A i)) (hB : ∀ i, IsStarNormal (B i))
    (hintertwine : ∀ i x, e (A i x) = B i (e x)) {Z : Submodule 𝕜 E}
    (hZ : Z ≤ ⨅ i, (A i).ker) {x : E} (hx : x ∈ ((⨅ i, (A i).ker) ⊓ Zᗮ)ᗮ) :
    e (Z.starProjection x) = (⨅ i, (B i).ker).starProjection (e x) := by
  let V : Submodule 𝕜 E := ⨅ i, (A i).ker
  let W : Submodule 𝕝 F := ⨅ i, (B i).ker
  rw [(Submodule.starProjection_eq_iff_mem_orthogonal_inf hZ).mpr hx]
  symm
  refine W.eq_starProjection_of_mem_orthogonal ?_ ?_
  · refine (Submodule.mem_iInf _).mpr fun i ↦ LinearMap.mem_ker.mpr ?_
    rw [← hintertwine, LinearMap.mem_ker.mp
      ((Submodule.mem_iInf _).mp (V.starProjection_apply_mem x) i), map_zero]
  · rw [← map_sub, ← e.map_orthogonal_iInf_ker_eq_of_isStarNormal hA hB hintertwine]
    exact Submodule.mem_map_of_mem (V.sub_starProjection_mem_orthogonal x)

/-- Projection to `Z` is contractive after semilinear transport intertwining normal operators,
on vectors orthogonal to the complement of `Z` inside their joint kernel. -/
theorem norm_map_starProjection_le_of_intertwining_normal
    (hA : ∀ i, IsStarNormal (A i)) (hB : ∀ i, IsStarNormal (B i))
    (hintertwine : ∀ i x, e (A i x) = B i (e x)) {Z : Submodule 𝕜 E}
    (hZ : Z ≤ ⨅ i, (A i).ker) {x : E} (hx : x ∈ ((⨅ i, (A i).ker) ⊓ Zᗮ)ᗮ) :
    ‖e (Z.starProjection x)‖ ≤ ‖e x‖ := by
  rw [e.map_starProjection_eq_of_intertwining_normal hA hB hintertwine hZ hx]
  exact Submodule.norm_starProjection_apply_le _ _

end LinearEquiv

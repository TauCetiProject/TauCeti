/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
public import TauCeti.LinearAlgebra.LinearPMap.Restrict

/-!
# Reducing subspaces of partial linear maps

A subspace `U` of an inner-product space, admitting an orthogonal projection `P`, reduces a
partial linear map `A` when `P` maps `dom A` into itself and both `U` and `Uᗮ` are invariant
under `A`. Then every domain vector splits as `P x + (x - P x)` with both summands in the domain,
and `A` acts diagonally with respect to `E = U ⊕ Uᗮ`. For an everywhere-defined map this is
reduction in the sense of `Submodule.IsReducing`.

The reduced part `A.restrict hR.isInvariant : U →ₗ.[𝕜] U` inherits the properties of `A` that
matter for spectral theory: it is densely defined when `A` is, closed when `A` is
(`LinearPMap.IsClosed.restrict`), symmetric when `A` is, and self-adjoint when `A` is. The last
statement is what lets the spectral theory of a self-adjoint operator be split along an
orthogonal decomposition into reducing subspaces.

## Main definitions

* `LinearPMap.IsReducing A U`: the subspace `U` reduces the partial linear map `A`.

## Main results

* `LinearPMap.IsReducing.orthogonal`: if `U` reduces `A`, so does `Uᗮ`.
* `LinearPMap.isReducing_toPMap_top_iff`: for everywhere-defined maps, reduction agrees with
  `Submodule.IsReducing`.
* `LinearPMap.IsReducing.dense_restrict_domain`: the reduced part of a densely defined map is
  densely defined.
* `LinearPMap.IsFormalAdjoint.restrict`: the restriction of a symmetric map to an invariant
  subspace is symmetric.
* `LinearPMap.IsReducing.isSelfAdjoint_restrict`: the reduced part of a self-adjoint map is
  self-adjoint.

## References

K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Section 1.4.
-/

public section

namespace LinearPMap

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A subspace `U` admitting an orthogonal projection reduces a partial linear map `A` when the
orthogonal projection onto `U` maps `dom A` into itself and both `U` and `Uᗮ` are invariant
under `A`. -/
structure IsReducing (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    Prop where
  /-- The orthogonal projection onto `U` preserves the domain. -/
  starProjection_mem_domain {x : E} : x ∈ A.domain → U.starProjection x ∈ A.domain
  /-- The subspace is invariant. -/
  isInvariant : A.IsInvariant U
  /-- The orthogonal complement is invariant. -/
  isInvariant_orthogonal : A.IsInvariant Uᗮ

/-- The restriction of a symmetric partial linear map to an invariant subspace is symmetric. -/
theorem IsFormalAdjoint.restrict {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E}
    (hA : A.IsFormalAdjoint A) (hU : A.IsInvariant U) :
    (A.restrict hU).IsFormalAdjoint (A.restrict hU) := fun x y ↦ by
  simp only [Submodule.coe_inner, coe_restrict_apply]
  exact hA ⟨x, (mem_restrict_domain hU).1 x.2⟩ ⟨y, (mem_restrict_domain hU).1 y.2⟩

variable {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]

/-- The orthogonal projection onto the complement of a reducing subspace preserves the domain. -/
theorem IsReducing.sub_starProjection_mem_domain (hR : A.IsReducing U) {x : E}
    (hx : x ∈ A.domain) : x - U.starProjection x ∈ A.domain :=
  A.domain.sub_mem hx (hR.starProjection_mem_domain hx)

/-- The orthogonal complement of a reducing subspace is reducing. -/
theorem IsReducing.orthogonal (hR : A.IsReducing U) : A.IsReducing Uᗮ where
  starProjection_mem_domain hx := by
    rw [Submodule.starProjection_orthogonal_val]
    exact hR.sub_starProjection_mem_domain hx
  isInvariant := hR.isInvariant_orthogonal
  isInvariant_orthogonal := by
    rw [Submodule.orthogonal_orthogonal]
    exact hR.isInvariant

/-- The orthogonal complement reduces a partial linear map exactly when the subspace does. -/
theorem isReducing_orthogonal_iff : A.IsReducing Uᗮ ↔ A.IsReducing U := by
  refine ⟨fun h ↦ ⟨fun {x} hx ↦ ?_, ?_, h.isInvariant⟩, IsReducing.orthogonal⟩
  · rw [← sub_sub_cancel x (U.starProjection x), ← Submodule.starProjection_orthogonal_val]
    exact h.sub_starProjection_mem_domain hx
  · simpa only [Submodule.orthogonal_orthogonal] using h.isInvariant_orthogonal

/-- For an everywhere-defined linear map, reduction in the sense of partial linear maps is
reduction in the sense of `Submodule.IsReducing`. -/
theorem isReducing_toPMap_top_iff (f : Module.End 𝕜 E) :
    (f.toPMap ⊤).IsReducing U ↔ U.IsReducing f := by
  rw [Submodule.isReducing_iff, ← isInvariant_toPMap_top_iff, ← isInvariant_toPMap_top_iff]
  exact ⟨fun h ↦ ⟨h.isInvariant, h.isInvariant_orthogonal⟩,
    fun h ↦ ⟨fun _ ↦ Submodule.mem_top, h.1, h.2⟩⟩

/-- The reduced part of a densely defined partial linear map is densely defined. -/
theorem IsReducing.dense_restrict_domain (hR : A.IsReducing U) (hA : Dense (A.domain : Set E)) :
    Dense ((A.restrict hR.isInvariant).domain : Set U) := by
  have hP : DenseRange U.orthogonalProjectionOnto :=
    Function.Surjective.denseRange fun v ↦ ⟨v, U.orthogonalProjectionOnto_mem_subspace_eq_self v⟩
  refine (hP.dense_image U.orthogonalProjectionOnto.continuous hA).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_restrict_domain, Submodule.coe_orthogonalProjectionOnto_apply]
  exact hR.starProjection_mem_domain hx

/-- A vector of a reducing subspace in the domain of the adjoint of the reduced part lies in the
domain of the adjoint: for `x ∈ dom A`, the component `x - P x ∈ Uᗮ` is sent into `Uᗮ`, which is
orthogonal to `y`, so only the component `P x` in the domain of the reduced part contributes. -/
private theorem IsReducing.coe_mem_adjoint_domain [CompleteSpace E] {U : Submodule 𝕜 E}
    [CompleteSpace U] (hR : A.IsReducing U) (hA : Dense (A.domain : Set E)) {y : U}
    (hy : y ∈ (A.restrict hR.isInvariant)†.domain) : (y : E) ∈ A†.domain := by
  set z : U := (A.restrict hR.isInvariant)† ⟨y, hy⟩
  refine mem_adjoint_domain_of_exists _ ⟨z, fun x ↦ ?_⟩
  have hp := hR.starProjection_mem_domain x.2
  have hq := hR.sub_starProjection_mem_domain x.2
  have hsplit : A x = A ⟨_, hp⟩ + A ⟨_, hq⟩ := by
    rw [← map_add]
    congr 1
    exact Subtype.ext (add_sub_cancel _ _).symm
  have hzx : ⟪(z : E), (x : E)⟫_𝕜 = ⟪(z : E), U.starProjection x⟫_𝕜 := by
    rw [← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr z.2]
  have hy0 : ⟪(y : E), A ⟨_, hq⟩⟫_𝕜 = 0 :=
    Submodule.inner_right_of_mem_orthogonal y.2
      (hR.isInvariant_orthogonal.apply_mem _ (U.sub_starProjection_mem_orthogonal x))
  have hz := adjoint_isFormalAdjoint (hR.dense_restrict_domain hA) ⟨y, hy⟩
    ⟨⟨_, U.starProjection_apply_mem x⟩, (mem_restrict_domain _).2 hp⟩
  rw [hsplit, inner_add_right, hy0, add_zero, hzx]
  simpa only [Submodule.coe_inner, coe_restrict_apply] using hz

/-- **Reduced parts of self-adjoint operators.** The reduced part of a self-adjoint partial linear
map along a reducing closed subspace is self-adjoint. -/
theorem IsReducing.isSelfAdjoint_restrict [CompleteSpace E] {U : Submodule 𝕜 E}
    [CompleteSpace U] (hR : A.IsReducing U) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (A.restrict hR.isInvariant) := by
  have hB := (hA.isFormalAdjoint.restrict hR.isInvariant).le_adjoint
    (hR.dense_restrict_domain hA.dense_domain)
  rw [isSelfAdjoint_def]
  refine (eq_of_le_of_domain_eq hB (le_antisymm hB.1 fun y hy ↦ ?_)).symm
  have hyA := hR.coe_mem_adjoint_domain hA.dense_domain hy
  rw [isSelfAdjoint_def.mp hA] at hyA
  exact (mem_restrict_domain _).2 hyA

end LinearPMap

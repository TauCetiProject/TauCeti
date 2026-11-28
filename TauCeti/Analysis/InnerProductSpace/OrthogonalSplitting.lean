/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Abel

/-!
# Orthogonal kernel projections and right inverses of a single operator

Given a continuous linear map `T : E →L[𝕜] F` and a continuous linear map `ι : E →L[𝕜] H` into
an inner product space (for example, `ι = id` on a Hilbert space, or the inclusion of a Sobolev
space into `L²`), we characterize:

* `ContinuousLinearMap.IsOrthogonalKerProjection ι T π`: `π` maps `E` into `ker T` with
  `ι (e - π e)` orthogonal to `ι (ker T)`.
* `ContinuousLinearMap.IsOrthogonalRightInverse ι T Q`: `Q` is a right inverse of `T` with
  values `ι`-orthogonal to `ker T`.

For injective `ι`, both are unique (`ContinuousLinearMap.IsOrthogonalKerProjection.unique`,
`ContinuousLinearMap.IsOrthogonalRightInverse.unique`), and yield the splitting `e = π e + Q (T e)`
(`ContinuousLinearMap.IsOrthogonalKerProjection.apply_add_apply_apply_eq_self`). The canonical
operators chosen from these characterizations are `ContinuousLinearMap.orthogonalKerProjection` and
`ContinuousLinearMap.orthogonalRightInverse`. We also record equivariance under linear
equivalences intertwining the kernels and `ι`-pairings
(`ContinuousLinearMap.apply_eq_of_ker_projection_conj`,
`ContinuousLinearMap.apply_eq_of_rightInverse_conj`).
-/

public section

open Function
open scoped InnerProductSpace

namespace ContinuousLinearMap

section SingleOperator

variable {𝕜 E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- If `π` takes values in the kernel of `T` and `R` is a right inverse of `T`, then so is
`R - π R`. -/
theorem rightInverse_sub_comp [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [IsTopologicalAddGroup E] [AddCommGroup F] [Module 𝕜 F]
    {T : E →L[𝕜] F} {π : E →L[𝕜] E} {R : F →L[𝕜] E}
    (hmem : ∀ e, π e ∈ T.ker) (hR : RightInverse R T) : RightInverse (R - π ∘L R) T := fun y ↦ by
  have h0 : T (π (R y)) = 0 := LinearMap.mem_ker.1 (hmem (R y))
  simp [hR y, h0]

/-- Let `ι` be an injective operator into an inner product space. An element of the kernel of `T`
whose image under `ι` is orthogonal to `ι` of the kernel vanishes. -/
theorem eq_zero_of_mem_ker_of_forall_inner_eq_zero {H : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    {ι : E →L[𝕜] H} (hι : Injective ι) {T : E →L[𝕜] F} {w : E} (hw : w ∈ T.ker)
    (h : ∀ k ∈ T.ker, ⟪ι w, ι k⟫_𝕜 = 0) : w = 0 :=
  hι ((inner_self_eq_zero.1 (h w hw)).trans (map_zero ι).symm)

/-- Let `ι` be an injective operator into an inner product space, let `π` take values in the kernel
of `T` with `ι (e - π e)` orthogonal to `ι` of the kernel, and let `Q` be a right inverse of `T`
whose values are `ι`-orthogonal to the kernel. Then every `e` splits as `e = π e + Q (T e)`. -/
theorem apply_add_apply_apply_eq_self {H : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    {ι : E →L[𝕜] H} (hι : Injective ι) {T : E →L[𝕜] F}
    {π : E →L[𝕜] E} {Q : F →L[𝕜] E} (hmem : ∀ e, π e ∈ T.ker)
    (horth : ∀ e, ∀ k ∈ T.ker, ⟪ι (e - π e), ι k⟫_𝕜 = 0) (hQ : RightInverse Q T)
    (hQorth : ∀ y, ∀ k ∈ T.ker, ⟪ι (Q y), ι k⟫_𝕜 = 0) (e : E) : π e + Q (T e) = e := by
  -- The defect `d = e - π e - Q (T e)` lies in the kernel and is `ι`-orthogonal to it.
  set d := e - π e - Q (T e)
  have h0 : T (π e) = 0 := LinearMap.mem_ker.1 (hmem e)
  have hd : d ∈ T.ker := by
    simp [d, hQ (T e), h0]
  have : d = 0 := eq_zero_of_mem_ker_of_forall_inner_eq_zero hι hd fun k hk ↦ by
    rw [map_sub, inner_sub_left, horth e k hk, hQorth _ k hk, sub_zero]
  exact (sub_eq_zero.1 (by simpa only [d, sub_sub] using this)).symm

section Orthogonal

variable {H : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {ι : E →L[𝕜] H} {T : E →L[𝕜] F}

/-- `π` is the projection onto the kernel of `T` along its `ι`-orthogonal complement: it takes
values in the kernel, and `ι (e - π e)` is orthogonal to `ι k` for every `k` in the kernel. -/
structure IsOrthogonalKerProjection (ι : E →L[𝕜] H) (T : E →L[𝕜] F) (π : E →L[𝕜] E) : Prop where
  /-- The projection takes values in the kernel. -/
  mem_ker : ∀ e, π e ∈ T.ker
  /-- The projection is along the `ι`-orthogonal complement of the kernel. -/
  inner_sub_eq_zero : ∀ e, ∀ k ∈ T.ker, ⟪ι (e - π e), ι k⟫_𝕜 = 0

/-- `Q` is a right inverse of `T` whose values are `ι`-orthogonal to the kernel of `T`. -/
structure IsOrthogonalRightInverse (ι : E →L[𝕜] H) (T : E →L[𝕜] F) (Q : F →L[𝕜] E) : Prop where
  /-- `Q` is a right inverse of `T`. -/
  rightInverse : RightInverse Q T
  /-- The values of `Q` are `ι`-orthogonal to the kernel. -/
  inner_eq_zero : ∀ y, ∀ k ∈ T.ker, ⟪ι (Q y), ι k⟫_𝕜 = 0

/-- **Uniqueness of the orthogonal kernel projection.** For an injective `ι` into an inner product
space, two projections onto the kernel of `T` along its `ι`-orthogonal complement agree. -/
theorem IsOrthogonalKerProjection.unique (hι : Injective ι) {π π' : E →L[𝕜] E}
    (h : IsOrthogonalKerProjection ι T π) (h' : IsOrthogonalKerProjection ι T π') : π = π' := by
  ext e
  refine sub_eq_zero.1 (eq_zero_of_mem_ker_of_forall_inner_eq_zero hι
    (T.ker.sub_mem (h.mem_ker e) (h'.mem_ker e)) fun k hk ↦ ?_)
  have hd : π e - π' e = (e - π' e) - (e - π e) := by abel
  rw [hd, map_sub, inner_sub_left, h'.inner_sub_eq_zero e k hk, h.inner_sub_eq_zero e k hk,
    sub_zero]

/-- The orthogonal kernel projection fixes the kernel, for an injective `ι`. -/
theorem IsOrthogonalKerProjection.apply_of_mem_ker (hι : Injective ι) {π : E →L[𝕜] E}
    (h : IsOrthogonalKerProjection ι T π) {k : E} (hk : k ∈ T.ker) : π k = k :=
  (sub_eq_zero.1 (eq_zero_of_mem_ker_of_forall_inner_eq_zero hι
    (T.ker.sub_mem hk (h.mem_ker k)) (h.inner_sub_eq_zero k))).symm

/-- Pairing with the orthogonal kernel projection gives its squared norm:
`⟪ι e, ι (π e)⟫ = ‖ι (π e)‖²`, since `ι (e - π e)` is orthogonal to `ι (π e)`. -/
theorem IsOrthogonalKerProjection.inner_apply_eq_norm_sq {π : E →L[𝕜] E}
    (h : IsOrthogonalKerProjection ι T π) (e : E) :
    ⟪ι e, ι (π e)⟫_𝕜 = (‖ι (π e)‖ : 𝕜) ^ 2 := by
  have h₀ := h.inner_sub_eq_zero e (π e) (h.mem_ker e)
  rw [map_sub, inner_sub_left, sub_eq_zero] at h₀
  rw [h₀, inner_self_eq_norm_sq_to_K]

/-- The real form of `IsOrthogonalKerProjection.inner_apply_eq_norm_sq`, without the coercion:
`⟪ι e, ι (π e)⟫_ℝ = ‖ι (π e)‖²`. -/
theorem IsOrthogonalKerProjection.real_inner_apply_eq_norm_sq [Module ℝ E] [Module ℝ F]
    [InnerProductSpace ℝ H] {ι : E →L[ℝ] H} {T : E →L[ℝ] F} {π : E →L[ℝ] E}
    (h : IsOrthogonalKerProjection ι T π) (e : E) : ⟪ι e, ι (π e)⟫_ℝ = ‖ι (π e)‖ ^ 2 := by
  simpa only [RCLike.ofReal_real_eq_id, id_eq] using h.inner_apply_eq_norm_sq e

/-- **Uniqueness of the orthogonal right inverse.** For an injective `ι` into an inner product
space, two right inverses of `T` whose values are `ι`-orthogonal to the kernel of `T` agree. -/
theorem IsOrthogonalRightInverse.unique (hι : Injective ι) {Q Q' : F →L[𝕜] E}
    (h : IsOrthogonalRightInverse ι T Q) (h' : IsOrthogonalRightInverse ι T Q') : Q = Q' := by
  ext y
  refine sub_eq_zero.1 (eq_zero_of_mem_ker_of_forall_inner_eq_zero (T := T) hι
    (LinearMap.mem_ker.2 (by simp [h.rightInverse y, h'.rightInverse y])) fun k hk ↦ ?_)
  rw [map_sub, inner_sub_left, h.inner_eq_zero y k hk, h'.inner_eq_zero y k hk, sub_zero]

/-- **The orthogonal splitting.** For an injective `ι`, if `π` is the projection onto the kernel
of `T` along its `ι`-orthogonal complement and `Q` is a right inverse of `T` with values in that
complement, then every `e` splits as `e = π e + Q (T e)`. -/
theorem IsOrthogonalKerProjection.apply_add_apply_apply_eq_self (hι : Injective ι)
    {π : E →L[𝕜] E} {Q : F →L[𝕜] E} (hπ : IsOrthogonalKerProjection ι T π)
    (hQ : IsOrthogonalRightInverse ι T Q) (e : E) : π e + Q (T e) = e :=
  ContinuousLinearMap.apply_add_apply_apply_eq_self hι hπ.mem_ker hπ.inner_sub_eq_zero
    hQ.rightInverse hQ.inner_eq_zero e

open Classical in
/-- **The orthogonal kernel projection** of `T` for `ι`: the projection onto the kernel of `T`
along its `ι`-orthogonal complement. It is unique for an injective `ι`
(`ContinuousLinearMap.IsOrthogonalKerProjection.unique`); it is `0` when no such projection
exists. -/
noncomputable def orthogonalKerProjection (ι : E →L[𝕜] H) (T : E →L[𝕜] F) : E →L[𝕜] E :=
  if h : ∃ π, IsOrthogonalKerProjection ι T π then h.choose else 0

open Classical in
/-- **The orthogonal right inverse** of `T` for `ι`: the right inverse of `T` whose values are
`ι`-orthogonal to the kernel of `T`. It is unique for an injective `ι`
(`ContinuousLinearMap.IsOrthogonalRightInverse.unique`); it is `0` when no such right inverse
exists. -/
noncomputable def orthogonalRightInverse (ι : E →L[𝕜] H) (T : E →L[𝕜] F) : F →L[𝕜] E :=
  if h : ∃ Q, IsOrthogonalRightInverse ι T Q then h.choose else 0

/-- Whenever a projection onto the kernel along its `ι`-orthogonal complement exists,
`ContinuousLinearMap.orthogonalKerProjection ι T` is one. -/
theorem IsOrthogonalKerProjection.isOrthogonalKerProjection_orthogonalKerProjection
    {π : E →L[𝕜] E} (h : IsOrthogonalKerProjection ι T π) :
    IsOrthogonalKerProjection ι T (orthogonalKerProjection ι T) := by
  have he : ∃ π, IsOrthogonalKerProjection ι T π := ⟨π, h⟩
  rw [orthogonalKerProjection, dite_eq_left_of_eq_true (eq_true he)]
  exact he.choose_spec

/-- Whenever a right inverse with values `ι`-orthogonal to the kernel exists,
`ContinuousLinearMap.orthogonalRightInverse ι T` is one. -/
theorem IsOrthogonalRightInverse.isOrthogonalRightInverse_orthogonalRightInverse
    {Q : F →L[𝕜] E} (h : IsOrthogonalRightInverse ι T Q) :
    IsOrthogonalRightInverse ι T (orthogonalRightInverse ι T) := by
  have he : ∃ Q, IsOrthogonalRightInverse ι T Q := ⟨Q, h⟩
  rw [orthogonalRightInverse, dite_eq_left_of_eq_true (eq_true he)]
  exact he.choose_spec

/-- For an injective `ι`, a projection onto the kernel of `T` along its `ι`-orthogonal complement
is `ContinuousLinearMap.orthogonalKerProjection ι T`. -/
theorem IsOrthogonalKerProjection.eq_orthogonalKerProjection (hι : Injective ι) {π : E →L[𝕜] E}
    (h : IsOrthogonalKerProjection ι T π) : π = orthogonalKerProjection ι T :=
  h.unique hι h.isOrthogonalKerProjection_orthogonalKerProjection

/-- For an injective `ι`, a right inverse of `T` with values `ι`-orthogonal to the kernel is
`ContinuousLinearMap.orthogonalRightInverse ι T`. -/
theorem IsOrthogonalRightInverse.eq_orthogonalRightInverse (hι : Injective ι) {Q : F →L[𝕜] E}
    (h : IsOrthogonalRightInverse ι T Q) : Q = orthogonalRightInverse ι T :=
  h.unique hι h.isOrthogonalRightInverse_orthogonalRightInverse

end Orthogonal

variable {H E' F' H' : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F]
  [Module 𝕜 F] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [AddCommGroup E'] [Module 𝕜 E']
  [TopologicalSpace E'] [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F']
  [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H'] {ι : E →L[𝕜] H} {ι' : E' →L[𝕜] H'}
  {T : E →L[𝕜] F} {T' : E' →L[𝕜] F'}

/-- An equivalence carrying the kernel of `T` onto the kernel of `T'` and the pairing through `ι`
to the pairing through `ι'` carries vectors `ι`-orthogonal to the kernel of `T` to vectors
`ι'`-orthogonal to the kernel of `T'`. -/
private theorem inner_map_eq_zero_of_ker_conj (e : E ≃ₗ[𝕜] E')
    (hker : ∀ y, e y ∈ T'.ker ↔ y ∈ T.ker)
    (he : ∀ y y', ⟪ι' (e y), ι' (e y')⟫_𝕜 = ⟪ι y, ι y'⟫_𝕜) {y : E}
    (hy : ∀ k ∈ T.ker, ⟪ι y, ι k⟫_𝕜 = 0) {k : E'} (hk : k ∈ T'.ker) :
    ⟪ι' (e y), ι' k⟫_𝕜 = 0 := by
  rw [← e.apply_symm_apply k, he]
  exact hy _ ((hker _).1 (by rwa [e.apply_symm_apply]))

/-- **Orthogonal kernel projections are equivariant.** Let `e : E ≃ₗ[𝕜] E'` carry the kernel of
`T` onto the kernel of `T'` and the pairing through `ι` to the pairing through `ι'`, with `ι'`
injective. If `π` takes values in the kernel of `T` with `ι (y - π y)` orthogonal to `ι` of the
kernel, and `π'` is such a projection for `T'` and `ι'`, then `π' (e y) = e (π y)`. For
`e = LinearEquiv.refl` this is the uniqueness of the projection. No linearity of `π` or `π'` is
assumed. -/
theorem apply_eq_of_ker_projection_conj (hι' : Injective ι') (e : E ≃ₗ[𝕜] E')
    (hker : ∀ y, e y ∈ T'.ker ↔ y ∈ T.ker)
    (he : ∀ y y', ⟪ι' (e y), ι' (e y')⟫_𝕜 = ⟪ι y, ι y'⟫_𝕜) {π : E → E} {π' : E' → E'}
    (hπ : ∀ y, π y ∈ T.ker) (hπo : ∀ y, ∀ k ∈ T.ker, ⟪ι (y - π y), ι k⟫_𝕜 = 0)
    (hπ' : ∀ y, π' y ∈ T'.ker) (hπ'o : ∀ y, ∀ k ∈ T'.ker, ⟪ι' (y - π' y), ι' k⟫_𝕜 = 0)
    (y : E) : π' (e y) = e (π y) := by
  -- The difference lies in the kernel of `T'` and is `ι'`-orthogonal to it.
  refine sub_eq_zero.1 (eq_zero_of_mem_ker_of_forall_inner_eq_zero hι'
    (sub_mem (hπ' _) ((hker _).2 (hπ y))) fun k hk ↦ ?_)
  have h : π' (e y) - e (π y) = e (y - π y) - (e y - π' (e y)) := by
    rw [map_sub]
    abel
  rw [h, map_sub, inner_sub_left, inner_map_eq_zero_of_ker_conj e hker he (hπo y) hk,
    hπ'o _ k hk, sub_zero]

/-- **Orthogonal right inverses are equivariant.** Let `e : E ≃ₗ[𝕜] E'` carry the kernel of `T`
onto the kernel of `T'` and the pairing through `ι` to the pairing through `ι'`, with `ι'`
injective, and let `T' (e y) = σ (T y)`. If `Q` is a right inverse of `T` with values
`ι`-orthogonal to the kernel, and `Q'` such a right inverse of `T'` for `ι'`, then
`Q' (σ f) = e (Q f)`. For `e = LinearEquiv.refl` this is the uniqueness of the right inverse.
No linearity of `Q`, `Q'` or `σ` is assumed. -/
theorem apply_eq_of_rightInverse_conj (hι' : Injective ι') (e : E ≃ₗ[𝕜] E') (σ : F → F')
    (hTe : ∀ y, T' (e y) = σ (T y)) (hker : ∀ y, e y ∈ T'.ker ↔ y ∈ T.ker)
    (he : ∀ y y', ⟪ι' (e y), ι' (e y')⟫_𝕜 = ⟪ι y, ι y'⟫_𝕜) {Q : F → E} {Q' : F' → E'}
    (hQ : ∀ f, T (Q f) = f) (hQo : ∀ f, ∀ k ∈ T.ker, ⟪ι (Q f), ι k⟫_𝕜 = 0)
    (hQ' : ∀ f, T' (Q' f) = f) (hQ'o : ∀ f, ∀ k ∈ T'.ker, ⟪ι' (Q' f), ι' k⟫_𝕜 = 0) (f : F) :
    Q' (σ f) = e (Q f) := by
  -- The difference solves the homogeneous equation and is `ι'`-orthogonal to the kernel.
  refine sub_eq_zero.1 (eq_zero_of_mem_ker_of_forall_inner_eq_zero (T := T') hι' ?_
    fun k hk ↦ ?_)
  · rw [LinearMap.mem_ker, coe_coe, map_sub, hQ', hTe, hQ, sub_self]
  · rw [map_sub, inner_sub_left, hQ'o _ k hk, inner_map_eq_zero_of_ker_conj e hker he (hQo f) hk,
      sub_zero]

end SingleOperator

end ContinuousLinearMap

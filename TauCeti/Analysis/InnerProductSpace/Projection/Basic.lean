/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Products and norms of orthogonal projections

For submodules `U` and `V` of an inner product space admitting orthogonal projections `P_U` and
`P_V`, the two products `P_U P_V` and `P_V P_U` have the same operator norm. Since
`P_V P_U = (P_U P_V)†`, this is the identity `‖T‖ = ‖T†‖`, stated here without any completeness
hypothesis on the ambient space, where the adjoint of a bounded operator need not exist.

A map `T P_U` that factors through the projection onto a finite-dimensional `U` has rank at most
`dim U`. For subspaces `U` and `V` of the same finite dimension, `U ⊓ Vᗮ` and `V ⊓ Uᗮ` have the
same dimension. The orthogonal complement of a nonzero vector has codimension one, and fewer than
`dim E` vectors have a common nonzero orthogonal vector.

For finite-dimensional `U` and `V` with `dim V ≤ dim U`, a lower bound `k ‖u‖² ≤ ‖P_V u‖²` for
`u ∈ U` transfers to the same lower bound `k ‖v‖² ≤ ‖P_U v‖²` for `v ∈ V`.

The projection `P_U v` is the point of `v + Uᗮ` of least norm, and it is the only one: a vector
`w` with `‖w‖ ≤ ‖P_U w‖` equals `P_U w`. Equivalently, `v ∈ U` exactly when adding a vector of
`Uᗮ` never decreases the norm of `v`.

Since the kernel of `P_V` is `Vᗮ`, the projection `P_V` is injective on `U` exactly when no
nonzero vector of `U` is orthogonal to `V`.

Compressing the square of the difference `P_U - P_V` to `U`, from either side, gives
`P_U - P_U P_V P_U`.

A linear map agrees with its composition with the orthogonal projection onto the orthogonal
complement of its kernel whenever the kernel admits an orthogonal projection.

## Provenance

The submodule inclusion-adjoint identity is adapted from
`ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean` in the
AIQ-Kitware DKPS formalization (Apache-2.0; Jon Crall and GPT-6).

## Main results

* `Submodule.adjoint_subtype`: the adjoint of subspace inclusion is orthogonal projection
  onto that subspace.
* `Submodule.adjoint_orthogonalProjectionOnto_toLinearMap`: the adjoint of restricted
  orthogonal projection is subspace inclusion.
* `Submodule.norm_starProjection_comp_starProjection_comm`: `‖P_U P_V‖ = ‖P_V P_U‖`.
* `Submodule.finrank_range_comp_starProjection_le`: `rank (T P_U) ≤ dim U`.
* `Submodule.finrank_inf_orthogonal_comm`: `dim (U ⊓ Vᗮ) = dim (V ⊓ Uᗮ)` when `dim U = dim V`.
* `Submodule.finrank_orthogonal_span_singleton_eq_finrank_sub_one`: `dim (𝕜 ∙ v)ᗮ = dim E - 1`
  for a nonzero vector `v`.
* `TauCeti.exists_ne_zero_forall_inner_eq_zero_of_card_lt_finrank`: fewer than `dim E` vectors
  have a common nonzero orthogonal vector.
* `Submodule.mul_norm_sq_le_norm_starProjection_sq_of_finrank_le`: for finite-dimensional
  subspaces with `dim V ≤ dim U`, a lower bound on `‖P_V u‖²` over `U` transfers to the same
  bound on `‖P_U v‖²` over `V`.
* `Submodule.eq_starProjection_of_norm_le`: a vector whose norm is at most that of its projection
  is its projection.
* `Submodule.mem_iff_forall_mem_orthogonal_norm_le_norm_add`: `v ∈ U` if and only if
  `‖v‖ ≤ ‖v + w‖` for every `w ∈ Uᗮ`.
* `Submodule.injOn_starProjection_iff_disjoint`: `P_V` is injective on `U` if and only if
  `U ⊓ Vᗮ = ⊥`.
* `Submodule.starProjection_sub_starProjection_sq_mul_starProjection`,
  `Submodule.starProjection_mul_starProjection_sub_starProjection_sq`:
  `(P_U - P_V)² P_U = P_U (P_U - P_V)² = P_U - P_U P_V P_U`.
* `LinearMap.apply_sub_starProjection_ker`,
  `ContinuousLinearMap.comp_starProjection_orthogonal_ker`: maps ignore their kernel component.
-/

public section

noncomputable section

namespace Submodule

open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- One half of `norm_starProjection_comp_starProjection_comm`. -/
private theorem norm_starProjection_comp_starProjection_le :
    ‖U.starProjection ∘L V.starProjection‖ ≤ ‖V.starProjection ∘L U.starProjection‖ := by
  -- For `y = P_U P_V x`, `‖y‖² = Re ⟪x, P_V P_U y⟫` because both projections are symmetric and
  -- `P_U y = y`.
  refine opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  set y := U.starProjection (V.starProjection x)
  have hy : U.starProjection y = y := starProjection_eq_self_iff.mpr (U.starProjection_apply_mem _)
  have hinner : ⟪y, y⟫_𝕜 = ⟪x, V.starProjection y⟫_𝕜 :=
    calc ⟪y, y⟫_𝕜 = ⟪V.starProjection x, U.starProjection y⟫_𝕜 :=
          inner_starProjection_left_eq_right U _ _
      _ = ⟪x, V.starProjection y⟫_𝕜 := by rw [hy, inner_starProjection_left_eq_right]
  have key : ‖y‖ * ‖y‖ ≤ ‖V.starProjection ∘L U.starProjection‖ * ‖x‖ * ‖y‖ := by
    calc ‖y‖ * ‖y‖ = RCLike.re ⟪x, V.starProjection y⟫_𝕜 := by
          rw [← inner_self_eq_norm_mul_norm (𝕜 := 𝕜), hinner]
      _ ≤ ‖x‖ * ‖(V.starProjection ∘L U.starProjection) y‖ := by
          rw [comp_apply, hy]
          exact re_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖V.starProjection ∘L U.starProjection‖ * ‖y‖) := by
          gcongr
          exact le_opNorm _ _
      _ = ‖V.starProjection ∘L U.starProjection‖ * ‖x‖ * ‖y‖ := by ring
  rcases (norm_nonneg y).eq_or_lt with h | h
  · rw [comp_apply, ← h]
    positivity
  · exact le_of_mul_le_mul_right key h

/-- The two products of a pair of orthogonal projections have the same operator norm, that is,
`‖T‖ = ‖T†‖` for `T = P_U P_V`. No completeness of `E` is assumed. -/
theorem norm_starProjection_comp_starProjection_comm :
    ‖U.starProjection ∘L V.starProjection‖ = ‖V.starProjection ∘L U.starProjection‖ :=
  (norm_starProjection_comp_starProjection_le U V).antisymm
    (norm_starProjection_comp_starProjection_le V U)

/-- A map `T P_U` that factors through the projection onto `U` has rank at most `dim U`. -/
theorem finrank_range_comp_starProjection_le {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    [FiniteDimensional 𝕜 U] (T : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (LinearMap.range (T ∘ₗ (U.starProjection : E →ₗ[𝕜] E))) ≤
      Module.finrank 𝕜 U := by
  rw [LinearMap.range_comp, range_starProjection]
  exact finrank_map_le _ _

omit [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
/-- For finite-dimensional subspaces of the same dimension, `U ⊓ Vᗮ` and `V ⊓ Uᗮ` have the same
dimension. -/
theorem finrank_inf_orthogonal_comm [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 V]
    (h : Module.finrank 𝕜 U = Module.finrank 𝕜 V) :
    Module.finrank 𝕜 ↥(U ⊓ Vᗮ) = Module.finrank 𝕜 ↥(V ⊓ Uᗮ) := by
  -- `U ⊓ Vᗮ` and `V ⊓ Uᗮ` are the kernels of `P_V|_U : U → V` and of its adjoint `P_U|_V`, and a
  -- map and its adjoint have the same rank.
  have hker (U V : Submodule 𝕜 E) [FiniteDimensional 𝕜 U] [FiniteDimensional 𝕜 V] :
      Module.finrank 𝕜 ↥(U ⊓ Vᗮ) = Module.finrank 𝕜
        (LinearMap.ker (V.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype)) := by
    rw [LinearMap.ker_comp, ← map_comap_subtype, finrank_map_subtype_eq]
    exact congrArg (fun W : Submodule 𝕜 E ↦ Module.finrank 𝕜 (W.comap U.subtype))
      ker_orthogonalProjectionOnto.symm
  let T : U →ₗ[𝕜] V := V.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype
  have hT : T.adjoint = U.orthogonalProjectionOnto.toLinearMap ∘ₗ V.subtype :=
    ((LinearMap.eq_adjoint_iff _ _).2 fun v u ↦ by simp [T]).symm
  have h₁ := T.finrank_range_add_finrank_ker
  have h₂ := T.adjoint.finrank_range_add_finrank_ker
  rw [T.finrank_range_adjoint, hT, ← hker] at h₂
  rw [← hker] at h₁
  omega

/-- In a finite-dimensional inner product space, the orthogonal complement of the span of a
nonzero vector has codimension one. Unlike `Submodule.finrank_orthogonal_span_singleton`, the
dimension of the ambient space is not fixed in advance. -/
theorem finrank_orthogonal_span_singleton_eq_finrank_sub_one [FiniteDimensional 𝕜 E] {v : E}
    (hv : v ≠ 0) : Module.finrank 𝕜 (𝕜 ∙ v)ᗮ = Module.finrank 𝕜 E - 1 := by
  have := Module.finrank_pos_iff_exists_ne_zero (R := 𝕜).2 ⟨v, hv⟩
  exact finrank_add_finrank_orthogonal' <| by rw [finrank_span_singleton hv]; omega

/-- For finite-dimensional subspaces with `dim V ≤ dim U`, a lower bound `k ‖u‖² ≤ ‖P_V u‖²` on
the cosines of `U` towards `V` transfers to the same lower bound for `V` towards `U`. -/
theorem mul_norm_sq_le_norm_starProjection_sq_of_finrank_le [FiniteDimensional 𝕜 U]
    [FiniteDimensional 𝕜 V] (h : Module.finrank 𝕜 V ≤ Module.finrank 𝕜 U) {k : ℝ}
    (hU : ∀ u ∈ U, k * ‖u‖ ^ 2 ≤ ‖V.starProjection u‖ ^ 2) {v : E} (hv : v ∈ V) :
    k * ‖v‖ ^ 2 ≤ ‖U.starProjection v‖ ^ 2 := by
  rcases le_or_gt k 0 with hk | hk
  · exact (mul_nonpos_of_nonpos_of_nonneg hk (sq_nonneg _)).trans (sq_nonneg _)
  -- For `k > 0`, `P_V` maps `U` injectively, so `dim U ≤ dim V`; by the dimension hypothesis the
  -- dimensions agree and `P_V` maps `U` onto `V`.
  let T : U →ₗ[𝕜] V := V.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype
  have hT : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).mpr fun u hu => ?_
    have h0 : V.starProjection u = 0 := by
      simpa [T] using congrArg (Subtype.val : V → E) hu
    have := hU u u.2
    rw [h0, norm_zero, zero_pow two_ne_zero] at this
    have : ‖(u : E)‖ ^ 2 = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right this hk) (sq_nonneg _)
    simpa using this
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (le_antisymm (LinearMap.finrank_le_finrank_of_injective hT) h)).mp hT ⟨v, hv⟩
  have hPw : V.starProjection w = v := by
    simpa [T] using congrArg (Subtype.val : V → E) hw
  -- The preimage `w ∈ U` of `v` gives `‖v‖² = ⟪P_U v, w⟫ ≤ ‖P_U v‖ ‖w‖`.
  have hinner : ‖v‖ ^ 2 ≤ ‖U.starProjection v‖ * ‖(w : E)‖ := by
    have : ⟪U.starProjection v, (w : E)⟫_𝕜 = ⟪v, v⟫_𝕜 := calc
      _ = ⟪v, U.starProjection w⟫_𝕜 := inner_starProjection_left_eq_right U v w
      _ = ⟪V.starProjection v, (w : E)⟫_𝕜 := by
        rw [starProjection_eq_self_iff.mpr w.2, starProjection_eq_self_iff.mpr hv]
      _ = ⟪v, v⟫_𝕜 := by rw [inner_starProjection_left_eq_right, hPw]
    have h := norm_inner_le_norm (𝕜 := 𝕜) (U.starProjection v) (w : E)
    rwa [this, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at h
  -- Combined with `k ‖w‖² ≤ ‖P_V w‖² = ‖v‖²`, this gives `k ‖v‖⁴ ≤ ‖P_U v‖² ‖v‖²`.
  have hw' := hU w w.2
  rw [hPw] at hw'
  rcases (norm_nonneg v).eq_or_lt with hv0 | hv0
  · rw [← hv0, zero_pow two_ne_zero, mul_zero]
    positivity
  have hv2 : 0 < ‖v‖ ^ 2 := by positivity
  nlinarith [norm_nonneg (U.starProjection v), norm_nonneg (w : E),
    mul_le_mul_of_nonneg_left hw' (sq_nonneg ‖U.starProjection v‖),
    pow_le_pow_left₀ (by positivity) hinner 2]

/-- A vector whose norm is at most that of its orthogonal projection onto `U` is that projection,
since the projection never increases the norm and only fixes the norm of vectors of `U`. -/
theorem eq_starProjection_of_norm_le {w : E} (hw : ‖w‖ ≤ ‖U.starProjection w‖) :
    w = U.starProjection w :=
  (starProjection_eq_self_iff.2 ((U.mem_iff_norm_starProjection w).2
    ((U.norm_starProjection_apply_le w).antisymm hw))).symm

/-- A vector lies in `U` if and only if adding a vector of `Uᗮ` never decreases its norm. -/
theorem mem_iff_forall_mem_orthogonal_norm_le_norm_add {v : E} :
    v ∈ U ↔ ∀ w ∈ Uᗮ, ‖v‖ ≤ ‖v + w‖ := by
  refine ⟨fun hv w hw ↦ ?_, fun h ↦ ?_⟩
  · -- Pythagoras: `‖v + w‖² = ‖v‖² + ‖w‖²`.
    refine (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2 ?_
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero v w
      (inner_right_of_mem_orthogonal hv hw)]
    exact le_add_of_nonneg_right (mul_self_nonneg _)
  · have hle := h _ (sub_mem_comm_iff.1 (U.sub_starProjection_mem_orthogonal v))
    rw [add_sub_cancel] at hle
    rw [U.eq_starProjection_of_norm_le hle]
    exact U.starProjection_apply_mem v

omit [U.HasOrthogonalProjection] in
/-- The orthogonal projection onto `V` is injective on `U` exactly when `U ⊓ Vᗮ = ⊥`, since its
kernel is `Vᗮ`. -/
theorem injOn_starProjection_iff_disjoint :
    Set.InjOn V.starProjection U ↔ Disjoint U Vᗮ := by
  simpa using (LinearMap.disjoint_ker_iff_injOn (f := (V.starProjection : E →ₗ[𝕜] E))
    (p := U)).symm

/-- Compressing `(P_U - P_V)²` to `U` on the right gives `P_U - P_U P_V P_U`. -/
theorem starProjection_sub_starProjection_sq_mul_starProjection :
    (U.starProjection - V.starProjection) ^ 2 * U.starProjection =
      U.starProjection - U.starProjection * V.starProjection * U.starProjection := by
  have hP := U.isIdempotentElem_starProjection
  have hQ := V.isIdempotentElem_starProjection
  simp only [sq, sub_mul, mul_sub, mul_assoc, hP.eq, hQ.mul_self_mul]
  abel

/-- Compressing `(P_U - P_V)²` to `U` on the left gives `P_U - P_U P_V P_U`. -/
theorem starProjection_mul_starProjection_sub_starProjection_sq :
    U.starProjection * (U.starProjection - V.starProjection) ^ 2 =
      U.starProjection - U.starProjection * V.starProjection * U.starProjection := by
  have hP := U.isIdempotentElem_starProjection
  have hQ := V.isIdempotentElem_starProjection
  simp only [sq, sub_mul, mul_sub, mul_assoc, hP.eq, hQ.eq, hP.mul_self_mul]
  abel

/-- The adjoint of the inclusion `U → E` is the orthogonal projection `E → U`.
Both maps are regarded as finite-dimensional algebraic linear maps. -/
@[simp]
theorem adjoint_subtype [FiniteDimensional 𝕜 E] :
    LinearMap.adjoint U.subtype = U.orthogonalProjectionOnto.toLinearMap := by
  rw [eq_comm]
  apply (LinearMap.eq_adjoint_iff
    U.orthogonalProjectionOnto.toLinearMap U.subtype).2
  intro x y
  -- Identify the ambient action of the restricted orthogonal projection with
  -- `starProjection`; the inner-product identity is then a projection property.
  change ⟪U.starProjection x, (y : E)⟫_𝕜 = ⟪x, (y : E)⟫_𝕜
  rw [U.inner_starProjection_left_eq_right,
    U.starProjection_eq_self_iff.mpr y.2]

/-- The algebraic adjoint of the orthogonal projection `E → U` is the inclusion `U → E`.
This is the elementary simplification rule for the adjoints of cross-projections and
self-adjoint compressions, together with `LinearMap.adjoint_comp`. -/
@[simp]
theorem adjoint_orthogonalProjectionOnto_toLinearMap [FiniteDimensional 𝕜 E] :
    LinearMap.adjoint U.orthogonalProjectionOnto.toLinearMap = U.subtype := by
  rw [← U.adjoint_subtype, LinearMap.adjoint_adjoint]

end Submodule

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Fewer than `dim E` vectors have a common nonzero orthogonal vector: the orthogonal complement
of their span is nontrivial. -/
theorem exists_ne_zero_forall_inner_eq_zero_of_card_lt_finrank (s : Finset E)
    (hs : s.card < Module.finrank 𝕜 E) : ∃ e : E, e ≠ 0 ∧ ∀ u ∈ s, ⟪u, e⟫_𝕜 = 0 := by
  have : FiniteDimensional 𝕜 E := Module.finite_of_finrank_pos (by omega)
  set K := Submodule.span 𝕜 (s : Set E)
  have hK : Module.finrank 𝕜 K < Module.finrank 𝕜 E := (finrank_span_finset_le_card s).trans_lt hs
  obtain ⟨e, he, he₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := Kᗮ) fun h ↦ by
    have := K.finrank_add_finrank_orthogonal
    rw [h, finrank_bot] at this
    omega
  exact ⟨e, he₀, fun u hu ↦ Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span hu) he⟩

end TauCeti

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F]

/-- A linear map does not see the component of a vector in its kernel. -/
@[simp]
theorem apply_sub_starProjection_ker (u : E →ₗ[𝕜] F) [u.ker.HasOrthogonalProjection]
    (x : E) : u (x - u.ker.starProjection x) = u x := by
  have hx := Submodule.starProjection_apply_mem u.ker x
  rw [mem_ker] at hx
  simpa only [map_add, hx, add_zero] using
    congrArg u (sub_add_cancel x (u.ker.starProjection x))

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

/-- Composing a continuous linear map with the orthogonal projection onto the orthogonal
complement of its kernel does not change it. -/
@[simp]
theorem comp_starProjection_orthogonal_ker (u : E →L[𝕜] F) [u.ker.HasOrthogonalProjection] :
    u ∘L u.kerᗮ.starProjection = u := by
  ext x
  simpa only [comp_apply, Submodule.starProjection_orthogonal_val, coe_coe] using
    u.toLinearMap.apply_sub_starProjection_ker x

end ContinuousLinearMap

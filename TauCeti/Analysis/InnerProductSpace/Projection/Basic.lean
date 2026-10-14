/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Norms of orthogonal projections

For submodules `U` and `V` of an inner product space admitting orthogonal projections `P_U` and
`P_V`, the two products `P_U P_V` and `P_V P_U` have the same operator norm. Since
`P_V P_U = (P_U P_V)†`, this is the identity `‖T‖ = ‖T†‖`, stated here without any completeness
hypothesis on the ambient space, where the adjoint of a bounded operator need not exist.

For finite-dimensional `U` and `V` with `dim V ≤ dim U`, a lower bound `k ‖u‖² ≤ ‖P_V u‖²` for
`u ∈ U` transfers to the same lower bound `k ‖v‖² ≤ ‖P_U v‖²` for `v ∈ V`.

The projection `P_U v` is the point of `v + Uᗮ` of least norm, and it is the only one: a vector
`w` with `‖w‖ ≤ ‖P_U w‖` equals `P_U w`. Equivalently, `v ∈ U` exactly when adding a vector of
`Uᗮ` never decreases the norm of `v`.

## Main results

* `Submodule.norm_starProjection_comp_starProjection_comm`: `‖P_U P_V‖ = ‖P_V P_U‖`.
* `Submodule.mul_norm_sq_le_norm_starProjection_sq_of_finrank_le`: for finite-dimensional
  subspaces with `dim V ≤ dim U`, a lower bound on `‖P_V u‖²` over `U` transfers to the same
  bound on `‖P_U v‖²` over `V`.
* `Submodule.eq_starProjection_of_norm_le`: a vector whose norm is at most that of its projection
  is its projection.
* `Submodule.mem_iff_forall_mem_orthogonal_norm_le_norm_add`: `v ∈ U` if and only if
  `‖v‖ ≤ ‖v + w‖` for every `w ∈ Uᗮ`.
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

/-- A vector differs from its orthogonal projection onto `U` by a vector of `Uᗮ`; this is
`Submodule.sub_starProjection_mem_orthogonal` with the difference taken the other way. -/
theorem starProjection_sub_mem_orthogonal (v : E) : U.starProjection v - v ∈ Uᗮ := by
  rw [← neg_mem_iff, neg_sub]
  exact U.sub_starProjection_mem_orthogonal v

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
  · have hle := h _ (U.starProjection_sub_mem_orthogonal v)
    rw [add_sub_cancel] at hle
    rw [U.eq_starProjection_of_norm_le hle]
    exact U.starProjection_apply_mem v

end Submodule

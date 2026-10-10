/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The gap between two subspaces

For submodules `U` and `V` of an inner product space admitting orthogonal projections `P_U` and
`P_V`, the *gap* between `U` and `V` is the operator norm `‖P_U - P_V‖`, and the *directed gap*
from `U` to `V` is `‖P_{Vᗮ} P_U‖`, which measures how far vectors of `U` of norm at most one can
stick out of `V`. The gap is symmetric, bounded by `1`, and vanishes exactly when `U = V`; it is
the quantity in which perturbation bounds for spectral subspaces are stated.

The main result is the sharp identity
`‖P_U - P_V‖ = max ‖P_{Vᗮ} P_U‖ ‖P_{Uᗮ} P_V‖`, with no completeness or dimension hypothesis.
It reduces gap estimates to estimates of the two directed gaps, and identifies the gap as a
measure of how far each subspace sticks out of the other.

## Main definitions

* `Submodule.projectionGap U V`: the gap `‖P_U - P_V‖`.
* `Submodule.directedProjectionGap U V`: the directed gap `‖P_{Vᗮ} P_U‖`.

## Main results

* `Submodule.norm_starProjection_comp_starProjection_comm`: `‖P_U P_V‖ = ‖P_V P_U‖`.
* `Submodule.projectionGap_comm`: the gap is symmetric.
* `Submodule.directedProjectionGap_le_projectionGap`: each directed gap is at most the gap.
* `Submodule.projectionGap_eq_max`: the gap is the larger of the two directed gaps.
* `Submodule.directedProjectionGap_eq_zero_iff`: the directed gap from `U` to `V` vanishes
  exactly when `U ≤ V`; consequently `Submodule.projectionGap_eq_zero_iff`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), §I.6.8.
* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970).
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

/-- The gap `‖P_U - P_V‖` between two subspaces with orthogonal projections. -/
def projectionGap : ℝ :=
  ‖U.starProjection - V.starProjection‖

/-- The directed gap `‖P_{Vᗮ} P_U‖` from `U` to `V`: the supremum of the norm of the component
orthogonal to `V` of a vector of `U` with norm at most one. -/
def directedProjectionGap : ℝ :=
  ‖Vᗮ.starProjection ∘L U.starProjection‖

theorem projectionGap_def :
    projectionGap U V = ‖U.starProjection - V.starProjection‖ := (rfl)

theorem directedProjectionGap_def :
    directedProjectionGap U V = ‖Vᗮ.starProjection ∘L U.starProjection‖ := (rfl)

theorem projectionGap_nonneg : 0 ≤ projectionGap U V :=
  norm_nonneg _

theorem directedProjectionGap_nonneg : 0 ≤ directedProjectionGap U V :=
  norm_nonneg _

/-- The gap is symmetric. -/
theorem projectionGap_comm : projectionGap U V = projectionGap V U :=
  norm_sub_rev _ _

@[simp]
theorem projectionGap_self : projectionGap U U = 0 := by
  simp [projectionGap]

/-- Passing to orthogonal complements preserves the gap. -/
@[simp]
theorem projectionGap_orthogonal : projectionGap Uᗮ Vᗮ = projectionGap U V := by
  rw [projectionGap, starProjection_orthogonal', starProjection_orthogonal',
    sub_sub_sub_cancel_left, projectionGap_comm, projectionGap]

/-- Passing to orthogonal complements reverses the directed gap. -/
@[simp]
theorem directedProjectionGap_orthogonal :
    directedProjectionGap Vᗮ Uᗮ = directedProjectionGap U V := by
  rw [directedProjectionGap, directedProjectionGap, starProjection_orthogonal' Uᗮ,
    starProjection_orthogonal' U, sub_sub_cancel, norm_starProjection_comp_starProjection_comm]

/-- The directed gap from `U` to `V` is at most the gap. -/
theorem directedProjectionGap_le_projectionGap :
    directedProjectionGap U V ≤ projectionGap U V := by
  -- `P_{Vᗮ} P_U = P_{Vᗮ} (P_U - P_V)`, and `P_{Vᗮ}` has norm at most one.
  have h : Vᗮ.starProjection ∘L U.starProjection =
      Vᗮ.starProjection ∘L (U.starProjection - V.starProjection) := by
    rw [comp_sub, (isOrtho_orthogonal_left V).starProjection_comp_starProjection, sub_zero]
  rw [directedProjectionGap, h]
  exact (opNorm_comp_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (starProjection_norm_le _))

/-- The directed gap from `U` to `V` is at most `1`. -/
theorem directedProjectionGap_le_one : directedProjectionGap U V ≤ 1 :=
  (opNorm_comp_le _ _).trans <| (mul_le_mul (starProjection_norm_le _)
    (starProjection_norm_le _) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)

/-- **The sharp projection-gap identity**: the gap between two subspaces is the larger of the two
directed gaps, `‖P_U - P_V‖ = max ‖P_{Vᗮ} P_U‖ ‖P_{Uᗮ} P_V‖`. -/
theorem projectionGap_eq_max :
    projectionGap U V = max (directedProjectionGap U V) (directedProjectionGap V U) := by
  -- Each directed term is a compression of `P_U - P_V`, which gives the lower bound. For the
  -- upper bound, `P_U - P_V = P_{Vᗮ} P_U - P_V P_{Uᗮ}`, where the two terms take values in the
  -- orthogonal subspaces `Vᗮ` and `V` and act on the orthogonal components `P_U x` and
  -- `P_{Uᗮ} x`, so the Pythagorean theorem applies; the adjoint-free identity
  -- `‖P_U P_V‖ = ‖P_V P_U‖` handles the second term.
  refine le_antisymm ?_ (max_le (directedProjectionGap_le_projectionGap U V)
    (projectionGap_comm U V ▸ directedProjectionGap_le_projectionGap V U))
  set m := max (directedProjectionGap U V) (directedProjectionGap V U)
  have hm : 0 ≤ m := le_max_of_le_left (directedProjectionGap_nonneg U V)
  refine opNorm_le_bound _ hm fun x => ?_
  -- Split `(P_U - P_V) x = s - t` with `s = P_{Vᗮ} P_U x ∈ Vᗮ` and `t = P_V P_{Uᗮ} x ∈ V`.
  set s := Vᗮ.starProjection (U.starProjection x)
  set t := V.starProjection (Uᗮ.starProjection x)
  have hsplit : (U.starProjection - V.starProjection) x = s - t := by
    simp only [s, t, sub_apply, starProjection_orthogonal_val, map_sub]
    abel
  have horth : ⟪s, t⟫_𝕜 = 0 :=
    inner_left_of_mem_orthogonal (V.starProjection_apply_mem _) (Vᗮ.starProjection_apply_mem _)
  -- `s` is the directed sine map of `U` applied to `P_U x`, and `t` the adjoint directed sine map
  -- of `V` applied to `P_{Uᗮ} x`.
  have hs : ‖s‖ ≤ m * ‖U.starProjection x‖ := by
    have : s = (Vᗮ.starProjection ∘L U.starProjection) (U.starProjection x) := by
      rw [comp_apply, starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)]
    rw [this]
    exact (le_opNorm _ _).trans (by gcongr; exact le_max_left _ _)
  have ht : ‖t‖ ≤ m * ‖Uᗮ.starProjection x‖ := by
    have : t = (V.starProjection ∘L Uᗮ.starProjection) (Uᗮ.starProjection x) := by
      rw [comp_apply, starProjection_eq_self_iff.mpr (Uᗮ.starProjection_apply_mem x)]
    rw [this]
    refine (le_opNorm _ _).trans ?_
    rw [norm_starProjection_comp_starProjection_comm]
    gcongr
    exact le_max_right _ _
  have hsq : ‖(U.starProjection - V.starProjection) x‖ ^ 2 ≤ (m * ‖x‖) ^ 2 := by
    calc ‖(U.starProjection - V.starProjection) x‖ ^ 2 = ‖s‖ ^ 2 + ‖t‖ ^ 2 := by
          rw [hsplit, norm_sub_eq_norm_add (inner_eq_zero_symm.mp horth), sq, sq, sq,
            norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth]
      _ ≤ (m * ‖U.starProjection x‖) ^ 2 + (m * ‖Uᗮ.starProjection x‖) ^ 2 := by
          gcongr
      _ = (m * ‖x‖) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, ← mul_add, ← norm_sq_eq_add_norm_sq_starProjection]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- The gap between two subspaces is at most `1`. -/
theorem projectionGap_le_one : projectionGap U V ≤ 1 := by
  rw [projectionGap_eq_max]
  exact max_le (directedProjectionGap_le_one U V) (directedProjectionGap_le_one V U)

/-- The directed gap from `U` to `V` vanishes exactly when `U` is contained in `V`. -/
@[simp]
theorem directedProjectionGap_eq_zero_iff : directedProjectionGap U V = 0 ↔ U ≤ V := by
  rw [directedProjectionGap, norm_eq_zero, starProjection_comp_starProjection_eq_zero_iff,
    isOrtho_comm, isOrtho_iff_le, orthogonal_orthogonal]

/-- The gap between `U` and `V` vanishes exactly when `U = V`. -/
@[simp]
theorem projectionGap_eq_zero_iff : projectionGap U V = 0 ↔ U = V := by
  rw [projectionGap_eq_max, le_antisymm_iff (b := V)]
  simp only [← directedProjectionGap_eq_zero_iff]
  constructor
  · intro h
    exact ⟨le_antisymm (h ▸ le_max_left _ _) (directedProjectionGap_nonneg U V),
      le_antisymm (h ▸ le_max_right _ _) (directedProjectionGap_nonneg V U)⟩
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂, max_self]

end Submodule

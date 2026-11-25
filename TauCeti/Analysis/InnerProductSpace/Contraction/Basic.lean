/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Contractions that preserve the norm of a vector

Let `S : E →L[𝕜] F` be a contraction from an inner product space, and let `u` be a vector whose
norm `S` preserves. Then the functional `re ⟪·, u⟫` is dominated by `‖u‖` times the seminorm
`x ↦ ‖S x‖`: the unit ball of this seminorm contains the Euclidean unit ball and touches its
boundary at `u / ‖u‖`, so the Euclidean support functional at that point also supports it.

These are the inequalities satisfied at the contact points of John's position; see
`TauCeti.Analysis.InnerProductSpace.JohnEllipsoid`.

## Main statements

* `ContinuousLinearMap.re_inner_le_norm_mul_norm_apply`: if `‖S‖ ≤ 1` and `‖S u‖ = ‖u‖`, then
  `re ⟪x, u⟫ ≤ ‖u‖ * ‖S x‖` for all `x`.
* `ContinuousLinearMap.norm_inner_le_norm_mul_norm_apply`: under the same hypotheses,
  `‖⟪u, x⟫‖ ≤ ‖u‖ * ‖S x‖`.
* `ContinuousLinearMap.norm_comp_id_sub_smul_le`: the perturbation estimate behind John's
  theorem, bounding the norm of `S ∘ (1 - δ H)` for a contraction `S` and small `δ > 0`.

## References

* K. Ball, *An Elementary Introduction to Modern Convex Geometry*, Lecture 3.
-/

public section

open Filter Topology ComplexConjugate

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open RCLike in
/-- If a contraction `S` from an inner product space preserves the norm of `u`, then
`re ⟪x, u⟫ ≤ ‖u‖ * ‖S x‖` for every `x`. For a unit vector `u` with `‖S u‖ = 1`, the functional
`re ⟪·, u⟫` is thus a support functional at `u` of the unit ball of the seminorm `x ↦ ‖S x‖`
(a norm when `S` is injective), which contains the Euclidean unit ball and touches its boundary
at `u`. -/
theorem re_inner_le_norm_mul_norm_apply {S : E →L[𝕜] F} (hS : ‖S‖ ≤ 1) {u : E}
    (hu : ‖S u‖ = ‖u‖) (x : E) : re ⟪x, u⟫ ≤ ‖u‖ * ‖S x‖ := by
  set v := x - u
  -- For `0 < t ≤ 1`, the point `u + t v` lies on the segment from `u` to `x`, while `u - t v`
  -- is controlled by the Euclidean norm; their sum is `2 u`. This gives an inequality whose
  -- error term `t * ‖v‖ ^ 2 / 2` vanishes as `t → 0`.
  have key : ∀ t : ℝ, 0 < t → t < 1 → re ⟪x, u⟫ - t * ‖v‖ ^ 2 / 2 ≤ ‖u‖ * ‖S x‖ := by
    intro t ht₀ ht₁
    have h₁ : ‖S (u - (t : 𝕜) • v)‖ ≤ ‖u - (t : 𝕜) • v‖ :=
      (S.le_of_opNorm_le hS _).trans_eq (one_mul _)
    have h₂ : ‖S (u + (t : 𝕜) • v)‖ ≤ (1 - t) * ‖u‖ + t * ‖S x‖ := by
      have : u + (t : 𝕜) • v = ((1 - t : ℝ) : 𝕜) • u + (t : 𝕜) • x := by
        simp only [v, smul_sub, ofReal_sub, ofReal_one, sub_smul, one_smul]
        abel
      rw [this, map_add, map_smul, map_smul]
      refine (norm_add_le _ _).trans_eq ?_
      rw [norm_smul, norm_smul, norm_ofReal, norm_ofReal, abs_of_pos (sub_pos.2 ht₁),
        abs_of_pos ht₀, hu]
    have h₃ : 2 * ‖u‖ ≤ ‖S (u + (t : 𝕜) • v)‖ + ‖S (u - (t : 𝕜) • v)‖ := by
      calc 2 * ‖u‖ = ‖S (u + (t : 𝕜) • v) + S (u - (t : 𝕜) • v)‖ := by
            rw [← map_add, add_add_sub_cancel, ← two_smul 𝕜, map_smul, norm_smul, hu]
            simp
        _ ≤ _ := norm_add_le _ _
    have h₄ : ‖u - (t : 𝕜) • v‖ ^ 2 = ‖u‖ ^ 2 - 2 * t * re ⟪u, v⟫ + t ^ 2 * ‖v‖ ^ 2 := by
      rw [@norm_sub_sq 𝕜, inner_smul_right, re_ofReal_mul, norm_smul, norm_ofReal,
        abs_of_pos ht₀]
      ring
    have h₅ : re ⟪x, u⟫ = ‖u‖ ^ 2 + re ⟪u, v⟫ := by
      rw [← inner_re_symm, show x = u + v by simp [v], inner_add_right, map_add,
        inner_self_eq_norm_sq]
    have h₆ : t * (re ⟪x, u⟫ - t * ‖v‖ ^ 2 / 2) ≤ t * (‖u‖ * ‖S x‖) := by
      nlinarith [norm_nonneg u, norm_nonneg (u - (t : 𝕜) • v),
        sq_nonneg (‖u‖ - ‖u - (t : 𝕜) • v‖)]
    exact le_of_mul_le_mul_left h₆ ht₀
  have hlim : Tendsto (fun t : ℝ ↦ re ⟪x, u⟫ - t * ‖v‖ ^ 2 / 2) (𝓝[>] 0) (𝓝 (re ⟪x, u⟫)) := by
    have : Continuous fun t : ℝ ↦ re ⟪x, u⟫ - t * ‖v‖ ^ 2 / 2 := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim <| by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht using key t ht.1 ht.2

open RCLike in
/-- If a contraction `S` from an inner product space preserves the norm of `u`, then
`‖⟪u, x⟫‖ ≤ ‖u‖ * ‖S x‖` for every `x`. In particular, the contact points `u` of a
maximal-volume ellipsoid `T` satisfy `‖⟪u, x⟫‖ ≤ ‖T x‖`. -/
theorem norm_inner_le_norm_mul_norm_apply {S : E →L[𝕜] F} (hS : ‖S‖ ≤ 1) {u : E}
    (hu : ‖S u‖ = ‖u‖) (x : E) : ‖⟪u, x⟫‖ ≤ ‖u‖ * ‖S x‖ := by
  rw [norm_inner_symm]
  -- Rotate `x` by a unit scalar `conj c` with `c * ⟪x, u⟫ = ‖⟪x, u⟫‖`, so that the rotated inner
  -- product `⟪conj c • x, u⟫ = c * ⟪x, u⟫` is real.
  obtain ⟨c, hc, hcz⟩ := exists_norm_eq_mul_self ⟪x, u⟫
  have h := S.re_inner_le_norm_mul_norm_apply hS hu (conj c • x)
  rwa [inner_smul_left, conj_conj, ← hcz, ofReal_re, map_smul, norm_smul, norm_conj, hc,
    one_mul] at h

open RCLike in
/-- The perturbation estimate behind John's theorem: if a contraction `S` has norm at most `1 - r`
on the unit vectors `x` with `re ⟪x, H x⟫ ≤ s`, then `S ∘ (1 - δ H)` has norm at most
`1 - δ s / 2` for small `δ > 0`. Near the remaining unit vectors `1 - δ H` itself shrinks the norm,
since `‖x - δ H x‖² = 1 - 2 δ re ⟪x, H x⟫ + δ² ‖H x‖²`. -/
theorem norm_comp_id_sub_smul_le {S : E →L[𝕜] F} (hS : ‖S‖ ≤ 1) (H : E →L[𝕜] E)
    {s r δ : ℝ} (hδ : 0 < δ) (hc : 0 < 1 - δ * (s / 2))
    (hr : ∀ x, ‖x‖ = 1 → re ⟪x, H x⟫ ≤ s → ‖S x‖ ≤ 1 - r)
    (h₁ : δ * ‖H‖ ^ 2 < s) (h₂ : δ * (‖H‖ + s / 2) < r) :
    ‖S.comp (ContinuousLinearMap.id 𝕜 E - (δ : 𝕜) • H)‖ ≤ 1 - δ * (s / 2) := by
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hc.le fun x hx ↦ ?_
  have hHx : ‖H x‖ ≤ ‖H‖ := by simpa [hx] using H.le_opNorm x
  rw [ContinuousLinearMap.comp_apply, _root_.sub_apply, ContinuousLinearMap.id_apply,
    _root_.smul_apply]
  by_cases hxs : re ⟪x, H x⟫ ≤ s
  · have hSHx : ‖S (H x)‖ ≤ ‖H‖ := by
      simpa using (S.le_of_opNorm_le hS (H x)).trans (by simpa using hHx)
    calc ‖S (x - (δ : 𝕜) • H x)‖ = ‖S x - (δ : 𝕜) • S (H x)‖ := by simp
      _ ≤ ‖S x‖ + δ * ‖S (H x)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, norm_ofReal, abs_of_pos hδ]
      _ ≤ (1 - r) + δ * ‖H‖ := by gcongr; exact hr x hx hxs
      _ ≤ 1 - δ * (s / 2) := by nlinarith
  · rw [not_le] at hxs
    have hsq : ‖x - (δ : 𝕜) • H x‖ ^ 2 ≤ (1 - δ * (s / 2)) ^ 2 := by
      rw [norm_sub_sq (𝕜 := 𝕜), inner_smul_right, re_ofReal_mul, norm_smul, norm_ofReal,
        abs_of_pos hδ, hx, mul_pow]
      have : δ ^ 2 * ‖H x‖ ^ 2 ≤ δ ^ 2 * ‖H‖ ^ 2 := by gcongr
      have h₃ : δ * s < δ * re ⟪x, H x⟫ := mul_lt_mul_of_pos_left hxs hδ
      have h₄ : δ * (δ * ‖H‖ ^ 2) < δ * s := mul_lt_mul_of_pos_left h₁ hδ
      nlinarith [sq_nonneg (δ * (s / 2))]
    calc ‖S (x - (δ : 𝕜) • H x)‖ ≤ ‖x - (δ : 𝕜) • H x‖ := by
          simpa using S.le_of_opNorm_le hS (x - (δ : 𝕜) • H x)
      _ ≤ 1 - δ * (s / 2) := (pow_le_pow_iff_left₀ (norm_nonneg _) hc.le two_ne_zero).1 hsq

end ContinuousLinearMap

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Convex.StrictConvexBetween

/-!
# Ball-local isometries homogeneous along rays

Let `A` be a map from the ball of radius `δ > 0` about `0` in a real normed space to a strictly
convex real normed space. If `A` preserves distances and is homogeneous along rays, in the sense
that `A (t • v) = t • A v` for `t ∈ [0, 1]`, then `A` agrees on the ball with a linear isometry.

The proof extends `A` to the whole space by `B v = s⁻¹ • A (s • v)` for any small enough scale
`s > 0`; homogeneity makes this independent of `s`, and `B` is a distance-preserving map fixing
`0`, hence a linear isometry (`Isometry.affineIsometryOfStrictConvexSpace`). This is the linear
algebra in the Myers–Steenrod theorem, where `A` is a distance-preserving map read in normal
coordinates.

## Main results

* `TauCeti.exists_linearIsometry_eqOn_ball`: a distance-preserving map on a ball that is
  homogeneous along rays agrees there with a linear isometry.
-/

public section

open Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [StrictConvexSpace ℝ F]

/-- **A distance-preserving map on a ball that is homogeneous along rays is linear there.** If
`A` preserves distances on the ball of radius `δ > 0` about `0` and `A (t • v) = t • A v` for `v`
in the ball and `t ∈ [0, 1]`, then `A` agrees on the ball with a linear isometry. -/
theorem exists_linearIsometry_eqOn_ball {A : E → F} {δ : ℝ} (hδ : 0 < δ)
    (hsmul : ∀ v ∈ Metric.ball (0 : E) δ, ∀ t ∈ Icc (0 : ℝ) 1, A (t • v) = t • A v)
    (hdist : ∀ v ∈ Metric.ball (0 : E) δ, ∀ w ∈ Metric.ball (0 : E) δ,
      dist (A v) (A w) = dist v w) :
    ∃ L : E →ₗᵢ[ℝ] F, EqOn L A (Metric.ball 0 δ) := by
  -- Extend `A` to all of `E` by homogeneity: `B v = s⁻¹ • A (s • v)` with `s = δ / (‖v‖ + δ)`,
  -- which is the same for every smaller positive scale.
  let s : E → ℝ := fun v ↦ δ / (‖v‖ + δ)
  have hs₀ (v : E) : 0 < s v := div_pos hδ (by positivity)
  have hs₁ (v : E) : s v ≤ 1 :=
    (div_le_one (by positivity)).2 (le_add_of_nonneg_left (norm_nonneg v))
  have hmem {v : E} {u : ℝ} (hu₀ : 0 ≤ u) (hu : u ≤ s v) : u • v ∈ Metric.ball 0 δ := by
    simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu₀]
    calc u * ‖v‖ ≤ s v * ‖v‖ := by gcongr
      _ < δ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg v]
  let B : E → F := fun v ↦ (s v)⁻¹ • A (s v • v)
  have hB {v : E} {u : ℝ} (hu₀ : 0 < u) (hu : u ≤ s v) : B v = u⁻¹ • A (u • v) := by
    have hus : u / s v ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one (hs₀ v)).2 hu⟩
    have hA : A (u • v) = (u / s v) • A (s v • v) := by
      rw [← hsmul _ (hmem (hs₀ v).le le_rfl) _ hus, smul_smul, div_mul_cancel₀ _ (hs₀ v).ne']
    simp only [B]
    rw [hA, smul_smul]
    congr 1
    field_simp
  have hBA {v : E} (hv : v ∈ Metric.ball 0 δ) : B v = A v := by
    simp only [B]
    rw [hsmul v hv _ ⟨(hs₀ v).le, hs₁ v⟩, smul_smul, inv_mul_cancel₀ (hs₀ v).ne', one_smul]
  have hB_isometry : Isometry B := by
    refine Isometry.of_dist_eq fun v w ↦ ?_
    have hu₀ : 0 < min (s v) (s w) := lt_min (hs₀ v) (hs₀ w)
    rw [hB hu₀ (min_le_left _ _), hB hu₀ (min_le_right _ _), dist_smul₀,
      hdist _ (hmem hu₀.le (min_le_left _ _)) _ (hmem hu₀.le (min_le_right _ _))]
    simp [dist_smul₀, abs_of_pos hu₀, hu₀.ne']
  have hB0 : B 0 = 0 := by
    have h0 := Metric.mem_ball_self (x := (0 : E)) hδ
    rw [hBA h0, ← zero_smul ℝ (0 : E), hsmul 0 h0 0 ⟨le_rfl, zero_le_one⟩, zero_smul]
  -- A distance-preserving map into a strictly convex space fixing `0` is a linear isometry.
  let T := hB_isometry.affineIsometryOfStrictConvexSpace (E := F) (F := E)
  refine ⟨T.linearIsometry, fun v hv ↦ ?_⟩
  rw [← hBA hv]
  simpa [T, hB0] using T.map_vsub v 0

end TauCeti

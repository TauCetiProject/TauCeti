/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Covering.EssentialBoundary
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The essential boundary of a ball

Against an additive Haar measure on a finite-dimensional real normed space, the essential boundary
of the open ball `ball c r`, `r > 0`, is the sphere `sphere c r`
(`TauCeti.essentialBoundary_ball`): interior points of the ball and points outside the closed ball
have density `1` and `0`, while at a point `x` of the sphere both the ball and its complement
contain a ball of radius `ρ / 2` inside `ball x ρ`, so the density of the ball at `x` is neither
`0` nor `1`.

The essential boundary only depends on the set up to null sets, so the punctured ball
`ball c r \ {c}` and, in `EuclideanSpace ℝ (Fin n)`, the union of `ball c r` with the countable set
of points with rational coordinates, also have essential boundary `sphere c r`, although their
frontiers are larger: unlike the frontier, the essential boundary ignores null sets.
-/

public section

open MeasureTheory Metric Set Filter Module AffineMap
open scoped Topology ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {t : Set E} {x : E}

/-- A set containing, for every small `ρ > 0`, a ball of radius `ρ / 2` inside `ball x ρ` does not
have density zero at `x`. -/
theorem not_hasDensityAt_zero_of_eventually_exists_ball_subset
    (h : ∀ᶠ ρ in 𝓝[>] 0, ∃ y, ball y (ρ / 2) ⊆ t ∩ ball x ρ) : ¬HasDensityAt μ t x 0 := by
  have hB : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hBt : μ (ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  refine not_hasDensityAt_zero_of_eventually_ofReal_pow_le_mul_measure_inter_ball
    (c := 2 ^ finrank ℝ E * (μ (ball (0 : E) 1))⁻¹)
    (ENNReal.mul_ne_top (by simp) (ENNReal.inv_ne_top.2 hB)) ?_
  filter_upwards [h, self_mem_nhdsWithin] with ρ ⟨y, hy⟩ (hρ : 0 < ρ)
  -- Halving the radius divides the volume by `2 ^ n`.
  have h2 : ENNReal.ofReal (ρ ^ finrank ℝ E) =
      2 ^ finrank ℝ E * ENNReal.ofReal ((ρ / 2) ^ finrank ℝ E) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow zero_le_two,
      ← ENNReal.ofReal_mul (by positivity), ← mul_pow, mul_div_cancel₀ _ two_ne_zero]
  calc ENNReal.ofReal (ρ ^ finrank ℝ E)
      = 2 ^ finrank ℝ E * (μ (ball (0 : E) 1))⁻¹ * μ (ball y (ρ / 2)) := by
        rw [h2, Measure.addHaar_ball_of_pos μ y (by positivity), mul_assoc,
          mul_left_comm (μ (ball (0 : E) 1))⁻¹, ENNReal.inv_mul_cancel hB hBt, mul_one]
    _ ≤ 2 ^ finrank ℝ E * (μ (ball (0 : E) 1))⁻¹ * μ (t ∩ ball x ρ) := by gcongr

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- For `x` on `sphere c r`, the ball of radius `ρ / 2` about the point `x - (ρ / 2r)(c - x)`
lies outside `ball c r` and inside `ball x ρ`. -/
private theorem ball_lineMap_neg_subset_compl_ball_inter_ball {c : E} {r ρ : ℝ} (hx : dist x c = r)
    (hr : 0 < r) (hρ : 0 < ρ) :
    ball (lineMap x c (-(ρ / 2 / r))) (ρ / 2) ⊆ (ball c r)ᶜ ∩ ball x ρ := by
  have hyc := dist_lineMap_right x c (-(ρ / 2 / r))
  have hyx := dist_lineMap_left x c (-(ρ / 2 / r))
  rw [Real.norm_eq_abs, hx, sub_neg_eq_add, abs_of_pos (by positivity), add_mul, one_mul,
    div_mul_cancel₀ _ hr.ne'] at hyc
  rw [Real.norm_eq_abs, hx, abs_neg, abs_of_pos (by positivity), div_mul_cancel₀ _ hr.ne'] at hyx
  intro z hz
  rw [mem_ball] at hz
  simp only [mem_inter_iff, mem_compl_iff, mem_ball, not_lt]
  constructor
  · linarith [dist_triangle (lineMap x c (-(ρ / 2 / r))) z c,
      dist_comm z (lineMap x c (-(ρ / 2 / r)))]
  · linarith [dist_triangle z (lineMap x c (-(ρ / 2 / r))) x]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- For `x` on `sphere c r` and `ρ < r`, the ball of radius `ρ / 2` about the point
`x + (ρ / 2r)(c - x)` lies inside both `ball c r` and `ball x ρ`. -/
private theorem ball_lineMap_subset_ball_inter_ball {c : E} {r ρ : ℝ} (hx : dist x c = r)
    (hρ : 0 < ρ) (hρr : ρ < r) :
    ball (lineMap x c (ρ / 2 / r)) (ρ / 2) ⊆ ball c r ∩ ball x ρ := by
  have hr : 0 < r := hρ.trans hρr
  have hyc := dist_lineMap_right x c (ρ / 2 / r)
  have hyx := dist_lineMap_left x c (ρ / 2 / r)
  have hlt : ρ / 2 / r < 1 := (div_lt_one hr).2 (by linarith)
  rw [Real.norm_eq_abs, hx, abs_of_pos (by linarith), sub_mul, one_mul,
    div_mul_cancel₀ _ hr.ne'] at hyc
  rw [Real.norm_eq_abs, hx, abs_of_pos (by positivity), div_mul_cancel₀ _ hr.ne'] at hyx
  intro z hz
  rw [mem_ball] at hz
  rw [mem_inter_iff, mem_ball, mem_ball]
  constructor
  · linarith [dist_triangle z (lineMap x c (ρ / 2 / r)) c]
  · linarith [dist_triangle z (lineMap x c (ρ / 2 / r)) x]

/-- **The essential boundary of a ball is its sphere.** For `r > 0`, the open ball `ball c r` has
essential boundary `sphere c r`. -/
theorem essentialBoundary_ball {c : E} {r : ℝ} (hr : 0 < r) :
    essentialBoundary μ (ball c r) = sphere c r := by
  refine (essentialBoundary_subset_frontier.trans (frontier_ball c hr.ne').subset).antisymm
    fun x hx ↦ ?_
  rw [mem_sphere] at hx
  have hball : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall x ρ) ≠ 0 ∧ μ (closedBall x ρ) ≠ ∞ :=
    eventually_mem_nhdsWithin.mono fun ρ (hρ : 0 < ρ) ↦
      ⟨(measure_closedBall_pos μ x hρ).ne', measure_closedBall_lt_top.ne⟩
  have hnm := (measurableSet_ball (x := c) (ε := r)).nullMeasurableSet (μ := μ)
  refine mem_essentialBoundary.2 ⟨fun h1 ↦ ?_, fun h0 ↦ ?_⟩
  · -- Outside: the ball of radius `ρ / 2` about `x - (ρ / 2r)(c - x)` misses `ball c r`.
    refine not_hasDensityAt_zero_of_eventually_exists_ball_subset ?_
      ((hasDensityAt_compl_zero_iff hnm hball).2 (mem_essentialInterior.1 h1))
    filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    exact ⟨_, ball_lineMap_neg_subset_compl_ball_inter_ball hx hr hρ⟩
  · -- Inside: the ball of radius `ρ / 2` about `x + (ρ / 2r)(c - x)` lies in `ball c r`.
    refine not_hasDensityAt_zero_of_eventually_exists_ball_subset ?_ (mem_essentialExterior.1 h0)
    filter_upwards [Ioo_mem_nhdsGT hr] with ρ ⟨hρ, hρr⟩
    exact ⟨_, ball_lineMap_subset_ball_inter_ball hx hρ hρr⟩

/-- The punctured ball `ball c r \ {c}`, `r > 0`, has essential boundary `sphere c r`. -/
theorem essentialBoundary_ball_sdiff_singleton [Nontrivial E] {c : E} {r : ℝ} (hr : 0 < r) :
    essentialBoundary μ (ball c r \ {c}) = sphere c r := by
  rw [essentialBoundary_congr_ae (sdiff_null_ae_eq_self (measure_singleton c)),
    essentialBoundary_ball hr]

/-- In `EuclideanSpace ℝ (Fin n)`, the union of the ball `ball c r`, `r > 0`, with the points of
rational coordinates has essential boundary `sphere c r`. -/
theorem essentialBoundary_ball_union_rational {n : ℕ} [NeZero n]
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) :
    essentialBoundary volume
        (ball c r ∪ range fun q : Fin n → ℚ ↦ WithLp.toLp 2 fun i ↦ (q i : ℝ)) = sphere c r := by
  have hQ : (range fun q : Fin n → ℚ ↦ WithLp.toLp 2 fun i ↦ (q i : ℝ)) =ᵐ[volume]
      (∅ : Set (EuclideanSpace ℝ (Fin n))) :=
    ae_eq_empty.2 ((countable_range _).measure_zero _)
  rw [essentialBoundary_congr_ae (union_ae_eq_left_of_ae_eq_empty hQ), essentialBoundary_ball hr]

end TauCeti

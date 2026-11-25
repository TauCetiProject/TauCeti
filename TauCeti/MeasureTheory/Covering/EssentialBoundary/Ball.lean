/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Covering.EssentialBoundary
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

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
frontiers are larger. These are examples of Layer 5 of the GeometricMeasureTheory roadmap.
-/

public section

open MeasureTheory Metric Set Filter Module
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
  calc ENNReal.ofReal (ρ ^ finrank ℝ E)
      = 2 ^ finrank ℝ E * (μ (ball (0 : E) 1))⁻¹ * μ (ball y (ρ / 2)) := by
        rw [Measure.addHaar_ball_of_pos μ y (by positivity : 0 < ρ / 2),
          show ∀ a : ℝ≥0∞, 2 ^ finrank ℝ E * (μ (ball (0 : E) 1))⁻¹ * (a * μ (ball 0 1)) =
            2 ^ finrank ℝ E * a * ((μ (ball (0 : E) 1))⁻¹ * μ (ball 0 1)) from fun a ↦ by ring,
          ENNReal.inv_mul_cancel hB hBt, mul_one,
          show ρ ^ finrank ℝ E = 2 ^ finrank ℝ E * (ρ / 2) ^ finrank ℝ E by
            rw [← mul_pow]; ring_nf,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two,
          ENNReal.ofReal_ofNat]
    _ ≤ 2 ^ finrank ℝ E * (μ (ball (0 : E) 1))⁻¹ * μ (t ∩ ball x ρ) := by gcongr

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Moving a point `x` of `sphere c r` by `a • (c - x)` puts it at distance `|1 - a| r` from
`c`. -/
private theorem dist_add_smul_sub_self {c : E} {r : ℝ} (hx : dist x c = r) (a : ℝ) :
    dist (x + a • (c - x)) c = |1 - a| * r := by
  have : x + a • (c - x) - c = (1 - a) • (x - c) := by module
  rw [dist_eq_norm, this, norm_smul, Real.norm_eq_abs, ← dist_eq_norm, hx]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem dist_add_smul_sub_left {c : E} {r : ℝ} (hx : dist x c = r) (a : ℝ) :
    dist (x + a • (c - x)) x = |a| * r := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, ← dist_eq_norm', hx]

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
    have hyc := dist_add_smul_sub_self hx (-(ρ / 2 / r))
    have hyx := dist_add_smul_sub_left hx (-(ρ / 2 / r))
    have hpos : 0 < ρ / 2 / r := by positivity
    rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - -(ρ / 2 / r))] at hyc
    rw [abs_neg, abs_of_pos (by positivity), div_mul_cancel₀ _ hr.ne'] at hyx
    rw [show (1 - -(ρ / 2 / r)) * r = r + ρ / 2 by field_simp; ring] at hyc
    refine ⟨x + (-(ρ / 2 / r)) • (c - x), fun z hz ↦ ⟨?_, ?_⟩⟩ <;> rw [mem_ball] at hz
    · simp only [mem_compl_iff, mem_ball, not_lt]
      have := dist_triangle (x + (-(ρ / 2 / r)) • (c - x)) z c
      linarith [dist_comm z (x + (-(ρ / 2 / r)) • (c - x))]
    · rw [mem_ball]
      linarith [dist_triangle z (x + (-(ρ / 2 / r)) • (c - x)) x]
  · -- Inside: the ball of radius `ρ / 2` about `x + (ρ / 2r)(c - x)` lies in `ball c r`.
    refine not_hasDensityAt_zero_of_eventually_exists_ball_subset ?_ (mem_essentialExterior.1 h0)
    filter_upwards [Ioo_mem_nhdsGT hr] with ρ ⟨hρ, hρr⟩
    have hyc := dist_add_smul_sub_self hx (ρ / 2 / r)
    have hyx := dist_add_smul_sub_left hx (ρ / 2 / r)
    have hlt : ρ / 2 / r < 1 := (div_lt_one hr).2 (by linarith)
    rw [abs_of_pos (by linarith), show (1 - ρ / 2 / r) * r = r - ρ / 2 by field_simp] at hyc
    rw [abs_of_pos (by positivity), div_mul_cancel₀ _ hr.ne'] at hyx
    refine ⟨x + (ρ / 2 / r) • (c - x), fun z hz ↦ ⟨?_, ?_⟩⟩ <;> rw [mem_ball] at hz ⊢
    · linarith [dist_triangle z (x + (ρ / 2 / r) • (c - x)) c]
    · linarith [dist_triangle z (x + (ρ / 2 / r) • (c - x)) x]

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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Winding
public import TauCeti.Analysis.Contour.Winding.Number.Circle.Basic
import TauCeti.Analysis.Contour.Cycle.Trace
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Circle

/-!
# Circles as contour cycles

The counterclockwise circle `circleMap c R` on `[0, 2π]` is a closed `C¹` curve. This file packages
it as a one-generator contour cycle and identifies its cycle invariants with the classical ones:
the cycle integral is Mathlib's circle integral `∮ z in C(c, R), f z`, the trace is the sphere of
radius `|R|`, and the winding number is `1` inside the disc and `0` outside it.

Circles are the comparison cycles for cycle integrals whose integrand is controlled near infinity,
such as Banach-algebra resolvents.

## Main definitions

* `TauCeti.Contour.circleCurve`: the circle as a closed absolutely continuous curve.
* `TauCeti.Contour.circleCycle`: the corresponding one-generator contour cycle.

## Main results

* `TauCeti.Contour.Cycle.integral_circleCycle`: its cycle integral is the circle integral.
* `TauCeti.Contour.Cycle.trace_circleCycle`: its trace is the sphere.
* `TauCeti.Contour.Cycle.windingNumber_circleCycle_eq_one_of_dist_lt`,
  `TauCeti.Contour.Cycle.windingNumber_circleCycle_eq_zero_of_lt_dist`,
  `TauCeti.Contour.Cycle.windingNumber_circleCycle_eq_one_of_dist_lt_abs`,
  `TauCeti.Contour.Cycle.windingNumber_circleCycle_eq_zero_of_abs_lt_dist`: its winding numbers.
* `TauCeti.Contour.Cycle.windingWeight_circleCycle`: its trace-zero winding weight is the
  indicator of `ball c |R|`.
* `TauCeti.Contour.Cycle.isIn_and_isNullHomologous_sub_circleCycle`,
  `TauCeti.Contour.Cycle.windingWeight_sub_circleCycle_ae_eq`: excising a small circle about a
  point off the trace gives a punctured null-homologous cycle whose winding weight is the indicator
  of `Δ \ closedBall ξ ε` a.e.
-/

public section

noncomputable section

open MeasureTheory Metric Set

open scoped Real

namespace TauCeti.Contour

/-- The counterclockwise circle `circleMap c R` on `[0, 2π]`, bundled as a closed absolutely
continuous curve. -/
def circleCurve (c : ℂ) (R : ℝ) : AbsolutelyContinuousClosedCurve :=
  AbsolutelyContinuousClosedCurve.of (circleMap c R)
    (absolutelyContinuousOnInterval_circleMap c R 0 (2 * π))
    (by simpa using (periodic_circleMap c R 0).symm)

/-- The bundled circle starts at `0`. -/
@[simp]
theorem circleCurve_a (c : ℂ) (R : ℝ) : (circleCurve c R).a = 0 := by
  rw [circleCurve, AbsolutelyContinuousClosedCurve.of_a]

/-- The bundled circle ends at `2π`. -/
@[simp]
theorem circleCurve_b (c : ℂ) (R : ℝ) : (circleCurve c R).b = 2 * π := by
  rw [circleCurve, AbsolutelyContinuousClosedCurve.of_b]

/-- On its parameter interval, the bundled circle agrees with `circleMap c R`. -/
@[simp]
theorem circleCurve_apply {c : ℂ} {R t : ℝ} (ht : t ∈ uIcc 0 (2 * π)) :
    circleCurve c R t = circleMap c R t := by
  rw [circleCurve]
  exact AbsolutelyContinuousClosedCurve.of_apply _ _ _ ht

/-- The counterclockwise circle `circleMap c R` on `[0, 2π]` as a one-generator contour cycle. -/
def circleCycle (c : ℂ) (R : ℝ) : Cycle :=
  FreeAddCommGroup.of (circleCurve c R)

/-- Defining formula for `TauCeti.Contour.circleCycle`. -/
theorem circleCycle_def (c : ℂ) (R : ℝ) :
    circleCycle c R = FreeAddCommGroup.of (circleCurve c R) :=
  (rfl)

namespace Cycle

/-- Integrating over the circle cycle gives Mathlib's circle integral. -/
@[simp]
theorem integral_circleCycle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (c : ℂ) (R : ℝ) :
    integral f (circleCycle c R) = ∮ z in C(c, R), f z := by
  rw [circleCycle, circleCurve, integral_of_raw, circleIntegral]

/-- The trace of the circle cycle is the sphere of radius `|R|`. -/
@[simp]
theorem trace_circleCycle (c : ℂ) (R : ℝ) : trace (circleCycle c R) = sphere c |R| := by
  rw [circleCycle, circleCurve, trace_of_raw, Complex.image_circleMap_uIcc]

/-- The circle cycle winds once around every point inside its disc. -/
theorem windingNumber_circleCycle_eq_one_of_dist_lt {c w : ℂ} {R : ℝ} (hw : dist w c < R) :
    windingNumber w (circleCycle c R) = 1 := by
  rw [circleCycle, circleCurve, windingNumber_of_raw,
    Contour.windingNumber_circleMap_eq_one_of_dist_lt hw]

/-- The circle cycle does not wind around points outside its closed disc. -/
theorem windingNumber_circleCycle_eq_zero_of_lt_dist {c w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hw : R < dist w c) : windingNumber w (circleCycle c R) = 0 := by
  rw [circleCycle, circleCurve, windingNumber_of_raw,
    Contour.windingNumber_circleMap_eq_zero_of_lt_dist hR hw]

private theorem windingNumber_circleCycle_neg_of_notMem {c w : ℂ} {R : ℝ}
    (hw : w ∉ sphere c |R|) :
    windingNumber w (circleCycle c (-R)) = windingNumber w (circleCycle c R) := by
  have havoid : ∀ θ, circleMap c R θ ≠ w := fun θ h ↦ by
    apply hw
    rw [← h, mem_sphere, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero]
  have havoid_neg : ∀ θ, circleMap c (-R) θ ≠ w := fun θ h ↦
    havoid (θ + π) (by simpa [circleMap_neg_radius] using h)
  rw [circleCycle, circleCurve, windingNumber_of_raw, circleCycle, circleCurve,
    windingNumber_of_raw, Contour.windingNumber_circleMap_eq_circleIntegral havoid_neg,
    Contour.windingNumber_circleMap_eq_circleIntegral havoid]
  congr 1
  simp only [circleIntegral, smul_eq_mul]
  have hper : Function.Periodic
      (fun θ ↦ deriv (circleMap c R) θ * (circleMap c R θ - w)⁻¹) (2 * π) := fun θ ↦ by
    simp only [deriv_circleMap, periodic_circleMap c R θ, periodic_circleMap 0 R θ]
  have hfun : (fun θ ↦ deriv (circleMap c (-R)) θ * (circleMap c (-R) θ - w)⁻¹) =
      fun θ ↦ deriv (circleMap c R) (θ + π) * (circleMap c R (θ + π) - w)⁻¹ := by
    ext θ
    rw [circleMap_neg_radius, deriv_circleMap, deriv_circleMap, circleMap_neg_radius]
  rw [hfun, intervalIntegral.integral_comp_add_right
    (fun θ ↦ deriv (circleMap c R) θ * (circleMap c R θ - w)⁻¹) π,
    zero_add, add_comm (2 * π) π, hper.intervalIntegral_add_eq π 0, zero_add]

/-- The circle cycle winds once around every point inside its disc (regardless of the sign of
`R`). -/
theorem windingNumber_circleCycle_eq_one_of_dist_lt_abs {c w : ℂ} {R : ℝ} (hw : dist w c < |R|) :
    windingNumber w (circleCycle c R) = 1 := by
  rcases le_total 0 R with hR | hR
  · rw [abs_of_nonneg hR] at hw
    exact windingNumber_circleCycle_eq_one_of_dist_lt hw
  · rw [← windingNumber_circleCycle_neg_of_notMem fun h ↦ hw.ne (mem_sphere.mp h)]
    exact windingNumber_circleCycle_eq_one_of_dist_lt (by rwa [abs_of_nonpos hR] at hw)

/-- The circle cycle does not wind around points outside its closed disc (regardless of the sign of
`R`). -/
theorem windingNumber_circleCycle_eq_zero_of_abs_lt_dist {c w : ℂ} {R : ℝ} (hw : |R| < dist w c) :
    windingNumber w (circleCycle c R) = 0 := by
  rcases le_total 0 R with hR | hR
  · rw [abs_of_nonneg hR] at hw
    exact windingNumber_circleCycle_eq_zero_of_lt_dist hR hw
  · rw [← windingNumber_circleCycle_neg_of_notMem fun h ↦ hw.ne' (mem_sphere.mp h)]
    exact windingNumber_circleCycle_eq_zero_of_lt_dist (neg_nonneg.mpr hR)
      (by rwa [abs_of_nonpos hR] at hw)

/-- The trace-zero `windingWeight` of `circleCycle c R` is the indicator of `ball c |R|`. -/
theorem windingWeight_circleCycle (c : ℂ) (R : ℝ) :
    (circleCycle c R).windingWeight = (ball c |R|).indicator 1 := by
  ext z
  rcases lt_trichotomy (dist z c) |R| with hlt | heq | hgt
  · rw [windingWeight_eq_of_notMem _ (by rw [trace_circleCycle, mem_sphere]; exact hlt.ne),
      windingNumber_circleCycle_eq_one_of_dist_lt_abs hlt,
      indicator_of_mem (mem_ball.mpr hlt), Pi.one_apply, Complex.one_re]
  · rw [windingWeight_eq_zero_of_mem _ (by rw [trace_circleCycle, mem_sphere]; exact heq),
      indicator_of_notMem (by simp [mem_ball, heq])]
  · rw [windingWeight_eq_of_notMem _ (by rw [trace_circleCycle, mem_sphere]; exact hgt.ne'),
      windingNumber_circleCycle_eq_zero_of_abs_lt_dist hgt,
      indicator_of_notMem (by simp [mem_ball, hgt.le]), Complex.zero_re]

open scoped Classical in
/-- Excising a small closed disc `closedBall ξ ε ⊆ Δ` around `ξ ∉ C.trace` from a cycle `C`
lying in `Ω` with winding number `1` on `Δ` and `0` outside produces a cycle
`C - circleCycle ξ ε` that lies in and is null-homologous in `Ω \ closedBall ξ r` for some
`0 < r < ε`. -/
theorem isIn_and_isNullHomologous_sub_circleCycle (C : Cycle) {Ω Δ : Set ℂ}
    (hΔΩ : Δ ⊆ Ω) (htrace : C.IsIn Ω)
    (hindex : ∀ z ∉ C.trace, C.windingNumber z = if z ∈ Δ then 1 else 0)
    {ξ : ℂ} {ε : ℝ} (hε : 0 < ε) (hball : closedBall ξ ε ⊆ Δ) (hξtr : ξ ∉ C.trace) :
    ∃ r, 0 < r ∧ r < ε ∧
      (C - circleCycle ξ ε).IsIn (Ω \ closedBall ξ r) ∧
      (C - circleCycle ξ ε).IsNullHomologous (Ω \ closedBall ξ r) := by
  obtain ⟨δ, hδ, hballδ⟩ := Metric.isOpen_iff.mp C.isCompact_trace.isClosed.isOpen_compl ξ hξtr
  set r : ℝ := min (ε / 2) (δ / 2)
  have hr0 : 0 < r := lt_min (half_pos hε) (half_pos hδ)
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hrδ : r < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hmiss : Disjoint (closedBall ξ r) C.trace := Set.disjoint_left.mpr fun z hz htr ↦
    hballδ (mem_ball.mpr ((mem_closedBall.mp hz).trans_lt hrδ)) htr
  have htr_C : C.trace ⊆ Ω \ closedBall ξ r := fun z hz ↦
    ⟨C.isIn_iff.mp htrace hz, fun hzr ↦ Set.disjoint_left.mp hmiss hzr hz⟩
  have htr_S : (circleCycle ξ ε).trace ⊆ Ω \ closedBall ξ r := by
    rw [trace_circleCycle, abs_of_pos hε]
    exact fun z hz ↦ ⟨hΔΩ (hball (sphere_subset_closedBall hz)),
      fun hzr ↦ (mem_closedBall.mp hzr).not_gt (hrε.trans_eq (mem_sphere.mp hz).symm)⟩
  refine ⟨r, hr0, hrε, ?_, ?_⟩
  · rw [isIn_iff]
    exact (trace_sub_subset _ _).trans (union_subset htr_C htr_S)
  · rw [isNullHomologous_iff]
    intro z hzU
    rw [map_sub]
    by_cases hzr : z ∈ closedBall ξ r
    · have hzε : dist z ξ < ε := (mem_closedBall.mp hzr).trans_lt hrε
      rw [hindex z (fun h ↦ (htr_C h).2 hzr), ite_eq_left (hball (ball_subset_closedBall hzε)),
        windingNumber_circleCycle_eq_one_of_dist_lt hzε, sub_self]
    · have hzΩ : z ∉ Ω := fun h ↦ hzU ⟨h, hzr⟩
      have hzΔ : z ∉ Δ := fun h ↦ hzΩ (hΔΩ h)
      rw [hindex z (fun h ↦ hzΩ (htr_C h).1), ite_eq_right hzΔ,
        windingNumber_circleCycle_eq_zero_of_lt_dist hε.le
          (not_le.mp fun hle ↦ hzΔ (hball (mem_closedBall.mpr hle))), sub_zero]

open scoped Classical in
/-- Almost everywhere, subtracting `circleCycle ξ ε` (`closedBall ξ ε ⊆ Δ`, `ε > 0`) from a cycle
`C` with winding number `1` on `Δ` and `0` outside changes its trace-zero winding weight to the
indicator of `Δ \ closedBall ξ ε`. -/
theorem windingWeight_sub_circleCycle_ae_eq (C : Cycle) {Δ : Set ℂ}
    (hindex : ∀ z ∉ C.trace, C.windingNumber z = if z ∈ Δ then 1 else 0)
    {ξ : ℂ} {ε : ℝ} (hε : 0 < ε) (hball : closedBall ξ ε ⊆ Δ) :
    (C - circleCycle ξ ε).windingWeight =ᵐ[volume] (Δ \ closedBall ξ ε).indicator 1 := by
  have haeC : ∀ᵐ z ∂volume, z ∉ C.trace := compl_mem_ae_iff.mpr (C.addHaar_trace_eq_zero volume)
  have haeS : ∀ᵐ z ∂volume, z ∉ (circleCycle ξ ε).trace :=
    compl_mem_ae_iff.mpr ((circleCycle ξ ε).addHaar_trace_eq_zero volume)
  filter_upwards [C.windingWeight_sub_ae (circleCycle ξ ε), haeC, haeS] with z hzsub hzC hzS
  rw [hzsub, Pi.sub_apply, C.windingWeight_eq_of_notMem hzC, hindex z hzC,
    windingWeight_circleCycle ξ ε, abs_of_pos hε]
  have hne : dist z ξ ≠ ε := by
    rwa [trace_circleCycle, abs_of_pos hε, mem_sphere] at hzS
  have hmem : z ∈ ball ξ ε ↔ z ∈ closedBall ξ ε := by
    rw [mem_ball, mem_closedBall]
    exact ⟨le_of_lt, fun hle ↦ lt_of_le_of_ne hle hne⟩
  by_cases hzB : z ∈ closedBall ξ ε
  · have hzΔ : z ∈ Δ := hball hzB
    simp [hzΔ, hzB, hmem.mpr hzB]
  · have hzB' : z ∉ ball ξ ε := fun h ↦ hzB (hmem.mp h)
    by_cases hzΔ : z ∈ Δ <;> simp [hzΔ, hzB, hzB']

end Cycle

end TauCeti.Contour

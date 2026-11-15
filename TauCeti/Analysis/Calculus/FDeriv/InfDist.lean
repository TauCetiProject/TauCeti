/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The derivative of the distance to a set

In a real normed space, the distance `x ↦ infDist x s` to a nonempty set `s` is `1`-Lipschitz,
so its derivative has norm at most one wherever it exists. Away from the closure of `s` the norm
is exactly one (`TauCeti.norm_fderiv_infDist_eq_one`): moving from `x` straight towards an almost
nearest point of `s` decreases the distance at almost unit speed. Combined with Rademacher's
theorem, this says that in a finite-dimensional space the distance function solves the eikonal
equation `‖D (infDist · s)‖ = 1` almost everywhere off the closure of `s`, while its derivative
vanishes on the closure (`TauCeti.norm_fderiv_infDist_ae_eq_indicator`). This is the identity that
turns the coarea formula for the distance function into a formula for the volume of parallel
sets.
-/

public section

open Metric Set MeasureTheory Filter

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The distance to a set solves the eikonal equation.** In a real normed space, at every point
`x` off the closure of a nonempty set `s` where the distance function `infDist · s` is
differentiable, its derivative has norm one. -/
theorem norm_fderiv_infDist_eq_one {s : Set E} (hs : s.Nonempty) {x : E} (hx : x ∉ closure s)
    (hd : DifferentiableAt ℝ (infDist · s) x) : ‖fderiv ℝ (infDist · s) x‖ = 1 := by
  set f' := fderiv ℝ (infDist · s) x
  have hpos : 0 < infDist x s :=
    infDist_nonneg.lt_of_ne' fun h => hx ((mem_closure_iff_infDist_zero hs).2 h)
  set d := infDist x s
  refine le_antisymm ?_ (le_of_forall_pos_lt_add fun ε hε => ?_)
  · simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitz_infDist_pt (s := s)) (x₀ := x)
  -- On a ball of radius `δ` about `x`, the linearisation error is at most `ε / 2` times the step.
  obtain ⟨δ, hδ, hδx⟩ := eventually_nhds_iff_ball.1
    ((hasFDerivAt_iff_isLittleO.1 hd.hasFDerivAt).def (half_pos hε))
  set t := min (δ / 2) (min (ε / 2) d)
  have ht : 0 < t := lt_min (half_pos hδ) (lt_min (half_pos hε) hpos)
  have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have htε : t ≤ ε / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have htd : t ≤ d := (min_le_right _ _).trans (min_le_right _ _)
  -- An almost nearest point `q ∈ s`, at distance `ρ < d + t * t`, and the unit vector `v` from
  -- `x` towards it.
  obtain ⟨q, hq, hqx⟩ := (infDist_lt_iff hs).1 (lt_add_of_pos_right d (mul_pos ht ht))
  set ρ := ‖x - q‖
  have hρd : d ≤ ρ := (infDist_le_dist_of_mem hq).trans_eq (dist_eq_norm x q)
  have hρlt : ρ < d + t * t := (dist_eq_norm x q).symm.trans_lt hqx
  have hρ : 0 < ρ := hpos.trans_le hρd
  set v := ρ⁻¹ • (q - x)
  have hv : ‖v‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, norm_sub_rev q x, inv_mul_cancel₀ hρ.ne']
  -- Moving a distance `t` towards `q` brings the distance to `s` down to at most `ρ - t`.
  have hup : infDist (x + t • v) s ≤ ρ - t := by
    have hc : 0 ≤ 1 - t * ρ⁻¹ := by
      rw [sub_nonneg, ← div_eq_mul_inv, div_le_one hρ]; exact htd.trans hρd
    calc infDist (x + t • v) s ≤ dist (x + t • v) q := infDist_le_dist_of_mem hq
      _ = (1 - t * ρ⁻¹) * ρ := by
        rw [dist_eq_norm, show x + t • v - q = (1 - t * ρ⁻¹) • (x - q) by simp only [v]; module,
          norm_smul, Real.norm_of_nonneg hc]
      _ = ρ - t := by field_simp
  have hy := hδx (x + t • v) (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one,
      Real.norm_of_nonneg ht.le]
    exact htδ)
  rw [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul, hv, mul_one,
    Real.norm_of_nonneg ht.le, Real.norm_eq_abs] at hy
  have hlin := (abs_le.1 hy).1
  -- Hence `f' v < t - 1 + ε / 2`, while `-f' v ≤ ‖f'‖` since `v` is a unit vector.
  have hfv : f' v < t - 1 + ε / 2 :=
    lt_of_mul_lt_mul_left (by nlinarith) ht.le
  have hop : -f' v ≤ ‖f'‖ := by
    have h := f'.le_opNorm v
    rw [hv, mul_one, Real.norm_eq_abs] at h
    exact (neg_le_abs _).trans h
  linarith

section Rademacher

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

/-- **The distance to a set solves the eikonal equation almost everywhere.** Against an additive
Haar measure on a finite-dimensional real normed space, the derivative of the distance to a
nonempty set `s` has norm one at almost every point off the closure of `s`, and vanishes on the
closure. -/
theorem norm_fderiv_infDist_ae_eq_indicator {s : Set E} (hs : s.Nonempty) :
    (fun x => ‖fderiv ℝ (infDist · s) x‖) =ᵐ[μ] (closure s)ᶜ.indicator 1 := by
  filter_upwards [(lipschitz_infDist_pt (s := s)).ae_differentiableAt (μ := μ)] with x hx
  by_cases hcl : x ∈ closure s
  · -- On the closure the distance attains its minimum.
    have hmin : IsLocalMin (infDist · s) x := Eventually.of_forall fun y => by
      simp only [(mem_closure_iff_infDist_zero hs).1 hcl]
      exact infDist_nonneg
    rw [hmin.fderiv_eq_zero, indicator_of_notMem (not_not.2 hcl), norm_zero]
  · rw [indicator_of_mem hcl, norm_fderiv_infDist_eq_one hs hcl hx, Pi.one_apply]

end Rademacher

end TauCeti

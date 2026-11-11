/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ContinuousLog.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Continuous logarithms on circles

This file collects the facts about `TauCeti.HasContinuousLogOn` on circles in `ℂ`.

* `TauCeti.not_hasContinuousLogOn_zpow_sub_sphere`: no nonzero integer power of `z ↦ z - a` has
  a continuous logarithm on a circle centred at `a`; `TauCeti.not_hasContinuousLogOn_sub_sphere`
  is the first power. This is the classical winding obstruction, proved by following
  `t ↦ h (a + r * exp (t * I)) - k * (log r + t * I)` once around and finding it both constant
  and shifted by `k * 2 * π * I`.
* `TauCeti.exists_forall_hasContinuousLogOn_sphere`: a function continuous off the origin and
  tending to one at infinity has its principal logarithm on every large enough circle about the
  origin.
-/

public section

namespace TauCeti

open Complex Filter Metric Set Topology

open scoped Real

/-- **A circle carries no continuous logarithm of a nonzero power of the map to its centre.**
Following `t ↦ h (a + r * exp (t * I)) - k * (log r + t * I)` once around the circle, it is both
constant and shifted by `k * 2 * π * I`. -/
theorem not_hasContinuousLogOn_zpow_sub_sphere {r : ℝ} (hr : 0 ≤ r) (a : ℂ) {k : ℤ} (hk : k ≠ 0) :
    ¬ HasContinuousLogOn (fun z => (z - a) ^ k) (sphere a r) := by
  rcases hr.eq_or_lt with rfl | hr
  · intro hlog
    exact (hlog.ne_zero (by simp : a ∈ sphere a 0)) (by simp [zero_zpow k hk])
  rw [hasContinuousLogOn_iff]
  rintro ⟨h, hcont, heq⟩
  set γ : ℝ → ℂ := circleMap a r with hγdef
  have hγmem : ∀ t, γ t ∈ sphere a r := fun t => by
    simpa only [hγdef] using circleMap_mem_sphere a hr.le t
  have hγc : Continuous γ := by
    simpa only [hγdef] using continuous_circleMap a r
  set c : ℝ → ℂ := fun t => h (γ t) - k * (Real.log r + t * Complex.I) with hcdef
  have hcc : Continuous c := by
    have hhγ : Continuous fun t : ℝ => h (γ t) := hcont.comp_continuous hγc hγmem
    exact hhγ.sub (continuous_const.mul
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)))
  -- on the circle, `z - a = r * exp (t * I) = exp (log r + t * I)`
  have hγsub : ∀ t, γ t - a = Complex.exp (Real.log r + t * Complex.I) := fun t => by
    rw [hγdef, circleMap_sub_center, circleMap_zero, Complex.exp_add, ← Complex.ofReal_exp,
      Real.exp_log hr]
  have hc1 : ∀ t, Complex.exp (c t) = 1 := fun t => by
    rw [hcdef, Complex.exp_sub, heq _ (hγmem t), hγsub, Complex.exp_int_mul,
      div_self (zpow_ne_zero _ (Complex.exp_ne_zero _))]
  have hconst : c 0 = c (2 * π) :=
    eq_of_isPreconnected_of_forall_exp_eq_one (isPreconnected_range hcc)
      (by rintro w ⟨t, rfl⟩; exact hc1 t) (mem_range_self 0) (mem_range_self (2 * π))
  have hγ2 : γ (2 * π) = γ 0 := by
    simpa [hγdef] using periodic_circleMap a r 0
  rw [hcdef] at hconst
  simp only [hγ2, Complex.ofReal_zero, zero_mul, add_zero] at hconst
  have hzero : (k : ℂ) * (((2 * π : ℝ) : ℂ) * Complex.I) = 0 := by linear_combination hconst
  rcases mul_eq_zero.mp hzero with hk' | hzero
  · exact hk (by exact_mod_cast hk')
  rcases mul_eq_zero.mp hzero with hπ | hI
  · exact (by positivity : (0 : ℝ) < 2 * π).ne' (by exact_mod_cast hπ)
  · exact Complex.I_ne_zero hI

/-- **A circle carries no continuous logarithm of the map to its centre.** This is the winding
obstruction used in the plane-separation argument. -/
theorem not_hasContinuousLogOn_sub_sphere {r : ℝ} (hr : 0 ≤ r) (a : ℂ) :
    ¬ HasContinuousLogOn (fun z => z - a) (sphere a r) := by
  simpa only [zpow_one] using not_hasContinuousLogOn_zpow_sub_sphere hr a one_ne_zero

/-- A function continuous off the origin and tending to one at infinity has its principal
logarithm on every large enough circle about the origin. -/
theorem exists_forall_hasContinuousLogOn_sphere {F : ℂ → ℂ}
    (hF : Tendsto F (cocompact ℂ) (𝓝 1)) (hc : ∀ w ≠ 0, ContinuousAt F w) :
    ∃ R, ∀ ρ, R ≤ ρ → HasContinuousLogOn F (sphere 0 ρ) := by
  have hev : ∀ᶠ w in Bornology.cobounded ℂ, F w ∈ slitPlane := by
    rw [Metric.cobounded_eq_cocompact]
    exact hF.eventually_mem (isOpen_slitPlane.mem_nhds one_mem_slitPlane)
  obtain ⟨R, -, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hev
  refine ⟨max R 0 + 1, fun ρ hρ ↦ ?_⟩
  have hS : ∀ w ∈ sphere (0 : ℂ) ρ, R ≤ ‖w‖ ∧ w ≠ 0 := fun w hw ↦ by
    rw [mem_sphere_zero_iff_norm.mp hw]
    refine ⟨by linarith [le_max_left R 0], fun h ↦ ?_⟩
    simp only [h, mem_sphere_zero_iff_norm, norm_zero] at hw
    linarith [le_max_right R 0]
  exact hasContinuousLogOn_of_mapsTo_slitPlane
    (fun w hw ↦ (hc w (hS w hw).2).continuousWithinAt) fun w hw ↦ hR (hS w hw).1

end TauCeti

end

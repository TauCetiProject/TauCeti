/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Topology.Compactification.OnePoint.CrossRatio.Scalar
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Analytic cancellation limits of the cross-ratio at infinity

Over a normed field `K`, letting any single entry of the finite cross-ratio `TauCeti.crossRatio`
escape bounded sets along `Bornology.cobounded K` cancels the diverging linear factors and
converges to the corresponding one-infinity value of `OnePoint.crossRatioSphere`. When `K` is
furthermore a `ProperSpace` (such as `ℝ` or `ℂ`), `Bornology.cobounded K` agrees with the
coclosed-compact filter, yielding continuity of `OnePoint.crossRatioSphere` at `∞` in each variable
when the remaining three arguments are finite.

## Main results

* `TauCeti.tendsto_crossRatio_cobounded_first` (and its second, third, and fourth slot companions):
  convergence of `TauCeti.crossRatio` along `Bornology.cobounded K` to the four one-infinity values
  of `OnePoint.crossRatioSphere`.
* `TauCeti.tendsto_crossRatio_zero_one_cobounded`: `TauCeti.crossRatio a 0 1 z → z` along
  `Bornology.cobounded K`.
* `OnePoint.continuousAt_crossRatioSphere_infty_first` (and its three slot companions): continuity
  of `OnePoint.crossRatioSphere` at `∞` over a proper normed field.
-/

public section

open Bornology Filter OnePoint Topology

namespace TauCeti

variable {K : Type*} [NormedField K]

/-- As `a` escapes bounded sets in a normed field `K`, `crossRatio a b c d` converges to the
one-infinity cancellation value `crossRatioSphere ∞ b c d` for all `b, c, d : K`. -/
theorem tendsto_crossRatio_cobounded_first (b c d : K) :
    Tendsto (fun a : K ↦ crossRatio a b c d) (cobounded K)
      (𝓝 (crossRatioSphere ∞ b c d)) := by
  have hfactor (a : K) : crossRatio a b c d =
      ((a - c) / (a - d)) * crossRatioSphere ∞ b c d := by
    rw [crossRatio_def, crossRatioSphere_infty_coe_coe_coe, mul_div_mul_comm]
  simp_rw [hfactor]
  suffices hlim : Tendsto (fun a : K ↦ (a - c) / (a - d)) (cobounded K) (𝓝 1) by
    simpa only [one_mul] using hlim.mul_const (crossRatioSphere ∞ b c d)
  have hinv : Tendsto (fun a : K ↦ a⁻¹) (cobounded K) (𝓝 0) := tendsto_inv₀_cobounded
  have h1 (w : K) : Tendsto (fun a : K ↦ 1 - w * a⁻¹) (cobounded K) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hinv.const_mul w)
  have hdiv : Tendsto (fun a : K ↦ (1 - c * a⁻¹) / (1 - d * a⁻¹)) (cobounded K) (𝓝 1) := by
    simpa [Pi.div_def] using (h1 c).div (h1 d) one_ne_zero
  refine hdiv.congr' ?_
  filter_upwards [eventually_ne_cobounded (0 : K)] with a ha0
  have hsub (w : K) : a - w = a * (1 - w * a⁻¹) := by field_simp [ha0]
  rw [hsub c, hsub d, mul_div_mul_left _ _ ha0]

/-- As `b` escapes bounded sets in `K`, `crossRatio a b c d` converges to
`crossRatioSphere a ∞ c d` for all `a, c, d : K`. -/
theorem tendsto_crossRatio_cobounded_second (a c d : K) :
    Tendsto (fun b : K ↦ crossRatio a b c d) (cobounded K)
      (𝓝 (crossRatioSphere a ∞ c d)) := by
  simp_rw [← crossRatio_swap_within_pairs a _ c d,
    ← crossRatioSphere_swap_within_pairs (a : OnePoint K) ∞ c d]
  exact tendsto_crossRatio_cobounded_first a d c

/-- As `c` escapes bounded sets in `K`, `crossRatio a b c d` converges to
`crossRatioSphere a b ∞ d` for all `a, b, d : K`. -/
theorem tendsto_crossRatio_cobounded_third (a b d : K) :
    Tendsto (fun c : K ↦ crossRatio a b c d) (cobounded K)
      (𝓝 (crossRatioSphere a b ∞ d)) := by
  simp_rw [← crossRatio_swap_pairs a b _ d,
    ← crossRatioSphere_swap_pairs (a : OnePoint K) b ∞ d]
  exact tendsto_crossRatio_cobounded_first d a b

/-- As `d` escapes bounded sets in `K`, `crossRatio a b c d` converges to
`crossRatioSphere a b c ∞` for all `a, b, c : K`. -/
theorem tendsto_crossRatio_cobounded_fourth (a b c : K) :
    Tendsto (fun d : K ↦ crossRatio a b c d) (cobounded K)
      (𝓝 (crossRatioSphere a b c ∞)) := by
  simp_rw [← crossRatio_reverse a b c _,
    ← crossRatioSphere_reverse (a : OnePoint K) b c ∞]
  exact tendsto_crossRatio_cobounded_first c b a

/-- As `a` escapes bounded sets in `K`, `crossRatio a 0 1 z` converges to `z`. -/
theorem tendsto_crossRatio_zero_one_cobounded (z : K) :
    Tendsto (fun a : K ↦ crossRatio a 0 1 z) (cobounded K) (𝓝 z) := by
  simpa only [crossRatioSphere_infty_zero_one_coe] using
    tendsto_crossRatio_cobounded_first 0 1 z

end TauCeti

namespace OnePoint

variable {K : Type*} [NormedField K] [ProperSpace K]

/-- Over a proper normed field (such as `ℝ` or `ℂ`), `a ↦ crossRatioSphere a b c d` is continuous
at `∞` for any finite `b, c, d : K`. -/
theorem continuousAt_crossRatioSphere_infty_first (b c d : K) :
    ContinuousAt (fun a : OnePoint K ↦ crossRatioSphere a b c d) ∞ := by
  rw [OnePoint.continuousAt_infty', coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
  simpa [Function.comp_def] using TauCeti.tendsto_crossRatio_cobounded_first b c d

/-- Over a proper normed field, `b ↦ crossRatioSphere a b c d` is continuous at `∞` for any finite
`a, c, d : K`. -/
theorem continuousAt_crossRatioSphere_infty_second (a c d : K) :
    ContinuousAt (fun b : OnePoint K ↦ crossRatioSphere a b c d) ∞ := by
  rw [OnePoint.continuousAt_infty', coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
  simpa [Function.comp_def] using TauCeti.tendsto_crossRatio_cobounded_second a c d

/-- Over a proper normed field, `c ↦ crossRatioSphere a b c d` is continuous at `∞` for any finite
`a, b, d : K`. -/
theorem continuousAt_crossRatioSphere_infty_third (a b d : K) :
    ContinuousAt (fun c : OnePoint K ↦ crossRatioSphere a b c d) ∞ := by
  rw [OnePoint.continuousAt_infty', coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
  simpa [Function.comp_def] using TauCeti.tendsto_crossRatio_cobounded_third a b d

/-- Over a proper normed field, `d ↦ crossRatioSphere a b c d` is continuous at `∞` for any finite
`a, b, c : K`. -/
theorem continuousAt_crossRatioSphere_infty_fourth (a b c : K) :
    ContinuousAt (fun d : OnePoint K ↦ crossRatioSphere a b c d) ∞ := by
  rw [OnePoint.continuousAt_infty', coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
  simpa [Function.comp_def] using TauCeti.tendsto_crossRatio_cobounded_fourth a b c

end OnePoint

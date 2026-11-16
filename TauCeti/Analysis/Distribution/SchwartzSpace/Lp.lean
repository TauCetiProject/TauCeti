/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Schwartz functions in `L^∞` and uniform approximation

A Schwartz function is bounded and continuous, so it has two canonical embeddings into `L^∞(μ)` for
any measure `μ` of temperate growth: directly via `SchwartzMap.toLp ∞ μ` and via
`BoundedContinuousFunction.toLpTop μ 𝕜` applied to `SchwartzMap.toBoundedContinuousFunction`. The
two classes coincide (`SchwartzMap.toLp_top_eq_toLpTop`).

Whereas Schwartz functions are dense in `Lᵖ(μ)` for `p < ∞` (`SchwartzMap.denseRange_toLpCLM`),
they are not dense in `L^∞(μ)`. On bounded continuous functions, for any temperate measure `μ`
positive on nonempty open sets, a bounded continuous function lies in the `L^∞(μ)` closure of the
Schwartz functions exactly when it vanishes at infinity along `cocompact E`
(`BoundedContinuousFunction.toLpTop_mem_closure_range_schwartz_toLp_top_iff`): uniform limits of
Schwartz functions vanish at infinity, and conversely cutting off a function vanishing at infinity
by a smooth bump and mollifying produces a smooth compactly supported (hence Schwartz) uniform
approximant.

## Main declarations

* `SchwartzMap.toLp_top_eq_toLpTop`: `g.toLp ∞ μ` agrees with
  `BoundedContinuousFunction.toLpTop μ 𝕜 g.toBoundedContinuousFunction`.
* `BoundedContinuousFunction.toLpTop_mem_closure_range_schwartz_toLp_top_iff`: a bounded continuous
  function lies in the `L^∞(μ)` closure of the Schwartz functions iff it vanishes at infinity.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., §2.2 (Schwartz functions and approximation).
* G. B. Folland, *Real Analysis*, 2nd ed., §8.1 (mollification and density of smooth compactly
  supported functions in `C₀`).
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal SchwartzMap Convolution Topology

namespace SchwartzMap

variable {E F 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopologyEither E F]
  [NormedRing 𝕜] [Module 𝕜 F] [IsBoundedSMul 𝕜 F]

/-- The `L^∞` class of a Schwartz function agrees with `BoundedContinuousFunction.toLpTop` of its
underlying bounded continuous function. -/
theorem toLp_top_eq_toLpTop {μ : Measure E} [μ.HasTemperateGrowth] (g : 𝓢(E, F)) :
    g.toLp ∞ μ = BoundedContinuousFunction.toLpTop μ 𝕜 g.toBoundedContinuousFunction :=
  Lp.ext <| (g.coeFn_toLp ∞ μ).trans
    (BoundedContinuousFunction.coeFn_toLpTop (𝕜 := 𝕜) μ g.toBoundedContinuousFunction).symm

end SchwartzMap

namespace BoundedContinuousFunction

variable {E F 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedRing 𝕜] [Module 𝕜 F] [IsBoundedSMul 𝕜 F]

/-- **The `L^∞` closure of the Schwartz functions on bounded continuous functions.** For any
temperate measure `μ` that is positive on nonempty open sets, a bounded continuous function
`f : E →ᵇ F` lies in the `L^∞(μ)` closure of the Schwartz functions exactly when `f` vanishes at
infinity along `cocompact E`. -/
theorem toLpTop_mem_closure_range_schwartz_toLp_top_iff [CompleteSpace F] {μ : Measure E}
    [μ.HasTemperateGrowth] [μ.IsOpenPosMeasure] (f : E →ᵇ F) :
    toLpTop μ 𝕜 f ∈ closure (Set.range fun g : 𝓢(E, F) ↦ g.toLp ∞ μ) ↔
      Tendsto f (cocompact E) (𝓝 0) := by
  constructor
  · intro hf
    refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    obtain ⟨_, ⟨g, rfl⟩, hfg⟩ := Metric.mem_closure_iff.1 hf (ε / 2) (half_pos hε)
    have hnorm : ‖f - g.toBoundedContinuousFunction‖ < ε / 2 := by
      dsimp only at hfg
      rw [dist_eq_norm, g.toLp_top_eq_toLpTop (𝕜 := 𝕜), ← map_sub, norm_toLpTop] at hfg
      exact hfg
    filter_upwards [Metric.tendsto_nhds.1 g.tendsto_cocompact (ε / 2) (half_pos hε)] with x hx
    calc dist (f x) 0 ≤ dist (f x) (g x) + dist (g x) 0 := dist_triangle _ _ _
      _ = ‖(f - g.toBoundedContinuousFunction) x‖ + dist (g x) 0 := by rw [dist_eq_norm]; rfl
      _ ≤ ‖f - g.toBoundedContinuousFunction‖ + dist (g x) 0 :=
          add_le_add ((f - g.toBoundedContinuousFunction).norm_coe_le_norm x) le_rfl
      _ < ε / 2 + ε / 2 := add_lt_add hnorm hx
      _ = ε := add_halves ε
  · intro hf
    refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
    -- Outside a large ball of radius `R`, `‖f x‖ < ε / 3`.
    obtain ⟨K, hK, hKε⟩ := hasBasis_cocompact.mem_iff.1
      (Metric.tendsto_nhds.1 hf (ε / 3) (by positivity))
    obtain ⟨R₀, hKR₀⟩ := hK.isBounded.subset_closedBall (0 : E)
    set R : ℝ := max R₀ 1
    have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right R₀ 1)
    let χ : ContDiffBump (0 : E) := ⟨R, R + 1, hR, by linarith⟩
    set fcut : E → F := fun x ↦ χ x • f x
    have hfcut_cont : Continuous fcut := χ.continuous.smul f.continuous
    have hfcut_supp : HasCompactSupport fcut := χ.hasCompactSupport.smul_right
    have hfcut_dist : ∀ x, ‖f x - fcut x‖ ≤ ε / 3 := fun x ↦ by
      rcases le_or_gt ‖x‖ R with hx | hx
      · have h1 : χ x = 1 := χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hx)
        simp only [fcut, h1, one_smul, sub_self, norm_zero]
        positivity
      · have hxK : x ∈ Kᶜ := fun hxK ↦ by
          have hle : ‖x‖ ≤ R₀ := mem_closedBall_zero_iff.1 (hKR₀ hxK)
          linarith [le_max_left R₀ 1]
        have hfx : ‖f x‖ < ε / 3 := by simpa [dist_zero_right] using hKε hxK
        have hsub : f x - fcut x = (1 - χ x) • f x := by
          simp only [fcut, sub_smul, one_smul]
        rw [hsub, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 χ.le_one)]
        exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [χ.nonneg' x])).trans hfx.le
    -- Mollify `fcut` against a Haar measure at a scale `δ` where it oscillates by `< ε / 3`.
    obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.1
      (hfcut_supp.uniformContinuous_of_continuous hfcut_cont) (ε / 3) (by positivity)
    let ν : Measure E := (Module.finBasis ℝ E).addHaar
    let ρ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
    set g₀ : E → F := ρ.normed ν ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] fcut
    have hg₀_smooth : ContDiff ℝ (⊤ : ℕ∞) g₀ :=
      ρ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
        ρ.contDiff_normed hfcut_cont.locallyIntegrable
    have hg₀_supp : HasCompactSupport g₀ :=
      ρ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hfcut_supp
    set g : 𝓢(E, F) := hg₀_supp.toSchwartzMap hg₀_smooth
    refine ⟨g.toLp ∞ μ, ⟨g, rfl⟩, ?_⟩
    have hpt : ∀ x, ‖f x - g x‖ ≤ 2 * ε / 3 := fun x ↦ by
      have hconv : dist (g x) (fcut x) ≤ ε / 3 :=
        ρ.dist_normed_convolution_le (μ := ν) hfcut_cont.aestronglyMeasurable
          fun y hy ↦ (hδf (Metric.mem_ball.1 hy)).le
      calc ‖f x - g x‖ ≤ ‖f x - fcut x‖ + ‖fcut x - g x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = ‖f x - fcut x‖ + dist (g x) (fcut x) := by rw [dist_comm, dist_eq_norm]
        _ ≤ ε / 3 + ε / 3 := add_le_add (hfcut_dist x) hconv
        _ = 2 * ε / 3 := by ring
    rw [dist_eq_norm]
    refine (Lp.norm_top_le_of_ae_bound (c := 2 * ε / 3) (by positivity) ?_).trans_lt (by linarith)
    filter_upwards [Lp.coeFn_sub (toLpTop μ 𝕜 f) (g.toLp ∞ μ),
      coeFn_toLpTop (𝕜 := 𝕜) μ f, g.coeFn_toLp ∞ μ] with x hsub hf' hg'
    rw [hsub, Pi.sub_apply, hf', hg']
    exact hpt x

end BoundedContinuousFunction

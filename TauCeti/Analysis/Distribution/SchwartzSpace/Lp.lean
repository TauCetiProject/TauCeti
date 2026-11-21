/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.Geometry.Manifold.SmoothApprox
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
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
by a smooth bump and taking a support-preserving smooth approximation produces a Schwartz uniform
approximant.

## Main declarations

* `SchwartzMap.toLp_top_eq_toLpTop`: `g.toLp ∞ μ` agrees with
  `BoundedContinuousFunction.toLpTop μ 𝕜 g.toBoundedContinuousFunction`.
* `BoundedContinuousFunction.toLpTop_mem_closure_range_schwartz_toLp_top_iff`: a bounded continuous
  function lies in the `L^∞(μ)` closure of the Schwartz functions iff it vanishes at infinity.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., §2.2 (Schwartz functions and approximation).
* G. B. Folland, *Real Analysis*, 2nd ed., §8.1 (density of smooth compactly supported functions in
  `C₀`).
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal SchwartzMap Topology

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
theorem toLpTop_mem_closure_range_schwartz_toLp_top_iff {μ : Measure E}
    [μ.HasTemperateGrowth] [μ.IsOpenPosMeasure] (f : E →ᵇ F) :
    toLpTop μ 𝕜 f ∈ closure (Set.range fun g : 𝓢(E, F) ↦ g.toLp ∞ μ) ↔
      Tendsto f (cocompact E) (𝓝 0) := by
  constructor
  · intro hf
    have hiso : Isometry (toLpTop μ 𝕜 : (E →ᵇ F) →L[𝕜] Lp F ∞ μ) :=
      AddMonoidHomClass.isometry_of_norm _ (norm_toLpTop μ)
    have him :
        ((toLpTop μ 𝕜 : (E →ᵇ F) →L[𝕜] Lp F ∞ μ) ''
            Set.range fun g : 𝓢(E, F) ↦ g.toBoundedContinuousFunction) =
          Set.range fun g : 𝓢(E, F) ↦ g.toLp ∞ μ := by
      ext y
      simp [SchwartzMap.toLp_top_eq_toLpTop (𝕜 := 𝕜)]
    have hmem : f ∈ closure (Set.range fun g : 𝓢(E, F) ↦ g.toBoundedContinuousFunction) := by
      rwa [hiso.isUniformInducing.isInducing.closure_eq_preimage_closure_image, Set.mem_preimage,
        him]
    have hsub :
        (Set.range fun g : 𝓢(E, F) ↦ g.toBoundedContinuousFunction) ⊆
          Set.range (ZeroAtInftyContinuousMap.toBCF : ZeroAtInftyContinuousMap E F → E →ᵇ F) :=
      Set.range_subset_iff.2 fun g ↦ ⟨g.toZeroAtInfty, g.toZeroAtInfty_toBCF⟩
    obtain ⟨h, hh⟩ := closure_minimal hsub ZeroAtInftyContinuousMap.isClosed_range_toBCF hmem
    rw [← hh]
    exact zero_at_infty h
  · intro hf
    refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
    -- Outside a compact set `K`, `‖f x‖ < ε / 3`.
    obtain ⟨K, hK, hKε⟩ := hasBasis_cocompact.mem_iff.1
      (Metric.tendsto_nhds.1 hf (ε / 3) (by positivity))
    obtain ⟨χ, hχ_smooth, hχ_range, hχ_one, hχ_supp, -⟩ :=
      hK.exists_contDiff_cutoff isOpen_univ (Set.subset_univ K)
    set fcut : E → F := fun x ↦ χ x • f x
    have hfcut_cont : Continuous fcut := hχ_smooth.continuous.smul f.continuous
    have hfcut_supp : HasCompactSupport fcut := hχ_supp.smul_right
    have hfcut_dist : ∀ x, ‖f x - fcut x‖ ≤ ε / 3 := fun x ↦ by
      by_cases hx : x ∈ K
      · have h1 : χ x = 1 := interior_subset (hχ_one hx)
        simp only [fcut, h1, one_smul, sub_self, norm_zero]
        positivity
      · have hfx : ‖f x‖ < ε / 3 := by simpa [dist_zero_right] using hKε hx
        have hχx : χ x ∈ Set.Icc (0 : ℝ) 1 := hχ_range ⟨x, rfl⟩
        have hsub : f x - fcut x = (1 - χ x) • f x := by simp only [fcut, sub_smul, one_smul]
        rw [hsub, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 hχx.2)]
        exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [hχx.1])).trans hfx.le
    -- Smoothly approximate `fcut` within `ε / 3` while preserving compact support.
    obtain ⟨g₀, hg₀_smooth, hg₀_approx, hg₀_supp⟩ := hfcut_cont.exists_contDiff_approx ⊤
      (ε := fun _ ↦ ε / 3) continuous_const fun _ ↦ by positivity
    set g : 𝓢(E, F) := (hfcut_supp.mono hg₀_supp).toSchwartzMap hg₀_smooth
    refine ⟨g.toLp ∞ μ, ⟨g, rfl⟩, ?_⟩
    have hpt : ∀ x, ‖f x - g x‖ ≤ 2 * ε / 3 := fun x ↦ by
      calc ‖f x - g x‖ ≤ ‖f x - fcut x‖ + ‖fcut x - g x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = ‖f x - fcut x‖ + dist (g x) (fcut x) := by rw [dist_comm, dist_eq_norm]
        _ ≤ ε / 3 + ε / 3 := add_le_add (hfcut_dist x) (hg₀_approx x).le
        _ = 2 * ε / 3 := by ring
    rw [dist_eq_norm]
    refine (Lp.norm_top_le_of_ae_bound (c := 2 * ε / 3) (by positivity) ?_).trans_lt (by linarith)
    filter_upwards [Lp.coeFn_sub (toLpTop μ 𝕜 f) (g.toLp ∞ μ),
      coeFn_toLpTop (𝕜 := 𝕜) μ f, g.coeFn_toLp ∞ μ] with x hsub hf' hg'
    rw [hsub, Pi.sub_apply, hf', hg']
    exact hpt x

end BoundedContinuousFunction

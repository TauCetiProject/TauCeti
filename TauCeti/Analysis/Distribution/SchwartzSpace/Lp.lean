/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Geometry.Manifold.SmoothApprox
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TemperateGrowth

/-!
# Schwartz functions in `L^∞` and uniform approximation

A Schwartz function is bounded and continuous, so it has two canonical embeddings into `L^∞(μ)` for
any measure `μ` of temperate growth: directly via `SchwartzMap.toLp ∞ μ` and via
`BoundedContinuousFunction.toLpTop μ 𝕜` applied to `SchwartzMap.toBoundedContinuousFunction`. The
two classes coincide (`SchwartzMap.toLp_top_eq_toLpTop`).

For `p < ∞` the Schwartz functions are dense in `Lᵖ(μ)`, so a linear functional on them bounded by
a multiple of the `Lᵖ` norm extends to a continuous linear functional on `Lᵖ(μ)` with the same
bound (`SchwartzMap.exists_strongDual_apply_toLp_eq`).

Whereas Schwartz functions are dense in `Lᵖ(μ)` for `p < ∞` (`SchwartzMap.denseRange_toLpCLM`),
they are not dense in `L^∞(μ)`. On bounded continuous functions, for any temperate measure `μ`
positive on nonempty open sets, a bounded continuous function lies in the `L^∞(μ)` closure of the
Schwartz functions exactly when it vanishes at infinity along `cocompact E`
(`BoundedContinuousFunction.toLpTop_mem_closure_range_schwartz_toLp_top_iff`): uniform limits of
Schwartz functions vanish at infinity, and conversely cutting off a function vanishing at infinity
by a smooth bump and taking a support-preserving smooth approximation produces a Schwartz uniform
approximant (`Continuous.exists_schwartzMap_norm_sub_le`).

## Main declarations

* `SchwartzMap.toLp_top_eq_toLpTop`: `g.toLp ∞ μ` agrees with
  `BoundedContinuousFunction.toLpTop μ 𝕜 g.toBoundedContinuousFunction`.
* `SchwartzMap.exists_strongDual_apply_toLp_eq`: a linear functional on the Schwartz functions
  bounded in `Lᵖ(μ)`, `p < ∞`, extends to `Lᵖ(μ)`.
* `Continuous.exists_schwartzMap_norm_sub_le`: a continuous function vanishing at infinity can be
  uniformly approximated by Schwartz functions.
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

variable [FiniteDimensional ℝ E] {μ : Measure E} [μ.HasTemperateGrowth] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Extension from the Schwartz functions.** A linear functional `S` on the Schwartz functions
with `‖S g‖ ≤ B ‖g‖_p`, `p < ∞`, extends from the dense Schwartz functions to a continuous linear
functional on `Lᵖ(μ)` of norm at most `B`. -/
theorem exists_strongDual_apply_toLp_eq (hp_top : p ≠ ∞) (S : 𝓢(E, ℂ) →ₗ[ℂ] ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hS : ∀ g : 𝓢(E, ℂ), ‖S g‖ ≤ B * ‖g.toLp p μ‖) :
    ∃ Λ : StrongDual ℂ (Lp ℂ p μ), ‖Λ‖ ≤ B ∧ ∀ g : 𝓢(E, ℂ), Λ (g.toLp p μ) = S g := by
  have := Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts μ
  set e : 𝓢(E, ℂ) →ₗ[ℂ] Lp ℂ p μ := (toLpCLM ℂ ℂ p μ).toLinearMap
  have he : DenseRange e := by
    have hcoe : ⇑e = ⇑(toLpCLM ℝ ℂ p μ) := by
      ext g : 1
      simp [e]
    rw [DenseRange, hcoe]
    exact denseRange_toLpCLM hp_top
  have hS' : ∀ g, ‖S g‖ ≤ B * ‖e g‖ := fun g ↦ by simpa [e] using hS g
  refine ⟨S.extendOfNorm e, (S.extendOfNorm e).opNorm_le_bound hB
    (LinearMap.norm_extendOfNorm_apply_le he B hS'), fun g ↦ ?_⟩
  simpa [e] using LinearMap.extendOfNorm_eq he ⟨B, hS'⟩ g

end SchwartzMap

/-- **Uniform approximation of `C₀` functions by Schwartz functions.** Any continuous function
vanishing at infinity along `cocompact E` can be uniformly approximated by Schwartz functions. -/
theorem Continuous.exists_schwartzMap_norm_sub_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hfc : Continuous f) (hf : Tendsto f (cocompact E) (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : 𝓢(E, F), ∀ x, ‖f x - g x‖ ≤ ε := by
  -- Outside a compact set `K`, `‖f x‖ < ε / 2`.
  obtain ⟨K, hK, hKε⟩ := hasBasis_cocompact.mem_iff.1
    (Metric.tendsto_nhds.1 hf (ε / 2) (by positivity))
  obtain ⟨χ, hχ_smooth, hχ_range, hχ_one, hχ_supp, -⟩ :=
    hK.exists_contDiff_cutoff isOpen_univ (Set.subset_univ K)
  set fcut : E → F := fun x ↦ χ x • f x
  have hfcut_cont : Continuous fcut := hχ_smooth.continuous.smul hfc
  have hfcut_supp : HasCompactSupport fcut := hχ_supp.smul_right
  have hfcut_dist : ∀ x, ‖f x - fcut x‖ ≤ ε / 2 := fun x ↦ by
    by_cases hx : x ∈ K
    · have h1 : χ x = 1 := interior_subset (hχ_one hx)
      simp only [fcut, h1, one_smul, sub_self, norm_zero]
      positivity
    · have hfx : ‖f x‖ < ε / 2 := by simpa [dist_zero_right] using hKε hx
      have hχx : χ x ∈ Set.Icc (0 : ℝ) 1 := hχ_range ⟨x, rfl⟩
      have hsub : f x - fcut x = (1 - χ x) • f x := by simp only [fcut, sub_smul, one_smul]
      rw [hsub, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 hχx.2)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [hχx.1])).trans hfx.le
  -- Smoothly approximate `fcut` within `ε / 2` while preserving compact support.
  obtain ⟨g₀, hg₀_smooth, hg₀_approx, hg₀_supp⟩ := hfcut_cont.exists_contDiff_approx ⊤
    (ε := fun _ ↦ ε / 2) continuous_const fun _ ↦ by positivity
  refine ⟨(hfcut_supp.mono hg₀_supp).toSchwartzMap hg₀_smooth, fun x ↦ ?_⟩
  have hg : ((hfcut_supp.mono hg₀_supp).toSchwartzMap hg₀_smooth) x = g₀ x :=
    HasCompactSupport.toSchwartzMap_toFun _ _ x
  calc ‖f x - ((hfcut_supp.mono hg₀_supp).toSchwartzMap hg₀_smooth) x‖
      ≤ ‖f x - fcut x‖ + ‖fcut x - g₀ x‖ := by
        rw [hg]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖f x - fcut x‖ + dist (g₀ x) (fcut x) := by rw [dist_comm, dist_eq_norm]
    _ ≤ ε / 2 + ε / 2 := add_le_add (hfcut_dist x) (hg₀_approx x).le
    _ = ε := add_halves ε

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
    obtain ⟨g, hpt⟩ := f.continuous.exists_schwartzMap_norm_sub_le hf (half_pos hε)
    refine ⟨g.toLp ∞ μ, ⟨g, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    refine (Lp.norm_le_of_ae_bound_top (C := ε / 2) (by positivity) ?_).trans_lt (half_lt_self hε)
    filter_upwards [Lp.coeFn_sub (toLpTop μ 𝕜 f) (g.toLp ∞ μ),
      coeFn_toLpTop (𝕜 := 𝕜) μ f, g.coeFn_toLp ∞ μ] with x hsub hf' hg'
    rw [hsub, Pi.sub_apply, hf', hg']
    exact hpt x

end BoundedContinuousFunction

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Topology.Maps.Proper.KernelSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth properly supported diagonal cutoffs

On any finite-dimensional real normed space `E`, subtracting a smooth compactly supported bump
function `b (x - y)` produces a smooth `[0, 1]`-valued properly supported cutoff equal to `1` on a
tube `‖x - y‖ ≤ r` (hence on a neighborhood of every diagonal point `(x, x)`) and vanishing when
`‖x - y‖ ≥ R`, whenever `0 < R` and `r < R`
(`TauCeti.exists_contDiff_hasProperSupport_eventuallyEq_one_diagonal`).
-/

public section

open Filter Function Set
open scoped ContDiff Topology

namespace TauCeti

/-- Every finite-dimensional real normed space admits a smooth `[0, 1]`-valued properly supported
cutoff equal to `1` when `‖x - y‖ ≤ r` (hence on a neighborhood of every diagonal point `(x, x)`)
and vanishing when `‖x - y‖ ≥ R`, whenever `0 < R` and `r < R`. -/
theorem exists_contDiff_hasProperSupport_eventuallyEq_one_diagonal {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {r R : ℝ}
    (hR : 0 < R) (hrR : r < R) :
    ∃ χ : E → E → ℝ, ContDiff ℝ ∞ (uncurry χ) ∧ range (uncurry χ) ⊆ Icc 0 1 ∧
      HasProperSupport χ ∧ (∀ x : E, uncurry χ =ᶠ[𝓝 (x, x)] 1) ∧
      (∀ x y : E, ‖x - y‖ ≤ r → χ x y = 1) ∧ ∀ x y : E, R ≤ ‖x - y‖ → χ x y = 0 := by
  set r' := max r (R / 2)
  have hr' : 0 < r' := (half_pos hR).trans_le (le_max_right r (R / 2))
  let b : ContDiffBump (0 : E) := ⟨r', R, hr', max_lt hrR (half_lt_self hR)⟩
  have hone : ∀ x y : E, ‖x - y‖ ≤ r → b (x - y) = 1 := fun x y hxy ↦
    b.one_of_mem_closedBall
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hxy.trans (le_max_left r _))
  refine ⟨fun x y ↦ b (x - y), (b.contDiff (n := ⊤)).comp (contDiff_fst.sub contDiff_snd),
    range_subset_iff.2 fun p ↦ ⟨b.nonneg' _, b.le_one⟩,
    hasProperSupport_comp_sub b.hasCompactSupport, fun x ↦ ?_, hone,
    fun x y hxy ↦ b.zero_of_le_dist (by simpa [dist_eq_norm] using hxy)⟩
  have hsub : Tendsto (fun p : E × E ↦ p.1 - p.2) (𝓝 (x, x)) (𝓝 (x - x)) :=
    (continuous_fst.sub continuous_snd).tendsto (x, x)
  rw [sub_self] at hsub
  filter_upwards [hsub (Metric.closedBall_mem_nhds 0 hr')] with p hp
  exact b.one_of_mem_closedBall hp

end TauCeti

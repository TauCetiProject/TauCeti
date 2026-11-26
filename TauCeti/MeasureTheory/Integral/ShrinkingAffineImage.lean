/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Integrals along shrinking affine images of a compact set

Let `K` be a compact subset of a topological space `X`, `L : X → E` a continuous map into a
topological vector space and `c` a point of `E`. As `t → 0`, the affine images `y ↦ c + t • L y`
of `K` eventually lie in any given neighbourhood of `c`
(`IsCompact.eventually_forall_add_smul_mem`). Consequently, for a measure which is finite on
compact sets and a function `Φ` continuous near `c`, the integral over `K` of `Φ (c + t • L y)`
tends to `μ K • Φ c` (`IsCompact.tendsto_setIntegral_add_smul`), by dominated convergence with a
constant bound.

This is how a pointwise value of a continuous integrand is recovered from its integrals over small
affine simplices, as in the proof that a continuous form with integer integrals over all smooth
simplices vanishes.
-/

public section

open Filter Topology MeasureTheory

namespace TauCeti

variable {X E : Type*} [TopologicalSpace X] [AddCommGroup E] [TopologicalSpace E]
  [ContinuousAdd E] {K : Set X} {L : X → E} {c : E}

/-- For `t` near `0`, the affine map `y ↦ c + t • L y` sends a compact set `K` into a given
neighbourhood of `c`. -/
theorem _root_.IsCompact.eventually_forall_add_smul_mem {𝕜 : Type*} [Semiring 𝕜]
    [TopologicalSpace 𝕜] [Module 𝕜 E] [ContinuousSMul 𝕜 E] (hK : IsCompact K)
    (hL : Continuous L) {U : Set E} (hU : U ∈ 𝓝 c) :
    ∀ᶠ t in 𝓝 (0 : 𝕜), ∀ y ∈ K, c + t • L y ∈ U := by
  refine hK.eventually_forall_of_forall_eventually fun y _ ↦ ?_
  have hcont : Continuous fun q : 𝕜 × X ↦ c + q.1 • L q.2 := by fun_prop
  have hlim : Tendsto (fun q : 𝕜 × X ↦ c + q.1 • L q.2) (𝓝 (0, y)) (𝓝 c) := by
    simpa using hcont.tendsto (0, y)
  exact hlim.eventually hU

/-- **Integrals over shrinking affine images.** If `Φ` is continuous at every point near `c`, the
integral over a compact set `K` of `Φ` along the affine map `y ↦ c + t • L y` tends to
`μ K • Φ c` as `t → 0`, for any measure finite on compact sets. -/
theorem _root_.IsCompact.tendsto_setIntegral_add_smul [Module ℝ E] [ContinuousSMul ℝ E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ] (hK : IsCompact K)
    (hKm : MeasurableSet K) (hL : Continuous L) {Φ : E → G}
    (hΦ : ∀ᶠ z in 𝓝 c, ContinuousAt Φ z) :
    Tendsto (fun t : ℝ ↦ ∫ y in K, Φ (c + t • L y) ∂μ) (𝓝 0) (𝓝 (μ.real K • Φ c)) := by
  -- For `t` near `0`, the affine image of `K` lies where `Φ` is continuous and bounded by
  -- `‖Φ c‖ + 1`.
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y ∈ K,
      c + t • L y ∈ {z | ContinuousAt Φ z ∧ ‖Φ z‖ < ‖Φ c‖ + 1} :=
    hK.eventually_forall_add_smul_mem hL
      (hΦ.and (hΦ.self_of_nhds.norm.eventually (gt_mem_nhds (lt_add_one _))))
  -- Dominated convergence, with a constant bound on the compact set.
  have hG : ContinuousAt (fun t : ℝ ↦ ∫ y in K, Φ (c + t • L y) ∂μ) 0 := by
    refine continuousAt_of_dominated (bound := fun _ ↦ ‖Φ c‖ + 1) ?_ ?_
      (integrableOn_const hK.measure_lt_top.ne) ?_
    · filter_upwards [hev] with t ht
      refine ContinuousOn.aestronglyMeasurable_of_isCompact (fun y hy ↦ ?_) hK hKm
      exact ((ht y hy).1.comp (f := fun y ↦ c + t • L y)
        (by fun_prop : Continuous fun y ↦ c + t • L y).continuousAt).continuousWithinAt
    · filter_upwards [hev] with t ht
      exact ae_restrict_of_forall_mem hKm fun y hy ↦ (ht y hy).2.le
    · refine ae_of_all _ fun y ↦ ?_
      have h0 : ContinuousAt Φ (c + (0 : ℝ) • L y) := by simpa using hΦ.self_of_nhds
      exact h0.comp (f := fun t : ℝ ↦ c + t • L y)
        (by fun_prop : Continuous fun t : ℝ ↦ c + t • L y).continuousAt
  simpa using hG.tendsto

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.UniformSpace.Equicontinuity
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.UniformConvergence
import TauCeti.Topology.MetricSpace.Equicontinuity

/-!
# Uniform convergence from convergence in measure

Let `U` be a totally bounded open subset of a pseudometric space `X`, and let `μ` be a measure on
`X` that charges every nonempty open set. For functions on `U` with a common modulus of
continuity, closeness in measure forces uniform closeness: every point of `U` lies in one of
finitely many small balls covering `U`, and each such ball meets `U` in a set of positive measure,
so it contains a point where the two functions are close.

Hence a family of functions uniformly equicontinuous on `U` that converges in measure on `U`
converges uniformly on `U` when its limit is uniformly continuous on `U`
(`MeasureTheory.TendstoInMeasure.tendstoUniformlyOn_of_uniformEquicontinuousOn`), and is uniformly
Cauchy on `U` whatever its limit
(`MeasureTheory.TendstoInMeasure.uniformCauchySeqOn_of_uniformEquicontinuousOn`). This is how
`L²` convergence of functions with uniform Hölder bounds, such as the solutions of elliptic
equations, is upgraded to uniform convergence.

## Main declarations

* `MeasureTheory.exists_pos_forall_dist_lt_of_measure_lt`: the quantitative estimate.
* `MeasureTheory.TendstoInMeasure.tendstoUniformlyOn_of_uniformEquicontinuousOn` and
  `MeasureTheory.TendstoInMeasure.uniformCauchySeqOn_of_uniformEquicontinuousOn`: convergence in
  measure of a uniformly equicontinuous family is uniform.
-/

public section

open Filter Metric Set
open scoped ENNReal Topology Uniformity

namespace MeasureTheory

variable {X Y ι : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X}
  [μ.IsOpenPosMeasure] [PseudoMetricSpace Y] {U : Set X}

/-- **Closeness in measure gives uniform closeness.** Let `U` be a totally bounded open set and
`δ > 0`. There is `η > 0` such that any two functions `f, g` whose values move by at most `c`
between points of `U` at distance less than `δ`, and with `ε ≤ dist (f x) (g x)` only on a set of
measure less than `η` in `U`, satisfy `dist (f x) (g x) < ε + 2 c` at every point `x ∈ U`. -/
theorem exists_pos_forall_dist_lt_of_measure_lt (hU : IsOpen U) (hUt : TotallyBounded U)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ≥0∞, 0 < η ∧ ∀ (f g : X → Y) (ε c : ℝ),
      (∀ x ∈ U, ∀ y ∈ U, dist x y < δ → dist (f x) (f y) ≤ c) →
      (∀ x ∈ U, ∀ y ∈ U, dist x y < δ → dist (g x) (g y) ≤ c) →
      μ.restrict U {x | ε ≤ dist (f x) (g x)} < η → ∀ x ∈ U, dist (f x) (g x) < ε + 2 * c := by
  obtain ⟨t, htU, htf, hUt⟩ := finite_approx_of_totallyBounded hUt (δ / 2) (half_pos hδ)
  -- `η` is the least measure of the finitely many sets `U ∩ ball y (δ / 2)`, `y ∈ t`.
  refine ⟨htf.toFinset.inf fun y ↦ μ (U ∩ ball y (δ / 2)), ?_, ?_⟩
  · refine (Finset.lt_inf_iff ENNReal.zero_lt_top).2 fun y hy ↦ ?_
    exact (hU.inter isOpen_ball).measure_pos μ
      ⟨y, htU (htf.mem_toFinset.1 hy), mem_ball_self (half_pos hδ)⟩
  intro f g ε c hf hg hμ x hx
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.1 (hUt hx)
  -- Some point `z` of `U ∩ ball y (δ / 2)` has `dist (f z) (g z) < ε`.
  obtain ⟨z, ⟨hzU, hzy⟩, hz⟩ : ∃ z ∈ U ∩ ball y (δ / 2), dist (f z) (g z) < ε := by
    by_contra! hle
    refine (Finset.inf_le (htf.mem_toFinset.2 hyt)).not_gt (hμ.trans_le' ?_)
    calc μ (U ∩ ball y (δ / 2)) = μ ((U ∩ ball y (δ / 2)) ∩ U) := by
          rw [inter_eq_left.2 inter_subset_left]
      _ ≤ μ.restrict U (U ∩ ball y (δ / 2)) := Measure.le_restrict_apply _ _
      _ ≤ μ.restrict U {x | ε ≤ dist (f x) (g x)} := measure_mono hle
  have hxz : dist x z < δ := by
    calc dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add (mem_ball.1 hxy) (mem_ball'.1 hzy)
      _ = δ := add_halves δ
  calc dist (f x) (g x) ≤ dist (f x) (f z) + dist (f z) (g z) + dist (g z) (g x) :=
        dist_triangle4 _ _ _ _
    _ < c + ε + c := by
        linarith [hf x hx z hzU hxz, hg z hzU x hx (by rwa [dist_comm])]
    _ = ε + 2 * c := by ring

/-- **Convergence in measure of a uniformly equicontinuous family is uniform.** Let `U` be a
totally bounded open set. If functions `F i`, uniformly equicontinuous on `U`, converge in measure
on `U` to a function `g` uniformly continuous on `U`, then they converge to `g` uniformly on `U`. -/
theorem TendstoInMeasure.tendstoUniformlyOn_of_uniformEquicontinuousOn (hU : IsOpen U)
    (hUt : TotallyBounded U) {l : Filter ι} {F : ι → X → Y} {g : X → Y}
    (hF : UniformEquicontinuousOn F U) (hg : UniformContinuousOn g U)
    (h : TendstoInMeasure (μ.restrict U) F l g) : TendstoUniformlyOn F g l U := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨δ₁, hδ₁, hF'⟩ := Metric.uniformEquicontinuousOn_iff.1 hF _ hε3
  obtain ⟨δ₂, hδ₂, hg'⟩ := Metric.uniformContinuousOn_iff.1 hg (ε / 3) hε3
  obtain ⟨η, hη, hclose⟩ := exists_pos_forall_dist_lt_of_measure_lt (μ := μ) (Y := Y) hU hUt
    (lt_min hδ₁ hδ₂)
  have hlim := tendstoInMeasure_iff_dist.1 h (ε / 3) hε3
  filter_upwards [hlim.eventually (gt_mem_nhds hη)] with i hi x hx
  rw [dist_comm]
  calc dist (F i x) (g x) < ε / 3 + 2 * (ε / 3) :=
        hclose (F i) g (ε / 3) (ε / 3)
          (fun x hx y hy hxy ↦ (hF' x hx y hy (hxy.trans_le (min_le_left _ _)) i).le)
          (fun x hx y hy hxy ↦ (hg' x hx y hy (hxy.trans_le (min_le_right _ _))).le) hi x hx
    _ = ε := by ring

/-- **Convergence in measure of a uniformly equicontinuous family is uniformly Cauchy.** Let `U`
be a totally bounded open set. If functions `F i`, uniformly equicontinuous on `U`, converge in
measure on `U` to some function `g`, then they are uniformly Cauchy on `U`. No regularity of `g` is
needed. -/
theorem TendstoInMeasure.uniformCauchySeqOn_of_uniformEquicontinuousOn (hU : IsOpen U)
    (hUt : TotallyBounded U) {l : Filter ι} {F : ι → X → Y} {g : X → Y}
    (hF : UniformEquicontinuousOn F U) (h : TendstoInMeasure (μ.restrict U) F l g) :
    UniformCauchySeqOn F l U := by
  intro V hV
  obtain ⟨ε, hε, hεV⟩ := mem_uniformity_dist.1 hV
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨δ, hδ, hF'⟩ := Metric.uniformEquicontinuousOn_iff.1 hF _ hε3
  obtain ⟨η, hη, hclose⟩ := exists_pos_forall_dist_lt_of_measure_lt (μ := μ) (Y := Y) hU hUt hδ
  -- `F i` and `F j` are at distance at least `ε / 3` only where one of them is at distance at
  -- least `ε / 6` from `g`.
  have hε6 : 0 < ε / 6 := by positivity
  have hlim := tendstoInMeasure_iff_dist.1 h (ε / 6) hε6
  have hsum : Tendsto (fun p : ι × ι ↦ μ.restrict U {x | ε / 6 ≤ dist (F p.1 x) (g x)} +
      μ.restrict U {x | ε / 6 ≤ dist (F p.2 x) (g x)}) (l ×ˢ l) (𝓝 0) := by
    simpa using (hlim.comp tendsto_fst).add (hlim.comp tendsto_snd)
  filter_upwards [hsum.eventually (gt_mem_nhds hη)] with p hp x hx
  refine hεV ?_
  have hsub : {x | ε / 3 ≤ dist (F p.1 x) (F p.2 x)} ⊆
      {x | ε / 6 ≤ dist (F p.1 x) (g x)} ∪ {x | ε / 6 ≤ dist (F p.2 x) (g x)} := by
    intro y hy
    rw [mem_ofPred_eq] at hy
    by_contra hlt
    simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hlt
    linarith [dist_triangle_right (F p.1 y) (F p.2 y) (g y)]
  calc dist (F p.1 x) (F p.2 x) < ε / 3 + 2 * (ε / 3) :=
        hclose (F p.1) (F p.2) (ε / 3) (ε / 3) (fun x hx y hy hxy ↦ (hF' x hx y hy hxy _).le)
          (fun x hx y hy hxy ↦ (hF' x hx y hy hxy _).le)
          ((measure_mono hsub).trans_lt ((measure_union_le _ _).trans_lt hp)) x hx
    _ = ε := by ring

end MeasureTheory

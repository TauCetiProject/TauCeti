/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.Calculus.FDeriv.ImageCone
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Tangent cones and unique differentiability at Haar density-one points

At any point `x` where a set `s` has density one with respect to an additive Haar measure on a
finite-dimensional real normed space, `s` meets small rescaled neighborhoods in every direction, so
`posTangentConeAt s x = univ`, `tangentConeAt ℝ s x = univ`, and relative derivatives within `s` at
`x` are unique. Combining this with `HasFDerivWithinAt.antilipschitzWith_of_tangentConeAt_eq_univ`
transfers inverse-Lipschitz bounds of a parametrization on `s` to its relative derivative at `x`.

## Main results

* `MeasureTheory.Measure.tendsto_inter_closedBall_div_of_mem_nhds`: neighborhoods of `x` have
  closed-ball density one for any locally finite measure positive on open sets.
* `MeasureTheory.Measure.mem_closure_of_tendsto_inter_closedBall_div`: any closed-ball density-one
  point of `s` belongs to `closure s`.
* `MeasureTheory.Measure.posTangentConeAt_eq_univ_of_tendsto_inter_closedBall_div`,
  `MeasureTheory.Measure.tangentConeAt_eq_univ_of_tendsto_inter_closedBall_div`,
  `MeasureTheory.Measure.uniqueDiffWithinAt_of_tendsto_inter_closedBall_div`: Haar density-one
  points have full tangent cones and unique relative derivatives.
* `HasFDerivWithinAt.antilipschitzWith_of_tendsto_inter_closedBall_div`,
  `HasFDerivWithinAt.injective_of_tendsto_inter_closedBall_div`: at a Haar density-one point, an
  inverse-Lipschitz parametrization has an antilipschitz (hence injective) derivative.

## References

* H. Federer, *Geometric Measure Theory*, §3.2.16.
* L. Simon, *Lectures on Geometric Measure Theory*, §11.
-/

public section

open Filter Function Metric MeasureTheory Set
open scoped ENNReal NNReal Pointwise Topology

namespace MeasureTheory.Measure

/-- Every neighborhood `s ∈ 𝓝 x` has closed-ball density one at `x` for any locally finite measure
that is positive on nonempty open sets. -/
theorem tendsto_inter_closedBall_div_of_mem_nhds {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {s : Set X} {x : X} (hs : s ∈ 𝓝 x) :
    Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Metric.eventually_measure_closedBall_ne_zero_ne_top μ x,
    eventually_nhdsWithin_of_eventually_nhds (eventually_closedBall_subset hs)] with r hr hsub
  rw [inter_eq_right.2 hsub, ENNReal.div_self hr.1 hr.2]

/-- A point at which `s` has closed-ball density one with respect to `μ` belongs to `closure s`. -/
theorem mem_closure_of_tendsto_inter_closedBall_div {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] (μ : Measure X) {s : Set X} {x : X}
    (hs : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) :
    x ∈ closure s := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, hr, _, hrε⟩ := (((tendsto_order.1 hs).1 0 zero_lt_one).and (Ioo_mem_nhdsGT hε)).exists
  obtain ⟨y, hys, hyr⟩ : (s ∩ closedBall x r).Nonempty :=
    nonempty_of_measure_ne_zero (μ := μ) fun h0 => by simp [h0] at hr
  exact ⟨y, hys, (dist_comm x y).trans_lt ((mem_closedBall.1 hyr).trans_lt hrε)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- At a Haar density-one point of an arbitrary set `s`, `posTangentConeAt s x = univ`. -/
theorem posTangentConeAt_eq_univ_of_tendsto_inter_closedBall_div (μ : Measure E)
    [μ.IsAddHaarMeasure] {s : Set E} {x : E}
    (hs : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) :
    posTangentConeAt s x = univ := by
  ext v
  simp only [mem_univ, iff_true]
  -- Rescaled closed balls around `v` meet `s - {x}` at arbitrarily small positive scales `r n`.
  have hex (n : ℕ) : ∃ r : ℝ, 0 < r ∧ r < ((n : ℝ) + 1)⁻¹ ∧
      ∃ a ∈ closedBall v ((n : ℝ) + 1)⁻¹, x + r • a ∈ s := by
    obtain ⟨r, ⟨y, hys, x', hx', _, ⟨a, ha, rfl⟩, rfl⟩, hr0, hrε⟩ :=
      ((eventually_nonempty_inter_smul_of_density_one μ s x hs (closedBall v ((n : ℝ) + 1)⁻¹)
        measurableSet_closedBall (measure_closedBall_pos μ v (by positivity)).ne').and
        (Ioo_mem_nhdsGT (by positivity : 0 < ((n : ℝ) + 1)⁻¹))).exists
    exact ⟨r, hr0, hrε, a, ha, mem_singleton_iff.1 hx' ▸ hys⟩
  choose r hr0 hrε a ha hxs using hex
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have ha_lim : Tendsto a atTop (𝓝 v) := tendsto_iff_norm_sub_tendsto_zero.2 <|
    squeeze_zero (fun _ => norm_nonneg _) (fun n => mem_closedBall_iff_norm.1 (ha n)) hinv
  have hr_lim := squeeze_zero (fun n => (hr0 n).le) (fun n => (hrε n).le) hinv
  refine mem_tangentConeAt_of_seq atTop (fun n => Real.toNNReal (r n)⁻¹)
    (fun n => r n • a n) (by simpa only [zero_smul] using hr_lim.smul ha_lim)
    (Eventually.of_forall hxs) (ha_lim.congr fun n => ?_)
  rw [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.2 (hr0 n).le), inv_smul_smul₀ (hr0 n).ne']

/-- At a Haar density-one point of an arbitrary set `s`, `tangentConeAt ℝ s x = univ`. -/
theorem tangentConeAt_eq_univ_of_tendsto_inter_closedBall_div (μ : Measure E) [μ.IsAddHaarMeasure]
    {s : Set E} {x : E}
    (hs : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) :
    tangentConeAt ℝ s x = univ :=
  eq_univ_of_subset tangentConeAt_mono_field
    (μ.posTangentConeAt_eq_univ_of_tendsto_inter_closedBall_div hs)

/-- At a Haar density-one point of an arbitrary set `s`, relative derivatives within `s` are
unique. -/
theorem uniqueDiffWithinAt_of_tendsto_inter_closedBall_div (μ : Measure E) [μ.IsAddHaarMeasure]
    {s : Set E} {x : E}
    (hs : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) :
    UniqueDiffWithinAt ℝ s x := by
  refine ⟨?_, μ.mem_closure_of_tendsto_inter_closedBall_div hs⟩
  rw [μ.tangentConeAt_eq_univ_of_tendsto_inter_closedBall_div hs, Submodule.span_univ,
    Submodule.top_coe]
  exact dense_univ

end MeasureTheory.Measure

namespace HasFDerivWithinAt

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {f : U → V} {s : Set U} {x₀ : U} {A : U →L[ℝ] V} {L : ℝ≥0}

/-- At a Haar density-one point of `s`, an inverse-Lipschitz parametrization has an antilipschitz
derivative with the same constant. -/
theorem antilipschitzWith_of_tendsto_inter_closedBall_div (μ : Measure U) [μ.IsAddHaarMeasure]
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => μ (s ∩ closedBall x₀ r) / μ (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1)) :
    AntilipschitzWith L A :=
  hf.antilipschitzWith_of_tangentConeAt_eq_univ hx₀ hi
    (μ.tangentConeAt_eq_univ_of_tendsto_inter_closedBall_div hs)

/-- At a Haar density-one point of `s`, an inverse-Lipschitz parametrization has an injective
derivative. -/
theorem injective_of_tendsto_inter_closedBall_div (μ : Measure U) [μ.IsAddHaarMeasure]
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => μ (s ∩ closedBall x₀ r) / μ (closedBall x₀ r)) (𝓝[>] 0) (𝓝 1)) :
    Injective A :=
  (hf.antilipschitzWith_of_tendsto_inter_closedBall_div μ hx₀ hi hs).injective

end HasFDerivWithinAt

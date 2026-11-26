/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.Calculus.FDeriv.ImageCone
import TauCeti.MeasureTheory.Covering.EssentialBoundary.Basic

/-!
# Tangent cones and unique differentiability at Haar density-one points

At any point `x` where a set `s` has density one with respect to an additive Haar measure on a
finite-dimensional real normed space, `posTangentConeAt s x = univ`, `tangentConeAt ℝ s x = univ`,
and relative derivatives within `s` at `x` are unique
(`MeasureTheory.Measure.posTangentConeAt_eq_univ_of_tendsto_inter_closedBall_div`,
`MeasureTheory.Measure.uniqueDiffWithinAt_of_tendsto_inter_closedBall_div`), transferring
inverse-Lipschitz bounds on `s` to the relative derivative
(`HasFDerivWithinAt.antilipschitzWith_of_tendsto_inter_closedBall_div`).

## References

* H. Federer, *Geometric Measure Theory*, §3.2.16; L. Simon, *Lectures on GMT*, §11.
-/

public section

open Filter Function Metric MeasureTheory Set
open scoped ENNReal NNReal Pointwise Topology

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- At a Haar density-one point of an arbitrary set `s`, `posTangentConeAt s x = univ`. -/
theorem posTangentConeAt_eq_univ_of_tendsto_inter_closedBall_div (μ : Measure E)
    [μ.IsAddHaarMeasure] {s : Set E} {x : E}
    (hs : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) :
    posTangentConeAt s x = univ := by
  ext v; simp only [mem_univ, iff_true]
  -- Rescaled closed balls around `v` meet `s - {x}` at arbitrarily small positive scales `r n`.
  have hex (n : ℕ) : ∃ r : ℝ, 0 < r ∧ r < ((n : ℝ) + 1)⁻¹ ∧
      ∃ a ∈ closedBall v ((n : ℝ) + 1)⁻¹, x + r • a ∈ s := by
    obtain ⟨r, ⟨y, hys, hyB⟩, hr0, hrε⟩ :=
      ((eventually_nonempty_inter_smul_of_density_one μ s x hs (closedBall v ((n : ℝ) + 1)⁻¹)
        measurableSet_closedBall (measure_closedBall_pos μ v (by positivity)).ne').and
        (Ioo_mem_nhdsGT (by positivity : 0 < ((n : ℝ) + 1)⁻¹))).exists
    rw [singleton_add, mem_image] at hyB
    obtain ⟨_, hz, rfl⟩ := hyB
    obtain ⟨a, ha, rfl⟩ := mem_smul_set.1 hz
    exact ⟨r, hr0, hrε, a, ha, hys⟩
  choose r hr0 hrε a ha hxs using hex
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have ha_lim : Tendsto a atTop (𝓝 v) := tendsto_iff_norm_sub_tendsto_zero.2 <|
    squeeze_zero (fun _ => norm_nonneg _) (fun n => mem_closedBall_iff_norm.1 (ha n)) hinv
  have hr_lim := squeeze_zero (fun n => (hr0 n).le) (fun n => (hrε n).le) hinv
  refine mem_tangentConeAt_of_seq atTop (fun n => Real.toNNReal (r n)⁻¹) (fun n => r n • a n)
    (by simpa only [zero_smul] using hr_lim.smul ha_lim) (Eventually.of_forall hxs)
    (ha_lim.congr fun n => ?_)
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
  refine ⟨?_, TauCeti.essentialInterior_subset_closure
    (TauCeti.mem_essentialInterior.2 (TauCeti.hasDensityAt_iff.2 hs))⟩
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

/-- Origin-centered Haar-ball variant of `injective_of_tendsto_inter_closedBall_div`. -/
theorem injective_of_tendsto_inter_closedBall_div_zero (μ : Measure U) [μ.IsAddHaarMeasure]
    (hf : HasFDerivWithinAt f A s x₀) (hx₀ : x₀ ∈ s) (hi : AntilipschitzWith L (s.domRestrict f))
    (hs : Tendsto (fun r => μ (s ∩ closedBall x₀ r) / μ (closedBall 0 r)) (𝓝[>] 0) (𝓝 1)) :
    Injective A :=
  hf.injective_of_tendsto_inter_closedBall_div μ hx₀ hi
    (hs.congr fun _ => by rw [μ.addHaar_closedBall_center x₀])

end HasFDerivWithinAt

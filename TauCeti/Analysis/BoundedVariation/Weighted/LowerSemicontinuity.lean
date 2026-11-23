/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Lower semicontinuity of the weighted variation

For a `C¹` weight `W`, the weighted variation `V_μ(u; Ω)` (`TauCeti.weightedVariation`) is lower
semicontinuous for `L¹_loc(Ω)` convergence: if `u i → u₀` in `L¹_loc(Ω)` then
`V_μ(u₀; Ω) ≤ liminf V_μ(u i; Ω)` (`TauCeti.weightedVariation_le_liminf`). Each pairing
`u ↦ ∫ u div_μ X dμ` with an admissible test vector field `X` is continuous for this convergence,
the weighted divergence `(div X − DW X) e^{−W}` being continuous with compact support in `Ω`, and
the weighted variation is their supremum.

For sets, convergence in `L¹_loc(Ω)` of the indicators is local convergence in measure, and the
weighted perimeter is lower semicontinuous for it (`TauCeti.weightedPerimeter_le_liminf`); in
particular so is the Gaussian perimeter (`TauCeti.gaussianPerimeter_le_liminf`). The inequality
can be strict: in `ℝ`, the sets `(−1, 1) ∪ (1 + 1/k, 2)` converge to `(−1, 2)`, and their Gaussian
perimeters `3 φ(1) + φ(2)` exceed `φ(1) + φ(2)`.

## References

* A. Cianchi, N. Fusco, F. Maggi, A. Pratelli, *On the isoperimetric deficit in Gauss space*,
  Amer. J. Math. (2011), Section 2.
* F. Maggi, *Sets of finite perimeter and geometric variational problems*, Cambridge University
  Press (2012), Proposition 12.15.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace TestFunction Set Filter
open scoped ENNReal Distributions Topology symmDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {Ω : Opens E}

/-- **Lower semicontinuity of the weighted variation under `L¹_loc` convergence.** For a `C¹`
weight, if `u i → u₀` in `L¹_loc(Ω)`, that is `∫_K |u i - u₀| → 0` for every compact `K ⊆ Ω`,
then `V_μ(u₀; Ω) ≤ liminf V_μ(u i; Ω)`. -/
theorem weightedVariation_le_liminf (hW : ContDiff ℝ 1 W) {ι : Type*} {l : Filter ι}
    {u : ι → E → ℝ} {u₀ : E → ℝ} (hu : ∀ᶠ i in l, LocallyIntegrableOn (u i) Ω)
    (hu₀ : LocallyIntegrableOn u₀ Ω)
    (h : ∀ K, IsCompact K → K ⊆ Ω → Tendsto (fun i => ∫⁻ x in K, ‖u i x - u₀ x‖ₑ) l (𝓝 0)) :
    weightedVariation W Ω u₀ ≤ liminf (fun i => weightedVariation W Ω (u i)) l := by
  -- Along the trivial filter the `liminf` is `⊤`.
  obtain rfl | hl := l.eq_or_neBot
  · simp
  refine weightedVariation_le_iff.2 fun X hX => ?_
  -- The weighted divergence `g` of `X` is continuous and vanishes off the compact `tsupport X`.
  set g : E → ℝ := fun x => (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x) with hgdef
  have hg : Continuous g := ((divergenceCLM X).continuous.sub
    ((hW.continuous_fderiv one_ne_zero).clm_apply X.continuous)).mul hW.continuous.neg.rexp
  have hg0 (x : E) (hx : x ∉ tsupport X) : g x = 0 := by
    simp only [hgdef]
    rw [divergenceCLM_apply, fderiv_of_notMem_tsupport ℝ hx,
      image_eq_zero_of_notMem_tsupport hx]
    simp
  have hK : IsCompact (tsupport X) := X.hasCompactSupport
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  -- The pairing with `g` converges, being bounded by `C ∫_K |u i - u₀|` for `K = tsupport X`.
  have hlim : Tendsto (fun i => ∫ x, g x * u i x) l (𝓝 (∫ x, g x * u₀ x)) := by
    rw [tendsto_iff_edist_tendsto_0]
    have hlim := ENNReal.Tendsto.const_mul (a := ‖C‖ₑ) (h _ hK X.tsupport_subset)
      (Or.inr eNorm_ne_top)
    rw [mul_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (.of_forall fun _ => zero_le) (hu.mono fun i hi => ?_)
    rw [eDist_eq_eNorm_sub, ← integral_sub (integrable_weightedDivergence_mul hW hi X)
      (integrable_weightedDivergence_mul hW hu₀ X), ← lintegral_const_mul' _ _ eNorm_ne_top,
      ← lintegral_indicator (isClosed_tsupport _).measurableSet]
    refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun x => ?_)
    by_cases hx : x ∈ tsupport X
    · rw [indicator_of_mem hx, ← mul_sub, eNorm_mul]
      gcongr
      exact eNorm_le_iff_norm_le.mpr ((hC x hx).trans (Real.le_norm_self C))
    · have hgx := hg0 x hx
      simp only [hgdef] at hgx
      rw [← mul_sub, hgx]
      simp
  rw [← ((ENNReal.continuous_ofReal.tendsto _).comp hlim).liminf_eq]
  exact liminf_le_liminf (.of_forall fun i => ofReal_integral_le_weightedVariation X hX)

/-- **Lower semicontinuity of the weighted perimeter.** For a `C¹` weight, if the sets `s i`
converge to `s₀` locally in measure in `Ω`, that is `|(s i ∆ s₀) ∩ K| → 0` for every compact
`K ⊆ Ω`, then `P_μ(s₀; Ω) ≤ liminf P_μ(s i; Ω)`. -/
theorem weightedPerimeter_le_liminf (hW : ContDiff ℝ 1 W) {ι : Type*} {l : Filter ι}
    {s : ι → Set E} {s₀ : Set E} (hs : ∀ᶠ i in l, NullMeasurableSet (s i))
    (hs₀ : NullMeasurableSet s₀)
    (h : ∀ K, IsCompact K → K ⊆ Ω → Tendsto (fun i => volume ((s i ∆ s₀) ∩ K)) l (𝓝 0)) :
    weightedPerimeter W Ω s₀ ≤ liminf (fun i => weightedPerimeter W Ω (s i)) l := by
  simp only [weightedPerimeter_def]
  -- The indicator of a null-measurable set is locally integrable.
  have hli {t : Set E} (ht : NullMeasurableSet t) :
      LocallyIntegrableOn (t.indicator (1 : E → ℝ)) Ω :=
    locallyIntegrableOn_indicator_const (ht.mono Measure.restrict_le_self) (1 : ℝ)
  refine weightedVariation_le_liminf hW (hs.mono fun i hi => hli hi) (hli hs₀)
    fun K hK hKΩ => ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h K hK hKΩ)
    (fun _ => zero_le) fun i => ?_
  have hpt : ∀ x, ‖(s i).indicator (1 : E → ℝ) x - s₀.indicator 1 x‖ₑ =
      (s i ∆ s₀).indicator 1 x := fun x => by
    by_cases h₁ : x ∈ s i <;> by_cases h₂ : x ∈ s₀ <;> simp [mem_symmDiff, h₁, h₂]
  simp_rw [hpt]
  exact (lintegral_indicator_one_le _).trans
    (Measure.restrict_apply' hK.isClosed.measurableSet).le

/-- **Lower semicontinuity of the Gaussian perimeter.** If the sets `s i` converge to `s₀` locally
in measure, that is `|(s i ∆ s₀) ∩ K| → 0` for every compact `K`, then
`P_γ(s₀) ≤ liminf P_γ(s i)`. -/
theorem gaussianPerimeter_le_liminf {ι : Type*} {l : Filter ι} {s : ι → Set E} {s₀ : Set E}
    (hs : ∀ᶠ i in l, NullMeasurableSet (s i)) (hs₀ : NullMeasurableSet s₀)
    (h : ∀ K, IsCompact K → Tendsto (fun i => volume ((s i ∆ s₀) ∩ K)) l (𝓝 0)) :
    gaussianPerimeter s₀ ≤ liminf (fun i => gaussianPerimeter (s i)) l := by
  simp only [gaussianPerimeter_def]
  exact weightedPerimeter_le_liminf contDiff_gaussianWeight hs hs₀ fun K hK _ => h K hK

end TauCeti

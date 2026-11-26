/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.Indicator

/-!
# Lower semicontinuity of the weighted variation

For a weight `W` that is `C¹` on `Ω`, the weighted variation `V_μ(u; Ω)`
(`TauCeti.weightedVariation`) is lower semicontinuous for `L¹_loc(Ω)` convergence: if `u₀` and
eventually the `u i` are locally integrable on `Ω` and `u i → u₀` in `L¹_loc(Ω)`, then
`V_μ(u₀; Ω) ≤ liminf V_μ(u i; Ω)` (`TauCeti.weightedVariation_le_liminf`). Each pairing
`u ↦ ∫ u div_μ X dμ` with an admissible test vector field `X` is continuous for this convergence:
against volume it pairs `u` with `e^{−W} div_μ X = (div X − DW X) e^{−W}`, where
`div_μ X = div X − DW X` is the weighted divergence, and this factor is continuous with compact
support in `Ω`. The weighted variation is the supremum of these pairings.

For sets that are null-measurable in `Ω`, convergence in `L¹_loc(Ω)` of the indicators is local
convergence in measure, and the weighted perimeter is lower semicontinuous for it
(`TauCeti.weightedPerimeter_le_liminf`); in particular so is the Gaussian perimeter
(`TauCeti.gaussianPerimeter_le_liminf`). The inequality can be strict: in `ℝ`, the sets
`(−1, 1) ∪ (1 + 1/k, 2)` converge to `(−1, 2)`. For `k > 1` their Gaussian perimeters are
`2 φ(1) + φ(1 + 1/k) + φ(2)`, which tend to `3 φ(1) + φ(2)`, more than `φ(1) + φ(2)`.

The proofs adapt those of the unweighted statements `TauCeti.totalVariationOn_le_liminf` and
`TauCeti.perimeter_le_liminf`.

## References

* A. Cianchi, N. Fusco, F. Maggi, A. Pratelli, *On the isoperimetric deficit in Gauss space*,
  Amer. J. Math. (2011), Section 2.
* F. Maggi, *Sets of finite perimeter and geometric variational problems*, Cambridge University
  Press (2012), Proposition 12.15.
-/

public section

noncomputable section

namespace TauCeti

open _root_.MeasureTheory TopologicalSpace TestFunction Set Filter
open scoped ENNReal Distributions Topology symmDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {Ω : Opens E}

/-- **Lower semicontinuity of the weighted variation under `L¹_loc` convergence.** For a weight
`C¹` on `Ω`, if `u₀` and eventually the `u i` are locally integrable on `Ω`, and `u i → u₀` in
`L¹_loc(Ω)`, that is `∫_K |u i - u₀| → 0` for every compact `K ⊆ Ω`, then
`V_μ(u₀; Ω) ≤ liminf V_μ(u i; Ω)`. -/
theorem weightedVariation_le_liminf (hW : ContDiffOn ℝ 1 W Ω) {ι : Type*} {l : Filter ι}
    {u : ι → E → ℝ} {u₀ : E → ℝ} (hu : ∀ᶠ i in l, LocallyIntegrableOn (u i) Ω)
    (hu₀ : LocallyIntegrableOn u₀ Ω)
    (h : ∀ K, IsCompact K → K ⊆ Ω → Tendsto (fun i => ∫⁻ x in K, ‖u i x - u₀ x‖ₑ) l (𝓝 0)) :
    weightedVariation W Ω u₀ ≤ liminf (fun i => weightedVariation W Ω (u i)) l := by
  -- Along the trivial filter the `liminf` is `⊤`.
  obtain rfl | hl := l.eq_or_neBot
  · simp
  refine weightedVariation_le_iff.2 fun X hX => ?_
  -- The factor `g = e^{−W} div_μ X` is bounded and vanishes off the compact `tsupport X`.
  set g : E → ℝ := fun x => (divergenceCLM X x - fderiv ℝ W x (X x)) * Real.exp (-W x)
  have hK : IsCompact (tsupport X) := X.hasCompactSupport
  have hg : Continuous g := continuous_weightedDivergence hW X
  have hg0 (x : E) (hx : x ∉ tsupport X) : g x = 0 :=
    weightedDivergence_eq_zero_of_notMem_tsupport X hx
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support (.intro hK hg0)
  -- The pairing with `g` converges, being bounded by `C ∫_K |u i - u₀|` for `K = tsupport X`.
  have hlim : Tendsto (fun i => ∫ x, g x * u i x) l (𝓝 (∫ x, g x * u₀ x)) :=
    MeasureTheory.tendsto_integral_smul_of_tendsto_lintegral_enorm_sub (.of_forall hC)
      (.of_forall hg0)
      (hu.mono fun _ hi => integrable_weightedDivergence_mul hW hi X)
      (integrable_weightedDivergence_mul hW hu₀ X).aestronglyMeasurable
      (h _ hK X.tsupport_subset)
  rw [← ((ENNReal.continuous_ofReal.tendsto _).comp hlim).liminf_eq]
  exact liminf_le_liminf (.of_forall fun i => ofReal_integral_le_weightedVariation X hX)

/-- **Lower semicontinuity of the weighted perimeter.** For a weight `C¹` on `Ω`, if `s₀` and
eventually the `s i` are null-measurable in `Ω`, and the sets `s i` converge to `s₀` locally in
measure in `Ω`, that is `|(s i ∆ s₀) ∩ K| → 0` for every compact `K ⊆ Ω`, then
`P_μ(s₀; Ω) ≤ liminf P_μ(s i; Ω)`. -/
theorem weightedPerimeter_le_liminf (hW : ContDiffOn ℝ 1 W Ω) {ι : Type*} {l : Filter ι}
    {s : ι → Set E} {s₀ : Set E} (hs : ∀ᶠ i in l, NullMeasurableSet (s i) (volume.restrict Ω))
    (hs₀ : NullMeasurableSet s₀ (volume.restrict Ω))
    (h : ∀ K, IsCompact K → K ⊆ Ω → Tendsto (fun i => volume ((s i ∆ s₀) ∩ K)) l (𝓝 0)) :
    weightedPerimeter W Ω s₀ ≤ liminf (fun i => weightedPerimeter W Ω (s i)) l := by
  simp only [weightedPerimeter_def]
  -- The indicator of a set null-measurable in `Ω` is locally integrable on `Ω`.
  have hli {t : Set E} (ht : NullMeasurableSet t (volume.restrict Ω)) :
      LocallyIntegrableOn (t.indicator (1 : E → ℝ)) Ω :=
    locallyIntegrableOn_indicator_const ht (1 : ℝ)
  refine weightedVariation_le_liminf hW (hs.mono fun i hi => hli hi) (hli hs₀)
    fun K hK hKΩ => ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h K hK hKΩ)
    (fun _ => zero_le) fun _ =>
      volume.setLIntegral_enorm_indicator_one_sub_le _ _ hK.isClosed.nullMeasurableSet

/-- **Lower semicontinuity of the Gaussian perimeter.** If `s₀` and eventually the `s i` are
null-measurable, and the sets `s i` converge to `s₀` locally in measure, that is
`|(s i ∆ s₀) ∩ K| → 0` for every compact `K`, then `P_γ(s₀) ≤ liminf P_γ(s i)`. -/
theorem gaussianPerimeter_le_liminf {ι : Type*} {l : Filter ι} {s : ι → Set E} {s₀ : Set E}
    (hs : ∀ᶠ i in l, NullMeasurableSet (s i)) (hs₀ : NullMeasurableSet s₀)
    (h : ∀ K, IsCompact K → Tendsto (fun i => volume ((s i ∆ s₀) ∩ K)) l (𝓝 0)) :
    gaussianPerimeter s₀ ≤ liminf (fun i => gaussianPerimeter (s i)) l := by
  simp only [gaussianPerimeter_def]
  exact weightedPerimeter_le_liminf contDiff_gaussianWeight.contDiffOn
    (hs.mono fun _ hi => hi.mono Measure.restrict_le_self) (hs₀.mono Measure.restrict_le_self)
    fun K hK _ => h K hK

end TauCeti

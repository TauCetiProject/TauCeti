/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.VariationMeasure
public import TauCeti.Analysis.BoundedVariation.FrontierCriterion
import Mathlib.MeasureTheory.Integral.Layercake
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Lebesgue.PositiveDensity
import TauCeti.MeasureTheory.Measure.Haar.Hausdorff.Frontier

/-!
# The frontier bound for the weighted perimeter, and the Gaussian perimeter of a ball

For a `C¹` weight `W` with measure `μ = e^{−W} · volume`, the codimension-one measure is
`μ^{n−1} = e^{−W} · μHE[n − 1]`. In dimension `n ≥ 2`, every set `s`, measurable or not, has
`P_μ(s; Ω) ≤ μ^{n−1}(∂s ∩ Ω)` in every open set `Ω`
(`TauCeti.weightedPerimeter_le_setLIntegral_frontier_inter`). If the right side is finite, the
frontier has locally finite `μHE[n − 1]` measure
(`TauCeti.measure_inter_ne_top_of_setLIntegral_ne_top`), so `s` agrees with its interior almost
everywhere in `Ω`
(`TauCeti.ae_eq_interior_of_forall_isCompact_hausdorffMeasure_frontier_inter_ne_top`), and the
interior has locally finite perimeter
(`TauCeti.exists_perimeter_interior_ne_top_of_euclideanHausdorffMeasure_frontier_inter_ne_top`).
Then `P_μ(s; Ω) = ∫ e^{−W} d|D1_s|` (`TauCeti.weightedVariation_eq_lintegral_variationMeasure`), and
the layer-cake formula compares both sides on the open superlevel sets of `e^{−W}`, where the
Euclidean frontier bound `TauCeti.perimeter_le_euclideanHausdorffMeasure_frontier_inter` applies.

The perimeter measure `|D1_s|` lives on the frontier of `s`
(`TauCeti.variationMeasure_indicator_compl_frontier_eq_zero`). So if `e^{−W}` takes a constant
value `a` on the frontier of a null-measurable set `s` in `Ω`, then `P_μ(s; Ω) = a P(s; Ω)`
(`TauCeti.weightedPerimeter_eq_ofReal_mul_perimeter`), and if `e^{−W} ≤ a` there, then
`P_μ(s; Ω) ≤ a P(s; Ω)` (`TauCeti.weightedPerimeter_le_ofReal_mul_perimeter`), in every
dimension; so a set of finite perimeter with bounded frontier has finite weighted perimeter. The
Gaussian density is constant on spheres about the origin, which gives the Gaussian perimeter of a
ball in every dimension `n`: `P_γ(B(0, r)) = (2π)^{−n/2} e^{−r²/2} n ω_n r^{n−1}` with `ω_n` the
volume of the unit ball (`TauCeti.gaussianPerimeter_ball`).

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022).
* A. Cianchi, N. Fusco, F. Maggi, A. Pratelli, *On the isoperimetric deficit in Gauss space*,
  Amer. J. Math. (2011).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Module Metric Filter
open scoped ENNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {Ω : Opens E} {s : Set E}

/-- **The frontier bound for the weighted perimeter.** For a `C¹` weight `W`, in dimension
`n ≥ 2`, every set `s`, measurable or not, has `P_μ(s; Ω) ≤ ∫_{∂s ∩ Ω} e^{−W} dHⁿ⁻¹` in every open
set `Ω`. -/
theorem weightedPerimeter_le_setLIntegral_frontier_inter (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (Ω : Opens E) (s : Set E) :
    weightedPerimeter W Ω s ≤
      ∫⁻ x in frontier s ∩ Ω, ENNReal.ofReal (Real.exp (-W x)) ∂μHE[finrank ℝ E - 1] := by
  by_cases hI : ∫⁻ x in frontier s ∩ Ω, ENNReal.ofReal (Real.exp (-W x))
      ∂μHE[finrank ℝ E - 1] = ∞
  · rw [hI]
    exact le_top
  have hρ : Continuous fun x : E => Real.exp (-W x) := hW.continuous.neg.rexp
  have hK (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :=
    measure_inter_ne_top_of_setLIntegral_ne_top hρ hK (fun x _ => Real.exp_pos (-W x)) hKΩ hI
  -- The frontier is Lebesgue-null in `Ω`, so `s` agrees with its interior almost everywhere there.
  have hH (K : Set E) (hK' : IsCompact K) (hKΩ : K ⊆ Ω) :
      μH[((finrank ℝ E - 1 : ℕ) : ℝ)] (frontier s ∩ K) ≠ ∞ :=
    (Measure.euclideanHausdorffMeasure_lt_top_iff.1 (lt_top_iff_ne_top.2 (hK K hK' hKΩ))).ne
  rw [weightedPerimeter_congr_ae
    (ae_eq_interior_of_forall_isCompact_hausdorffMeasure_frontier_inter_ne_top volume (by omega)
      hH)]
  set t := interior s
  have hu : LocallyIntegrableOn (t.indicator (1 : E → ℝ)) Ω :=
    ((locallyIntegrable_const 1).indicator isOpen_interior.measurableSet).locallyIntegrableOn _
  have hfin (K : Set E) (hK' : IsCompact K) (hKΩ : K ⊆ Ω) :
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (t.indicator 1) ≠ ∞ := by
    simpa only [perimeter_def] using
      exists_perimeter_interior_ne_top_of_euclideanHausdorffMeasure_frontier_inter_ne_top
        (μ := volume) hK hK' hKΩ
  rw [weightedPerimeter_def, weightedVariation_eq_lintegral_variationMeasure hW hu hfin,
    lintegral_eq_lintegral_meas_lt _ (.of_forall fun _ => (Real.exp_pos _).le)
      (hρ.comp continuous_subtypeVal).measurable.aemeasurable,
    lintegral_eq_lintegral_meas_lt _ (.of_forall fun _ => (Real.exp_pos _).le)
      hρ.measurable.aemeasurable]
  refine setLIntegral_mono' measurableSet_Ioi fun r _ => ?_
  -- Both sides are compared on the open superlevel set `U = {e^{−W} > r} ∩ Ω`.
  let U : Opens E := ⟨{y | r < Real.exp (-W y)} ∩ Ω,
    (isOpen_lt continuous_const hρ).inter Ω.isOpen⟩
  have hpre : {x : Ω | r < Real.exp (-W x)} = (↑) ⁻¹' (U : Set E) := by
    ext x
    simp [U]
  rw [hpre, variationMeasure_preimage_coe hu hfin (show U ≤ Ω from fun _ hx => hx.2),
    ← perimeter_def, Measure.restrict_apply (isOpen_lt continuous_const hρ).measurableSet]
  refine (perimeter_le_euclideanHausdorffMeasure_frontier_inter hn U t).trans
    (measure_mono fun x hx => ?_)
  exact ⟨hx.2.1, frontier_interior_subset hx.1, hx.2.2⟩

/-- **The perimeter measure lives on the frontier.** For a `C¹` weight `W` and a set `s`
null-measurable in `Ω`, either `s` has infinite perimeter in `Ω`, infinite weighted perimeter and
frontier meeting `Ω`, or `P_μ(s; Ω) = ∫ e^{−W} dν` for a measure `ν` on `Ω` of total mass
`P(s; Ω)` carried by `∂s`. -/
private theorem weightedPerimeter_eq_top_or_eq_lintegral (hW : ContDiff ℝ 1 W)
    (hs : NullMeasurableSet s (volume.restrict Ω)) :
    (perimeter volume Ω s = ∞ ∧ weightedPerimeter W Ω s = ∞ ∧ (frontier s ∩ Ω).Nonempty) ∨
      ∃ ν : Measure Ω, ν univ = perimeter volume Ω s ∧ (∀ᵐ x : Ω ∂ν, ↑x ∈ frontier s) ∧
        weightedPerimeter W Ω s = ∫⁻ x, ENNReal.ofReal (Real.exp (-W x)) ∂ν := by
  have hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω :=
    locallyIntegrableOn_indicator_const hs 1
  by_cases hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞
  · refine .inr ⟨variationMeasure volume Ω (s.indicator 1), by
      rw [variationMeasure_univ hu hfin, perimeter_def], ?_, by
      rw [weightedPerimeter_def, weightedVariation_eq_lintegral_variationMeasure hW hu hfin]⟩
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (variationMeasure_indicator_compl_frontier_eq_zero (μ := volume) (Ω := Ω) (s := s))]
      with x hx
    exact not_not.1 hx
  -- Without locally finite perimeter both perimeters are infinite.
  have hW' : weightedPerimeter W Ω s = ∞ := by
    by_contra h
    rw [weightedPerimeter_def] at h
    exact hfin (exists_totalVariationOn_ne_top_of_weightedVariation_ne_top hW hu h)
  have hP : perimeter volume Ω s = ∞ := by
    by_contra h
    rw [perimeter_def] at h
    exact hfin fun K _ hKΩ => ⟨Ω, hKΩ, h⟩
  refine .inl ⟨hP, hW', ?_⟩
  by_contra h
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h
  rw [perimeter_eq_zero_of_disjoint_frontier h] at hP
  exact ENNReal.zero_ne_top hP

/-- **A density constant on the frontier.** For a `C¹` weight `W` and a set `s` null-measurable
in `Ω`, if `e^{−W}` takes the constant value `a` on `∂s ∩ Ω`, then `P_μ(s; Ω) = a P(s; Ω)`: the
perimeter measure of `s` lives on its frontier. -/
theorem weightedPerimeter_eq_ofReal_mul_perimeter (hW : ContDiff ℝ 1 W)
    (hs : NullMeasurableSet s (volume.restrict Ω)) {a : ℝ}
    (ha : ∀ x ∈ frontier s ∩ Ω, Real.exp (-W x) = a) :
    weightedPerimeter W Ω s = ENNReal.ofReal a * perimeter volume Ω s := by
  rcases weightedPerimeter_eq_top_or_eq_lintegral hW hs with ⟨hP, hW', x, hx⟩ | ⟨ν, hν, hfr, hW'⟩
  · rw [hW', hP, ENNReal.mul_top (by simpa [← ha x hx] using Real.exp_pos (-W x))]
  rw [hW', ← hν, ← lintegral_const]
  refine lintegral_congr_ae ?_
  filter_upwards [hfr] with x hx
  rw [ha x ⟨hx, x.property⟩]

/-- **A density bounded on the frontier.** For a `C¹` weight `W` and a set `s` null-measurable in
`Ω`, if `e^{−W} ≤ a` on `∂s ∩ Ω`, then `P_μ(s; Ω) ≤ a P(s; Ω)`: the perimeter measure of `s` lives
on its frontier. In particular a set of finite perimeter with bounded frontier has finite weighted
perimeter, in every dimension. -/
theorem weightedPerimeter_le_ofReal_mul_perimeter (hW : ContDiff ℝ 1 W)
    (hs : NullMeasurableSet s (volume.restrict Ω)) {a : ℝ}
    (ha : ∀ x ∈ frontier s ∩ Ω, Real.exp (-W x) ≤ a) :
    weightedPerimeter W Ω s ≤ ENNReal.ofReal a * perimeter volume Ω s := by
  rcases weightedPerimeter_eq_top_or_eq_lintegral hW hs with ⟨hP, -, x, hx⟩ | ⟨ν, hν, hfr, hW'⟩
  · rw [hP, ENNReal.mul_top (ENNReal.ofReal_pos.2 ((Real.exp_pos _).trans_le (ha x hx))).ne']
    exact le_top
  rw [hW', ← hν, ← lintegral_const]
  refine lintegral_mono_ae ?_
  filter_upwards [hfr] with x hx
  exact ENNReal.ofReal_le_ofReal (ha x ⟨hx, x.property⟩)

/-- **The Gaussian perimeter of a ball.** For `r > 0`, the ball of radius `r` about the origin has
Gaussian perimeter `(2π)^{−n/2} e^{−r²/2} n ω_n r^{n−1}`, where `ω_n` is the volume of the unit
ball. -/
theorem gaussianPerimeter_ball {r : ℝ} (hr : 0 < r) :
    gaussianPerimeter (ball (0 : E) r) =
      ENNReal.ofReal ((2 * Real.pi) ^ (-(finrank ℝ E : ℝ) / 2) * Real.exp (-(r ^ 2 / 2))) *
        (finrank ℝ E * ENNReal.ofReal (r ^ (finrank ℝ E - 1)) * volume (ball (0 : E) 1)) := by
  rw [gaussianPerimeter_def, weightedPerimeter_eq_ofReal_mul_perimeter contDiff_gaussianWeight
    measurableSet_ball.nullMeasurableSet fun x hx => exp_neg_gaussianWeight_of_norm_eq ?_,
    perimeter_ball hr]
  simpa using frontier_ball_subset_sphere hx.1

end TauCeti

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

/-!
# The frontier bound for the weighted perimeter, and the Gaussian perimeter of a ball

For a `C¹` weight `W` with measure `μ = e^{−W} · volume`, the codimension-one measure is
`μ^{n−1} = e^{−W} · μHE[n − 1]`. In dimension `n ≥ 2`, every set `s`, measurable or not, has
`P_μ(s; Ω) ≤ μ^{n−1}(∂s ∩ Ω)` in every open set `Ω`
(`TauCeti.weightedPerimeter_le_lintegral_frontier_inter`). If the right side is finite, the
frontier has locally finite `μHE[n − 1]` measure, so it is Lebesgue-null and `s` agrees with its
interior almost everywhere in `Ω`, and `s` has locally finite perimeter
(`TauCeti.exists_perimeter_ne_top_of_euclideanHausdorffMeasure_frontier_inter_ne_top`). Then
`P_μ(s; Ω) = ∫ e^{−W} d|D1_s|` (`TauCeti.weightedVariation_eq_lintegral_variationMeasure`), and
the layer-cake formula compares both sides on the open superlevel sets of `e^{−W}`, where the
Euclidean frontier bound `TauCeti.perimeter_le_euclideanHausdorffMeasure_frontier_inter` applies.

The perimeter measure `|D1_s|` lives on the frontier of `s`
(`TauCeti.perimeter_eq_zero_of_disjoint_frontier`). So if `e^{−W}` takes a constant value `a` on
the frontier of a null-measurable set `s` in `Ω`, then `P_μ(s; Ω) = a P(s; Ω)`
(`TauCeti.weightedPerimeter_eq_ofReal_mul_perimeter`). The Gaussian density is constant on
spheres about the origin, which gives the Gaussian perimeter of a ball in every dimension `n`:
`P_γ(B(0, r)) = (2π)^{−n/2} e^{−r²/2} n ω_n r^{n−1}` with `ω_n` the volume of the unit ball
(`TauCeti.gaussianPerimeter_ball`).

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

omit [FiniteDimensional ℝ E] in
/-- If `μ^{n−1}(∂s ∩ Ω) = ∫_{∂s ∩ Ω} e^{−W} dHⁿ⁻¹` is finite, then the frontier of `s` has finite
`(n − 1)`-dimensional Hausdorff measure in every compact subset of `Ω`. -/
private theorem euclideanHausdorffMeasure_frontier_inter_ne_top (hW : ContDiff ℝ 1 W)
    (h : ∫⁻ x in frontier s ∩ Ω, ENNReal.ofReal (Real.exp (-W x))
      ∂μHE[finrank ℝ E - 1] ≠ ∞) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    μHE[finrank ℝ E - 1] (frontier s ∩ K) ≠ ∞ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  have hρ : Continuous fun x : E => Real.exp (-W x) := hW.continuous.neg.rexp
  obtain ⟨y, -, hy⟩ := hK.exists_isMinOn hne hρ.continuousOn
  have hle : ENNReal.ofReal (Real.exp (-W y)) * μHE[finrank ℝ E - 1] (frontier s ∩ K) ≤
      ∫⁻ x in frontier s ∩ Ω, ENNReal.ofReal (Real.exp (-W x)) ∂μHE[finrank ℝ E - 1] :=
    calc ENNReal.ofReal (Real.exp (-W y)) * μHE[finrank ℝ E - 1] (frontier s ∩ K)
        = ∫⁻ _ in frontier s ∩ K, ENNReal.ofReal (Real.exp (-W y)) ∂μHE[finrank ℝ E - 1] :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in frontier s ∩ K, ENNReal.ofReal (Real.exp (-W x)) ∂μHE[finrank ℝ E - 1] :=
          setLIntegral_mono hρ.measurable.ennreal_ofReal fun x hx =>
            ENNReal.ofReal_le_ofReal (hy hx.2)
      _ ≤ _ := lintegral_mono_set (inter_subset_inter_right _ hKΩ)
  intro htop
  rw [htop, ENNReal.mul_top (by simpa using Real.exp_pos (-W y))] at hle
  exact h (top_le_iff.1 hle)

/-- **The frontier bound for the weighted perimeter.** For a `C¹` weight `W`, in dimension
`n ≥ 2`, every set `s`, measurable or not, has `P_μ(s; Ω) ≤ ∫_{∂s ∩ Ω} e^{−W} dHⁿ⁻¹` in every open
set `Ω`. -/
theorem weightedPerimeter_le_lintegral_frontier_inter (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (Ω : Opens E) (s : Set E) :
    weightedPerimeter W Ω s ≤
      ∫⁻ x in frontier s ∩ Ω, ENNReal.ofReal (Real.exp (-W x)) ∂μHE[finrank ℝ E - 1] := by
  by_cases hI : ∫⁻ x in frontier s ∩ Ω, ENNReal.ofReal (Real.exp (-W x))
      ∂μHE[finrank ℝ E - 1] = ∞
  · rw [hI]
    exact le_top
  have hK (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :=
    euclideanHausdorffMeasure_frontier_inter_ne_top hW hI hK hKΩ
  -- The frontier is Lebesgue-null in `Ω`, so `s` agrees with its interior almost everywhere there.
  have hnull : volume (frontier s ∩ Ω) = 0 := by
    refine measure_null_of_locally_null _ fun x hx => ?_
    obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx.2
    refine ⟨frontier s ∩ Ω ∩ closedBall x (δ / 2),
      inter_mem_nhdsWithin _ (closedBall_mem_nhds x (by positivity)),
      measure_mono_null (show frontier s ∩ Ω ∩ closedBall x (δ / 2) ⊆
        frontier s ∩ closedBall x (δ / 2) from fun y hy => ⟨hy.1.1, hy.2⟩) ?_⟩
    refine volume_eq_zero_of_euclideanHausdorffMeasure_ne_top (by omega) (hK _
      (isCompact_closedBall x _) ((closedBall_subset_ball (by linarith)).trans hδΩ))
  have hae : s =ᵐ[volume.restrict Ω] interior s := by
    refine (interior_ae_eq_of_null_frontier ?_).symm
    rwa [Measure.restrict_apply' Ω.isOpen.measurableSet]
  rw [weightedPerimeter_congr_ae hae]
  set t := interior s
  have hft : frontier t ⊆ frontier s := frontier_interior_subset
  have hu : LocallyIntegrableOn (t.indicator (1 : E → ℝ)) Ω :=
    ((locallyIntegrable_const 1).indicator isOpen_interior.measurableSet).locallyIntegrableOn _
  have hfin (K : Set E) (hK' : IsCompact K) (hKΩ : K ⊆ Ω) :
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (t.indicator 1) ≠ ∞ := by
    simpa only [perimeter_def] using
      exists_perimeter_ne_top_of_euclideanHausdorffMeasure_frontier_inter_ne_top (μ := volume)
        (fun L hL hLΩ => ne_top_of_le_ne_top (hK L hL hLΩ)
          (measure_mono (inter_subset_inter_left _ hft))) hK' hKΩ
  have hρ : Continuous fun x : E => Real.exp (-W x) := hW.continuous.neg.rexp
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
  exact ⟨hx.2.1, hft hx.1, hx.2.2⟩

/-- **A density constant on the frontier.** For a `C¹` weight `W` and a set `s` null-measurable
in `Ω`, if `e^{−W}` takes the constant value `a` on `∂s ∩ Ω`, then `P_μ(s; Ω) = a P(s; Ω)`: the
perimeter measure of `s` lives on its frontier. -/
theorem weightedPerimeter_eq_ofReal_mul_perimeter (hW : ContDiff ℝ 1 W)
    (hs : NullMeasurableSet s (volume.restrict Ω)) {a : ℝ}
    (ha : ∀ x ∈ frontier s ∩ Ω, Real.exp (-W x) = a) :
    weightedPerimeter W Ω s = ENNReal.ofReal a * perimeter volume Ω s := by
  have hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω :=
    locallyIntegrableOn_indicator_const hs 1
  by_cases hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞
  swap
  · -- Without locally finite perimeter both sides are infinite.
    have hW' : weightedPerimeter W Ω s = ∞ := by
      by_contra h
      rw [weightedPerimeter_def] at h
      exact hfin (exists_totalVariationOn_ne_top_of_weightedVariation_ne_top hW hu h)
    have hP : perimeter volume Ω s = ∞ := by
      by_contra h
      rw [perimeter_def] at h
      exact hfin fun K _ hKΩ => ⟨Ω, hKΩ, h⟩
    obtain ⟨x, hx⟩ : (frontier s ∩ Ω).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at h
      rw [perimeter_eq_zero_of_disjoint_frontier h] at hP
      exact ENNReal.zero_ne_top hP
    rw [hW', hP, ENNReal.mul_top (by simpa [← ha x hx] using Real.exp_pos (-W x))]
  rw [weightedPerimeter_def, weightedVariation_eq_lintegral_variationMeasure hW hu hfin]
  -- The variation measure gives no mass to the open set `Ω ∖ ∂s`.
  let V : Opens E := ⟨(frontier s)ᶜ ∩ Ω, isClosed_frontier.isOpen_compl.inter Ω.isOpen⟩
  have hV : variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' (V : Set E)) = 0 := by
    rw [variationMeasure_preimage_coe hu hfin (show V ≤ Ω from fun _ hx => hx.2),
      ← perimeter_def]
    exact perimeter_eq_zero_of_disjoint_frontier (disjoint_left.2 fun _ hx hxV => hxV.1 hx)
  have hae : ∀ᵐ x : Ω ∂variationMeasure volume Ω (s.indicator 1),
      ENNReal.ofReal (Real.exp (-W x)) = ENNReal.ofReal a := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hV] with x hx
    have hxf : (x : E) ∈ frontier s := by
      by_contra h
      exact hx ⟨h, x.property⟩
    rw [ha x ⟨hxf, x.property⟩]
  rw [lintegral_congr_ae hae, lintegral_const, variationMeasure_univ hu hfin, perimeter_def]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Gaussian density on the sphere of radius `r` about the origin is
`(2π)^{−n/2} e^{−r²/2}`. -/
theorem exp_neg_gaussianWeight_of_norm_eq {r : ℝ} {x : E} (hx : ‖x‖ = r) :
    Real.exp (-gaussianWeight E x) =
      (2 * Real.pi) ^ (-(finrank ℝ E : ℝ) / 2) * Real.exp (-(r ^ 2 / 2)) := by
  rw [gaussianWeight_def, hx, Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
  congr 1
  ring

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
